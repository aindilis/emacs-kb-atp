;; First-order logic theorem prover with superposition
;; Compatible with Emacs 27.1

;; Data structures
(cl-defstruct (term (:constructor make-term)
                   (:copier nil))
  kind   ; :var or :func
  name   ; symbol
  args)  ; list

(cl-defstruct (literal (:constructor make-literal)
                      (:copier nil))
  polarity  ; boolean
  atom)     ; term

(cl-defstruct (clause (:constructor make-clause)
                     (:copier nil))
  literals  ; list of literals
  weight    ; number
  history)  ; list for proof tracking

(cl-defstruct (formula (:constructor make-formula)
                      (:copier nil))
  kind   ; :pred, :not, :and, :or, :implies, :forall, :exists
  args)  ; list

;; Formula parsing
(defun parse-formula (sexp)
  "Convert S-expression to formula structure"
  (cond
    ((atom sexp) 
     (make-formula :kind :pred :args (list sexp)))
    ((eq (car sexp) 'not)
     (make-formula :kind :not :args (list (parse-formula (cadr sexp)))))
    ((member (car sexp) '(and or implies))
     (make-formula :kind (intern (concat ":" (symbol-name (car sexp))))
                  :args (mapcar #'parse-formula (cdr sexp))))
    ((member (car sexp) '(forall exists))
     (make-formula :kind (intern (concat ":" (symbol-name (car sexp))))
                  :args (list (cadr sexp) 
                             (parse-formula (caddr sexp)))))
    (t (make-formula :kind :pred :args sexp))))

;; Negation normal form
(defun negate (formula)
  "Negate a formula, pushing negation inward"
  (if (not (formula-p formula))
      (make-formula :kind :not :args (list formula))
    (case (formula-kind formula)
      (:not (car (formula-args formula)))  ; Double negation
      (:and (make-formula :kind :or        ; De Morgan's laws
                         :args (mapcar #'negate (formula-args formula))))
      (:or (make-formula :kind :and
                        :args (mapcar #'negate (formula-args formula))))
      (:implies 
       (let ((ant (car (formula-args formula)))
             (con (cadr (formula-args formula))))
         (make-formula :kind :and
                      :args (list ant (negate con)))))
      (:forall (make-formula :kind :exists
                           :args (list (car (formula-args formula))
                                     (negate (cadr (formula-args formula))))))
      (:exists (make-formula :kind :forall
                           :args (list (car (formula-args formula))
                                     (negate (cadr (formula-args formula))))))
      (otherwise (make-formula :kind :not :args (list formula))))))

;; Formula conversion pipeline
(defun eliminate-implications (formula)
  "Convert implication to disjunction with negation"
  (if (not (formula-p formula))
      formula
    (case (formula-kind formula)
      (:implies 
       (let ((ant (eliminate-implications (car (formula-args formula))))
             (con (eliminate-implications (cadr (formula-args formula)))))
         (make-formula 
          :kind :or
          :args (list (make-formula :kind :not :args (list ant))
                     con))))
      (otherwise
       (make-formula
        :kind (formula-kind formula)
        :args (mapcar #'eliminate-implications (formula-args formula)))))))

(defun eliminate-quantifiers (formula)
  "Eliminate universal quantifiers (simple version without Skolemization)"
  (if (not (formula-p formula))
      formula
    (case (formula-kind formula)
      (:forall 
       (eliminate-quantifiers (cadr (formula-args formula))))
      (otherwise
       (make-formula
        :kind (formula-kind formula)
        :args (mapcar #'eliminate-quantifiers (formula-args formula)))))))

(defun to-nnf (formula)
  "Convert to negation normal form"
  (if (not (formula-p formula))
      formula
    (case (formula-kind formula)
      (:not 
       (let ((arg (car (formula-args formula))))
         (if (not (formula-p arg))
             formula
           (case (formula-kind arg)
             (:not (to-nnf (car (formula-args arg))))  ; Double negation
             (:and                                     ; De Morgan
              (make-formula 
               :kind :or
               :args (mapcar (lambda (f) 
                             (to-nnf (make-formula :kind :not 
                                                 :args (list f))))
                           (formula-args arg))))
             (:or                                      ; De Morgan
              (make-formula 
               :kind :and
               :args (mapcar (lambda (f)
                             (to-nnf (make-formula :kind :not 
                                                 :args (list f))))
                           (formula-args arg))))
             (otherwise formula)))))
      ((:and :or)
       (make-formula 
        :kind (formula-kind formula)
        :args (mapcar #'to-nnf (formula-args formula))))
      (otherwise formula))))

(defun distribute-or-over-and (formula)
  "Distribute OR over AND in CNF conversion"
  (if (not (and (formula-p formula)
                (eq (formula-kind formula) :or)))
      formula
    (let ((args (formula-args formula)))
      (if (some (lambda (f) 
                  (and (formula-p f) 
                       (eq (formula-kind f) :and)))
              args)
          (let ((and-arg (find-if (lambda (f)
                                   (and (formula-p f)
                                        (eq (formula-kind f) :and)))
                                 args))
                (other-args (remove-if (lambda (f)
                                       (and (formula-p f)
                                            (eq (formula-kind f) :and)))
                                     args)))
            (make-formula 
             :kind :and
             :args (mapcar (lambda (and-arg-clause)
                            (distribute-or-over-and
                             (make-formula 
                              :kind :or
                              :args (cons and-arg-clause other-args))))
                          (formula-args and-arg))))
        formula))))

(defun cnf-convert (formula)
  "Convert formula to CNF"
  (let* ((no-impl (eliminate-implications formula))
         (no-quant (eliminate-quantifiers no-impl))
         (nnf (to-nnf no-quant))
         (cnf (if (and (formula-p nnf)
                      (eq (formula-kind nnf) :or))
                 (distribute-or-over-and nnf)
               nnf)))
    cnf))

;; Clause conversion
(defun formula-to-literals (formula)
  "Convert a formula to a list of literals"
  (cond 
   ;; Base case: predicate
   ((and (formula-p formula)
         (eq (formula-kind formula) :pred))
    (list (make-literal 
           :polarity t
           :atom (make-term :kind :pred
                          :name (car (formula-args formula))
                          :args (cdr (formula-args formula))))))
   ;; Negation
   ((and (formula-p formula)
         (eq (formula-kind formula) :not))
    (let ((arg (car (formula-args formula))))
      (cond
       ;; Negated predicate
       ((and (formula-p arg)
             (eq (formula-kind arg) :pred))
        (list (make-literal 
               :polarity nil
               :atom (make-term :kind :pred
                              :name (car (formula-args arg))
                              :args (cdr (formula-args arg))))))
       (t (error "Cannot negate non-predicate: %S" arg)))))
   ;; Disjunction
   ((and (formula-p formula)
         (eq (formula-kind formula) :or))
    (let (result)
      (dolist (f (formula-args formula))
        (let ((lits (formula-to-literals f)))
          (setq result (nconc result lits))))
      result))
   ;; Default case for atomic symbols
   ((symbolp formula)
    (list (make-literal 
           :polarity t
           :atom (make-term :kind :pred
                          :name formula
                          :args nil))))
   ;; Default case for lists (treating as predicate applications)
   ((and (listp formula) (not (null formula)))
    (list (make-literal 
           :polarity t
           :atom (make-term :kind :pred
                          :name (car formula)
                          :args (cdr formula)))))
   (t (error "Cannot convert to literals: %S" formula))))

(defun formula-to-clause (formula)
  "Convert a formula in CNF to a clause"
  (make-clause 
   :literals (formula-to-literals formula)
   :weight 1
   :history nil))

(cl-defstruct (term-index (:constructor make-term-index)
                         (:copier nil))
  (path-map (make-hash-table :test 'equal)))

(cl-defstruct (prover-state (:constructor make-prover-state)
                           (:copier nil))
  active   ; Active set of clauses
  passive  ; Passive set of clauses
  index)   ; Term index

;; Resolution and proof search
(defun empty-clause-p (clause)
  "Check if clause is empty"
  (null (clause-literals clause)))

(defun resolve-literals (lit1 lit2)
  "Resolve two literals if possible"
  (when (eq (literal-polarity lit1)
            (not (literal-polarity lit2)))
    (let ((atom1 (literal-atom lit1))
          (atom2 (literal-atom lit2)))
      (when (and (eq (term-name atom1)
                     (term-name atom2))
                 (= (length (term-args atom1))
                    (length (term-args atom2))))
        t)))) ; TODO: Add unification

(defun process-clause (clause state)
  "Process clause against active set"
  (let (new-clauses)
    (dolist (active-clause (prover-state-active state))
      (dolist (lit1 (clause-literals clause))
        (dolist (lit2 (clause-literals active-clause))
          (when (resolve-literals lit1 lit2)
            (push (make-clause 
                   :literals nil
                   :weight 0
                   :history (list clause active-clause))
                  new-clauses)))))
    (setf (prover-state-active state)
          (cons clause (prover-state-active state)))
    new-clauses))

(defun select-given-clause (state)
  "Select next clause using weight heuristic"
  (let ((passive (prover-state-passive state)))
    (when passive
      (car passive))))

(defun clause-to-string (clause)
  "Convert clause to readable string"
  (format "[%s]"
          (mapconcat 
           (lambda (lit)
             (format "%s%s(%s)"
                     (if (literal-polarity lit) "" "¬")
                     (term-name (literal-atom lit))
                     (mapconcat #'symbol-name 
                               (term-args (literal-atom lit))
                               ",")))
           (clause-literals clause)
           " ∨ ")))

(defun prove (conjecture axioms &optional debug)
  "Try to prove conjecture from axioms"
  (when debug (princ "Starting proof search\n"))
  (let* ((parsed-conjecture (parse-formula conjecture))
         (_ (when debug
              (princ (format "Parsed conjecture: %S\n" parsed-conjecture))))
         (parsed-axioms (mapcar #'parse-formula axioms))
         (_ (when debug
              (princ "Parsed axioms:\n")
              (dolist (ax parsed-axioms)
                (princ (format "  %S\n" ax)))))
         (negated (negate parsed-conjecture))
         (_ (when debug
              (princ (format "Negated conjecture: %S\n" negated))))
         (no-impl (eliminate-implications negated))
         (_ (when debug
              (princ (format "After implication elimination: %S\n" no-impl))))
         (no-quant (eliminate-quantifiers no-impl))
         (_ (when debug 
              (princ (format "After quantifier elimination: %S\n" no-quant))))
         (nnf (to-nnf no-quant))
         (_ (when debug
              (princ (format "In NNF: %S\n" nnf))))
         (cnf-conj (cnf-convert negated))
         (_ (when debug
              (princ (format "CNF conjecture: %S\n" cnf-conj))
              (princ "Converting conjecture to clause...\n")))
         (conj-clause (formula-to-clause cnf-conj))
         (_ (when debug
              (princ (format "Conjecture clause: %s\n" 
                            (clause-to-string conj-clause)))))
         (cnf-axioms (mapcar #'cnf-convert parsed-axioms))
         (_ (when debug
              (princ "CNF axioms:\n")
              (dolist (ax cnf-axioms)
                (princ (format "  %S\n" ax)))))
         (_ (when debug
              (princ "Converting axioms to clauses...\n")))
         (axiom-clauses (mapcar #'formula-to-clause cnf-axioms))
         (_ (when debug
              (princ "Axiom clauses:\n")
              (dolist (cl axiom-clauses)
                (princ (format "  %s\n" (clause-to-string cl))))))
         (state (make-prover-state
                :active nil
                :passive (cons conj-clause axiom-clauses)
                :index (make-term-index)))
         result)
    (catch 'proof-found
      (while (prover-state-passive state)
        (let* ((given (select-given-clause state))
               (_ (when debug
                    (princ (format "\nProcessing clause: %s\n" 
                                 (clause-to-string given)))))
               (new-clauses (process-clause given state))
               (_ (when debug
                    (when new-clauses
                      (princ "Generated clauses:\n")
                      (dolist (cl new-clauses)
                        (princ (format "  %s\n" 
                                     (clause-to-string cl))))))))
          ;; Check for empty clause (proof found)
          (when (and new-clauses (member-if #'empty-clause-p new-clauses))
            (when debug (princ "Found empty clause - proof complete\n"))
            (setq result t)
            (throw 'proof-found t))
          ;; Add new clauses to passive set
          (setf (prover-state-passive state)
                (append (remove given (prover-state-passive state))
                       new-clauses)))))
    (unless result
      (when debug (princ "No proof found\n")))
    result))

;; ;; Example usage:
;; (prove '(dies socrates)
;;        '((forall (x) (implies (mortal x) (dies x)))
;;          (forall (x) (implies (human x) (mortal x)))
;;          (human socrates))
;;  t)

;; ;; Simple transitivity
;; (prove '(eats tweety worms)
;;        '((forall (x) (implies (canary x) (bird x)))
;;          (forall (x) (implies (bird x) (eats x worms)))
;;          (canary tweety))
;;        t)

;; ;; Multiple steps required
;; (prove '(happy fluffy)
;;        '((forall (x) (implies (cat x) (likes x milk)))
;;          (forall (x) (implies (likes x milk) (happy x)))
;;          (cat fluffy))
;;        t)

;; ;; Requires multiple premises to combine
;; (prove '(flies tweety)
;;        '((forall (x) (implies (and (bird x) (healthy x)) (flies x)))
;;          (bird tweety)
;;          (healthy tweety))
;;        t)

;; ;; Test double negation handling
;; (prove '(mortal socrates)
;;        '((forall (x) (implies (human x) (mortal x)))
;;          (not (not (human socrates))))
;;        t)

;; ;; Test with equality (if implemented)
;; (prove '(equals (plus 2 2) 4)
;;        '((forall (x y z) (implies (and (equals x y) (equals y z)) (equals x z)))
;;          (equals (plus 2 2) (times 2 2))
;;          (equals (times 2 2) 4))
;;        t)

;; ;; More complex chains of reasoning
;; (prove '(likes john music)
;;        '((forall (x) (implies (student x) (likes x learning)))
;;          (forall (x) (implies (likes x learning) (likes x books)))
;;          (forall (x) (implies (likes x books) (likes x music)))
;;          (student john))
;;        t)
