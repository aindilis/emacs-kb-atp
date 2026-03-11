;;; emacs-atp.el --- First-Order Logic Automated Theorem Prover -*- lexical-binding: t; -*-

;; Copyright (C) 2024 Andrew Dougherty
;; License: GPL-3.0-or-later

;;; Commentary:
;;
;; A resolution-based automated theorem prover for first-order logic
;; implemented in Emacs Lisp.
;;
;; Variable convention: In user-facing formulas, variables are the symbols
;; bound by quantifiers (forall/exists). During CNF conversion, all
;; quantified variables are renamed to internal form (_V1, _V2, ...)
;; so they are distinguishable from constants after quantifier dropping.
;; Internally, a symbol is a variable iff its name starts with underscore _
;; and does NOT start with _sk (Skolem symbols).
;;
;; Formula syntax:
;;   Predicates:   (predicate arg1 arg2 ...)
;;   Negation:     (not formula)
;;   Implication:  (implies antecedent consequent)
;;   Universal:    (forall (var) formula)
;;   Existential:  (exists (var) formula)
;;   Conjunction:  (and formula1 formula2 ...)
;;   Disjunction:  (or formula1 formula2 ...)

;;; Code:

(require 'cl-lib)

;; ============================================================
;; Counters and fresh symbol generation
;; ============================================================

(defvar atp--var-counter 0
  "Counter for generating fresh variable names.")

(defvar atp--skolem-counter 0
  "Counter for generating fresh Skolem function/constant names.")

(defun atp--reset-counters ()
  "Reset all internal counters."
  (setq atp--var-counter 0)
  (setq atp--skolem-counter 0))

(defun atp--fresh-var ()
  "Generate a fresh internal variable symbol (_V1, _V2, ...)."
  (setq atp--var-counter (1+ atp--var-counter))
  (intern (format "_V%d" atp--var-counter)))

(defun atp--fresh-skolem ()
  "Generate a fresh Skolem symbol (_sk1, _sk2, ...)."
  (setq atp--skolem-counter (1+ atp--skolem-counter))
  (intern (format "_sk%d" atp--skolem-counter)))

;; ============================================================
;; Type predicates
;; ============================================================

(defun atp--variable-p (x)
  "Return non-nil if X is an internal variable (starts with _ but not _sk)."
  (and (symbolp x)
       (let ((name (symbol-name x)))
         (and (> (length name) 1)
              (= (aref name 0) ?_)
              (not (string-prefix-p "_sk" name))))))

;; ============================================================
;; Substitution application
;; ============================================================

(defun atp--apply-subst (subst term)
  "Apply substitution SUBST (alist) to TERM, following variable chains.
Detects self-referential bindings to prevent infinite loops."
  (cond
   ((atp--variable-p term)
    (let ((binding (assq term subst)))
      (if binding
          (let ((val (cdr binding)))
            ;; Guard against self-referential binding (x -> x)
            (if (eq val term)
                term
              (atp--apply-subst subst val)))
        term)))
   ((consp term)
    (cons (atp--apply-subst subst (car term))
          (atp--apply-subst subst (cdr term))))
   (t term)))

;; ============================================================
;; Unification (Robinson's algorithm with occur check)
;; ============================================================

(defun atp--occurs-in-p (var term)
  "Return non-nil if VAR occurs anywhere in TERM."
  (cond
   ((eq var term) t)
   ((consp term)
    (or (atp--occurs-in-p var (car term))
        (atp--occurs-in-p var (cdr term))))
   (t nil)))

(defconst atp--empty-subst '((atp--marker . t))
  "Marker substitution representing success with no bindings.
In Emacs Lisp, nil means both empty-list and false.  We need to
distinguish \\='success with no bindings\\=' from \\='failure\\=', so we
seed every substitution with this harmless dummy binding.
The symbol atp--marker starts with \\='a\\=', not \\='_\\=', so it is
never treated as a variable and never interferes with unification.")

(defun atp--unify (t1 t2 &optional subst)
  "Unify T1 and T2 under SUBST. Returns MGU or nil on failure.
Uses Robinson's algorithm with occur check.
On success, always returns a non-nil alist (seeded with a marker)."
  (unless subst (setq subst atp--empty-subst))
  (let ((s1 (atp--apply-subst subst t1))
        (s2 (atp--apply-subst subst t2)))
    (cond
     ;; Identical terms (handles atoms, equal compound terms, nil=nil)
     ((equal s1 s2) subst)
     ;; Variable cases
     ((atp--variable-p s1)
      (if (atp--occurs-in-p s1 s2) nil
        (cons (cons s1 s2) subst)))
     ((atp--variable-p s2)
      (if (atp--occurs-in-p s2 s1) nil
        (cons (cons s2 s1) subst)))
     ;; Both are consp: unify car, then cdr
     ((and (consp s1) (consp s2))
      (let ((head-subst (atp--unify (car s1) (car s2) subst)))
        (when head-subst
          (atp--unify (cdr s1) (cdr s2) head-subst))))
     ;; Everything else fails
     (t nil))))

;; ============================================================
;; CNF Conversion Pipeline
;; ============================================================

;; --- Step 1: Rename quantified variables to _Vn form ---

(defun atp--rename-quantified-vars (formula)
  "Rename all quantified variables in FORMULA to internal _Vn form."
  (atp--rqv formula '()))

(defun atp--rqv (formula env)
  "Recursive helper for variable renaming. ENV maps user vars to internal vars."
  (cond
   ((symbolp formula)
    (let ((b (assq formula env))) (if b (cdr b) formula)))
   ((not (consp formula)) formula)
   ((memq (car formula) '(forall exists))
    (let* ((var (car (nth 1 formula)))
           (new-var (atp--fresh-var))
           (new-env (cons (cons var new-var) env)))
      (list (car formula) (list new-var) (atp--rqv (nth 2 formula) new-env))))
   ((memq (car formula) '(not and or implies))
    (cons (car formula) (mapcar (lambda (f) (atp--rqv f env)) (cdr formula))))
   ;; Atomic formula: apply env to each sub-term
   (t (mapcar (lambda (f) (atp--rqv f env)) formula))))

;; --- Step 2: Eliminate implications ---

(defun atp--eliminate-implications (formula)
  "Eliminate implications: (implies A B) => (or (not A) B)."
  (cond
   ((atom formula) formula)
   ((eq (car formula) 'implies)
    (list 'or
          (list 'not (atp--eliminate-implications (nth 1 formula)))
          (atp--eliminate-implications (nth 2 formula))))
   (t (cons (car formula) (mapcar #'atp--eliminate-implications (cdr formula))))))

;; --- Step 3: Negation Normal Form ---

(defun atp--nnf (formula)
  "Push negations inward to atoms."
  (cond
   ((atom formula) formula)
   ((eq (car formula) 'not)
    (let ((inner (nth 1 formula)))
      (cond
       ((atom inner) formula)
       ((eq (car inner) 'not) (atp--nnf (nth 1 inner)))
       ((eq (car inner) 'and)
        (atp--nnf (cons 'or (mapcar (lambda (a) (list 'not a)) (cdr inner)))))
       ((eq (car inner) 'or)
        (atp--nnf (cons 'and (mapcar (lambda (a) (list 'not a)) (cdr inner)))))
       ((eq (car inner) 'forall)
        (atp--nnf (list 'exists (nth 1 inner) (list 'not (nth 2 inner)))))
       ((eq (car inner) 'exists)
        (atp--nnf (list 'forall (nth 1 inner) (list 'not (nth 2 inner)))))
       (t (list 'not (atp--nnf inner))))))
   ((memq (car formula) '(and or))
    (cons (car formula) (mapcar #'atp--nnf (cdr formula))))
   ((memq (car formula) '(forall exists))
    (list (car formula) (nth 1 formula) (atp--nnf (nth 2 formula))))
   (t formula)))

;; --- Step 4: Skolemize ---

(defun atp--skolemize (formula &optional uvars)
  "Remove existentials by Skolemization. UVARS = universal vars in scope."
  (unless uvars (setq uvars '()))
  (cond
   ((atom formula) formula)
   ((eq (car formula) 'forall)
    (let ((v (car (nth 1 formula))))
      (list 'forall (nth 1 formula)
            (atp--skolemize (nth 2 formula) (cons v uvars)))))
   ((eq (car formula) 'exists)
    (let* ((v (car (nth 1 formula)))
           (sk (atp--fresh-skolem))
           (sk-term (if uvars (cons sk (reverse uvars)) sk))
           (body (atp--sk-subst v sk-term (nth 2 formula))))
      (atp--skolemize body uvars)))
   ((memq (car formula) '(and or not))
    (cons (car formula) (mapcar (lambda (f) (atp--skolemize f uvars)) (cdr formula))))
   (t formula)))

(defun atp--sk-subst (var replacement formula)
  "Replace VAR with REPLACEMENT in FORMULA."
  (cond
   ((eq formula var) replacement)
   ((atom formula) formula)
   ((and (memq (car formula) '(forall exists)) (eq (car (nth 1 formula)) var))
    formula)
   (t (mapcar (lambda (f) (atp--sk-subst var replacement f)) formula))))

;; --- Step 5: Drop universal quantifiers ---

(defun atp--drop-universals (formula)
  "Strip all universal quantifiers (they are implicit in clausal form)."
  (cond
   ((atom formula) formula)
   ((eq (car formula) 'forall) (atp--drop-universals (nth 2 formula)))
   (t (cons (car formula) (mapcar #'atp--drop-universals (cdr formula))))))

;; --- Step 6: Distribute OR over AND ---

(defun atp--flatten (conn formula)
  "Flatten nested CONN (and/or) occurrences."
  (cond
   ((atom formula) (list formula))
   ((eq (car formula) conn)
    (apply #'append (mapcar (lambda (f) (atp--flatten conn f)) (cdr formula))))
   (t (list formula))))

(defun atp--distribute (formula)
  "Convert FORMULA to CNF by distributing OR over AND."
  (cond
   ((atom formula) formula)
   ((eq (car formula) 'not) formula)
   ((eq (car formula) 'and)
    (let* ((args (mapcar #'atp--distribute (cdr formula)))
           (flat (apply #'append (mapcar (lambda (a) (atp--flatten 'and a)) args))))
      (if (= (length flat) 1) (car flat) (cons 'and flat))))
   ((eq (car formula) 'or)
    (let ((args (mapcar #'atp--distribute (cdr formula))))
      (atp--dist-or args)))
   (t formula)))

(defun atp--dist-or (disjuncts)
  "Distribute OR over AND in DISJUNCTS list."
  (let ((and-pos nil) (idx 0))
    (dolist (d disjuncts)
      (when (and (null and-pos) (consp d) (eq (car d) 'and))
        (setq and-pos idx))
      (setq idx (1+ idx)))
    (if (null and-pos)
        ;; No AND found: flatten ORs and done
        (let ((flat (apply #'append (mapcar (lambda (d) (atp--flatten 'or d)) disjuncts))))
          (if (= (length flat) 1) (car flat) (cons 'or flat)))
      ;; Found AND: distribute
      ;; (or X1 ... (and A B) ... Xn) => (and (or X1 ... A ... Xn) (or X1 ... B ... Xn))
      (let* ((and-f (nth and-pos disjuncts))
             (and-args (cdr and-f))
             (others (append (cl-subseq disjuncts 0 and-pos)
                             (cl-subseq disjuncts (1+ and-pos)))))
        (let ((conjuncts (mapcar (lambda (ai) (atp--dist-or (append others (list ai))))
                                 and-args)))
          (if (= (length conjuncts) 1) (car conjuncts) (cons 'and conjuncts)))))))

;; --- Full pipeline ---

(defun atp--formula-to-cnf (formula)
  "Full CNF conversion pipeline."
  (atp--distribute
   (atp--drop-universals
    (atp--skolemize
     (atp--nnf
      (atp--eliminate-implications
       (atp--rename-quantified-vars formula)))))))

;; ============================================================
;; Clause extraction from CNF
;; ============================================================

(defun atp--literal-p (formula)
  "Non-nil if FORMULA is a literal (atom or negated atom)."
  (cond
   ((atom formula) t)
   ((and (eq (car formula) 'not)
         (let ((inner (nth 1 formula)))
           (or (atom inner)
               (not (memq (car inner) '(and or not implies forall exists))))))
    t)
   ((not (memq (car formula) '(and or not implies forall exists))) t)
   (t nil)))

(defun atp--cnf-to-clauses (cnf)
  "Convert CNF formula to list of clauses."
  (cond
   ((atp--literal-p cnf) (list (list cnf)))
   ((eq (car cnf) 'and)
    (apply #'append (mapcar #'atp--cnf-to-clauses (cdr cnf))))
   ((eq (car cnf) 'or)
    (list (apply #'append
                 (mapcar (lambda (f)
                           (if (atp--literal-p f) (list f)
                             (if (and (consp f) (eq (car f) 'or)) (cdr f) (list f))))
                         (cdr cnf)))))
   (t (list (list cnf)))))

(defun atp--formula-to-clauses (formula)
  "Convert FORMULA to list of clauses."
  (atp--cnf-to-clauses (atp--formula-to-cnf formula)))

;; ============================================================
;; Variable standardization apart (for resolution)
;; ============================================================

(defun atp--collect-vars (term)
  "Collect all variables in TERM."
  (cond
   ((atp--variable-p term) (list term))
   ((atom term) nil)
   (t (cl-remove-duplicates
       (apply #'append (mapcar #'atp--collect-vars term))))))

(defun atp--standardize-clause (clause)
  "Rename all variables in CLAUSE to fresh ones.
Ensures no identity bindings (which would cause infinite loops in apply-subst)."
  (let* ((vars (atp--collect-vars clause))
         (ren (let (result)
                (dolist (v vars (nreverse result))
                  (let ((new-v (atp--fresh-var)))
                    ;; Only add non-identity bindings
                    (unless (eq v new-v)
                      (push (cons v new-v) result)))))))
    (if ren
        (atp--apply-subst ren clause)
      clause)))

;; ============================================================
;; Literal operations
;; ============================================================

(defun atp--negate-literal (lit)
  "Negate LIT."
  (if (and (consp lit) (eq (car lit) 'not)) (nth 1 lit) (list 'not lit)))

(defun atp--positive-p (lit)
  "Non-nil if LIT is positive."
  (not (and (consp lit) (eq (car lit) 'not))))

(defun atp--atom-of (lit)
  "Predicate application of LIT (strip negation)."
  (if (and (consp lit) (eq (car lit) 'not)) (nth 1 lit) lit))

;; ============================================================
;; Resolution
;; ============================================================

(defun atp--resolve (c1 c2)
  "Resolve clauses C1 and C2. Returns list of resolvents."
  (let* ((sc1 (atp--standardize-clause c1))
         (sc2 (atp--standardize-clause c2))
         (results nil))
    (dotimes (i (length sc1))
      (dotimes (j (length sc2))
        (let ((l1 (nth i sc1)) (l2 (nth j sc2)))
          (when (not (eq (atp--positive-p l1) (atp--positive-p l2)))
            (let ((mgu (atp--unify (atp--atom-of l1) (atp--atom-of l2))))
              (when mgu
                (let* ((r1 (append (cl-subseq sc1 0 i) (cl-subseq sc1 (1+ i))))
                       (r2 (append (cl-subseq sc2 0 j) (cl-subseq sc2 (1+ j))))
                       (res (cl-remove-duplicates
                             (mapcar (lambda (l) (atp--apply-subst mgu l))
                                     (append r1 r2))
                             :test #'equal)))
                  (push res results))))))))
    results))

(defun atp--tautology-p (clause)
  "Non-nil if CLAUSE contains complementary literals."
  (cl-some (lambda (l) (member (atp--negate-literal l) clause)) clause))

(defun atp--clause-equal-p (c1 c2)
  "Non-nil if C1 and C2 are equal as sets of literals."
  (and (= (length c1) (length c2))
       (cl-every (lambda (l) (member l c2)) c1)))

;; ============================================================
;; Given-clause algorithm with set-of-support
;; ============================================================

(defun atp--pick-lightest (sos)
  "Remove and return the shortest clause from SOS. Returns (clause . rest)."
  (when sos
    (let ((best (car sos)) (bw (length (car sos))))
      (dolist (c (cdr sos))
        (when (< (length c) bw) (setq best c) (setq bw (length c))))
      (cons best (cl-remove best sos :test #'equal :count 1)))))

(defun prove (goal axioms &optional debug max-iterations)
  "Prove GOAL from AXIOMS by resolution refutation.
Returns non-nil on success. DEBUG enables tracing.
MAX-ITERATIONS limits search (default 1000)."
  (atp--reset-counters)
  (unless max-iterations (setq max-iterations 1000))
  (let* ((ax-clauses (apply #'append (mapcar #'atp--formula-to-clauses axioms)))
         (neg-goal-clauses (atp--formula-to-clauses (list 'not goal)))
         (usable ax-clauses)
         (sos neg-goal-clauses)
         (seen (append (copy-sequence usable) (copy-sequence sos)))
         (iter 0) (proved nil))
    (when debug
      (message "=== ATP ===")
      (message "Axioms: %S" usable)
      (message "Neg goal: %S" sos))
    ;; Check for empty clause already present
    (when (cl-some #'null sos) (setq proved t))
    (while (and sos (not proved) (< iter max-iterations))
      (setq iter (1+ iter))
      (let* ((sel (atp--pick-lightest sos))
             (given (car sel)))
        (setq sos (cdr sel))
        (when debug
          (message "%d: given=%S |sos|=%d |usable|=%d" iter given (length sos) (length usable)))
        (if (null given)
            (progn (setq proved t)
                   (when debug (message "PROVED (empty clause selected)")))
          (push given usable)
          (dolist (other usable)
            (unless proved
              (dolist (r (atp--resolve given other))
                (unless proved
                  (cond
                   ((null r)
                    (setq proved t)
                    (when debug (message "PROVED via %S x %S" given other)))
                   ((atp--tautology-p r) nil)
                   ((cl-some (lambda (c) (atp--clause-equal-p c r)) seen) nil)
                   (t (push r sos) (push r seen)
                      (when debug (message "  +%S" r)))))))))))
    (when debug
      (message (if proved "Proof found (%d iters)" "No proof (%d iters)") iter))
    proved))

;; ============================================================
;; KB interface
;; ============================================================

(defvar atp--kb nil "Current knowledge base.")
(defun atp-clear-kb () "Clear KB." (setq atp--kb nil))
(defun atp-assert (formula) "Assert FORMULA." (push formula atp--kb))
(defun atp-prove (goal &optional debug) "Prove GOAL from KB." (prove goal atp--kb debug))

(provide 'emacs-atp)
;;; emacs-atp.el ends here
