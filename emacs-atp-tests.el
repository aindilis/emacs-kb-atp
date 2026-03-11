;;; emacs-atp-tests.el --- Tests for emacs-atp -*- lexical-binding: t; -*-

;;; Code:

(require 'ert)

;; Load emacs-atp.el from the same directory
(load-file (expand-file-name "emacs-atp.el"
                              (or (and load-file-name (file-name-directory load-file-name))
                                  default-directory)))

;; ============================================================
;; UNIFICATION TESTS
;; ============================================================

(ert-deftest test-unify-identical ()
  (should (atp--unify 'a 'a))  ; non-nil = success
  ;; No real variable bindings, only the marker
  (should-not (assq '_x (atp--unify 'a 'a))))

(ert-deftest test-unify-diff-constants ()
  (should-not (atp--unify 'A 'B)))

(ert-deftest test-unify-var-const ()
  (let ((r (atp--unify '_x 'A)))
    (should r)
    (should (equal (atp--apply-subst r '_x) 'A))))

(ert-deftest test-unify-two-vars ()
  (let ((r (atp--unify '_x '_y)))
    (should r)
    (should (equal (atp--apply-subst r '_x)
                   (atp--apply-subst r '_y)))))

(ert-deftest test-unify-compound ()
  (let ((r (atp--unify '(f _x A) '(f B _y))))
    (should r)
    (should (equal (atp--apply-subst r '_x) 'B))
    (should (equal (atp--apply-subst r '_y) 'A))))

(ert-deftest test-unify-nested ()
  (let ((r (atp--unify '(f (g _x) A) '(f (g B) _y))))
    (should r)
    (should (equal (atp--apply-subst r '_x) 'B))
    (should (equal (atp--apply-subst r '_y) 'A))))

(ert-deftest test-unify-occur-check ()
  "x = f(x) should fail."
  (should-not (atp--unify '_x '(f _x))))

(ert-deftest test-unify-occur-nested ()
  "x = g(h(x)) should fail."
  (should-not (atp--unify '_x '(g (h _x)))))

(ert-deftest test-unify-diff-arity ()
  (should-not (atp--unify '(f A) '(f A B))))

(ert-deftest test-unify-diff-functor ()
  (should-not (atp--unify '(f _x) '(g _x))))

(ert-deftest test-unify-chain ()
  "f(x,y) ~ f(y,A) => x=A, y=A."
  (let ((r (atp--unify '(f _x _y) '(f _y A))))
    (should r)
    (should (equal (atp--apply-subst r '_x) 'A))
    (should (equal (atp--apply-subst r '_y) 'A))))

;; ============================================================
;; CNF PIPELINE TESTS
;; ============================================================

(ert-deftest test-cnf-implication ()
  (should (equal (atp--eliminate-implications '(implies A B))
                 '(or (not A) B))))

(ert-deftest test-nnf-double-neg ()
  (should (equal (atp--nnf '(not (not A))) 'A)))

(ert-deftest test-nnf-demorgan-and ()
  (should (equal (atp--nnf '(not (and A B)))
                 '(or (not A) (not B)))))

(ert-deftest test-nnf-demorgan-or ()
  (should (equal (atp--nnf '(not (or A B)))
                 '(and (not A) (not B)))))

(ert-deftest test-cnf-distribution ()
  "Distribution of OR over AND produces two clauses (order may vary)."
  (let ((result (atp--distribute '(or A (and B C)))))
    ;; Should be (and (or ...) (or ...)) where each disjunction has A and one of B,C
    (should (eq (car result) 'and))
    (should (= (length (cdr result)) 2))
    ;; Each sub-clause should be an (or ...) containing A
    (let ((c1 (nth 1 result))
          (c2 (nth 2 result)))
      (should (eq (car c1) 'or))
      (should (eq (car c2) 'or))
      (should (member 'A (cdr c1)))
      (should (member 'A (cdr c2)))
      ;; Together they should cover B and C
      (let ((non-a-lits (append (cl-remove 'A (cdr c1))
                                (cl-remove 'A (cdr c2)))))
        (should (member 'B non-a-lits))
        (should (member 'C non-a-lits))))))

(ert-deftest test-cnf-forall-impl ()
  "forall x.(P(x)->Q(x)) should produce one clause with 2 literals."
  (atp--reset-counters)
  (let ((clauses (atp--formula-to-clauses
                  '(forall (x) (implies (P x) (Q x))))))
    (should (= (length clauses) 1))
    (should (= (length (car clauses)) 2))))

(ert-deftest test-cnf-skolem-const ()
  "exists x.P(x) should Skolemize to P(_sk1)."
  (atp--reset-counters)
  (let* ((clauses (atp--formula-to-clauses '(exists (x) (P x))))
         (lit (car (car clauses))))
    (should (eq (car lit) 'P))
    (should (string-prefix-p "_sk" (symbol-name (nth 1 lit))))))

(ert-deftest test-cnf-skolem-func ()
  "forall x.exists y.loves(x,y) should produce Skolem function."
  (atp--reset-counters)
  (let* ((clauses (atp--formula-to-clauses
                   '(forall (x) (exists (y) (loves x y)))))
         (lit (car (car clauses))))
    (should (eq (car lit) 'loves))
    (should (consp (nth 2 lit)))
    (should (string-prefix-p "_sk" (symbol-name (car (nth 2 lit)))))))

;; ============================================================
;; VARIABLE STANDARDIZATION
;; ============================================================

(ert-deftest test-standardize-apart ()
  "Standardized clause has different vars from original."
  ;; Use high counter values to ensure no overlap
  (setq atp--var-counter 100)
  (let* ((clause '((P _V1) (Q _V1 _V2)))
         (new (atp--standardize-clause clause))
         (old-vars (atp--collect-vars clause))
         (new-vars (atp--collect-vars new)))
    ;; New vars should be different from old vars
    (should-not (cl-intersection old-vars new-vars))))

;; ============================================================
;; PROOF TESTS (positive)
;; ============================================================

(ert-deftest test-prove-socrates-mortal ()
  "All humans are mortal. Socrates is human. => mortal(socrates)."
  (should (prove '(mortal socrates)
                 '((forall (x) (implies (human x) (mortal x)))
                   (human socrates)))))

(ert-deftest test-prove-socrates-dies ()
  "human->mortal->dies chain."
  (should (prove '(dies socrates)
                 '((forall (x) (implies (mortal x) (dies x)))
                   (forall (x) (implies (human x) (mortal x)))
                   (human socrates)))))

(ert-deftest test-prove-tweety ()
  "canary->bird->eats worms."
  (should (prove '(eats tweety worms)
                 '((forall (x) (implies (canary x) (bird x)))
                   (forall (x) (implies (bird x) (eats x worms)))
                   (canary tweety)))))

(ert-deftest test-prove-happy-fluffy ()
  "cat->likes milk->happy."
  (should (prove '(happy fluffy)
                 '((forall (x) (implies (cat x) (likes x milk)))
                   (forall (x) (implies (likes x milk) (happy x)))
                   (cat fluffy)))))

(ert-deftest test-prove-direct-fact ()
  (should (prove '(P A) '((P A)))))

(ert-deftest test-prove-modus-ponens ()
  (should (prove '(Q A)
                 '((P A)
                   (forall (x) (implies (P x) (Q x)))))))

(ert-deftest test-prove-3-step ()
  "A->B->C->D chain."
  (should (prove '(D socrates)
                 '((forall (x) (implies (A x) (B x)))
                   (forall (x) (implies (B x) (C x)))
                   (forall (x) (implies (C x) (D x)))
                   (A socrates)))))

(ert-deftest test-prove-disjunctive-syllogism ()
  "P(A) v Q(A), ~P(A) => Q(A)."
  (should (prove '(Q A)
                 '((or (P A) (Q A))
                   (not (P A))))))

(ert-deftest test-prove-conjunction ()
  "P(A) ^ Q(A) => Q(A)."
  (should (prove '(Q A)
                 '((and (P A) (Q A))))))

(ert-deftest test-prove-multiple-individuals ()
  "Prove about plato specifically."
  (should (prove '(mortal plato)
                 '((forall (x) (implies (human x) (mortal x)))
                   (human socrates)
                   (human plato)
                   (human aristotle)))))

;; ============================================================
;; NEGATIVE TESTS (must NOT prove)
;; ============================================================

(ert-deftest test-neg-unrelated ()
  "Q(A) not provable from just P(A)."
  (should-not (prove '(Q A) '((P A)) nil 100)))

(ert-deftest test-neg-wrong-constant ()
  "P(B) not provable from P(A)."
  (should-not (prove '(P B) '((P A)) nil 100)))

(ert-deftest test-neg-missing-premise ()
  "mortal(socrates) not provable without human(socrates)."
  (should-not (prove '(mortal socrates)
                     '((forall (x) (implies (human x) (mortal x))))
                     nil 100)))

(ert-deftest test-neg-empty-kb ()
  (should-not (prove '(P A) '() nil 100)))

(ert-deftest test-neg-wrong-direction ()
  "P->Q does not allow inferring P from Q."
  (should-not (prove '(P A)
                     '((forall (x) (implies (P x) (Q x)))
                       (Q A))
                     nil 200)))

;; ============================================================
;; LITERAL & RESOLVE UNIT TESTS
;; ============================================================

(ert-deftest test-literal-atom ()
  (should (equal (atp--atom-of '(not (P _x))) '(P _x)))
  (should (equal (atp--atom-of '(P _x)) '(P _x))))

(ert-deftest test-negate-literal ()
  (should (equal (atp--negate-literal '(P _x)) '(not (P _x))))
  (should (equal (atp--negate-literal '(not (P _x))) '(P _x))))

(ert-deftest test-tautology ()
  (should (atp--tautology-p '((P A) (not (P A)))))
  (should-not (atp--tautology-p '((P A) (Q B)))))

(ert-deftest test-resolve-to-empty ()
  "Resolving {P(A)} with {~P(A)} => empty clause."
  (setq atp--var-counter 100)
  (let ((r (atp--resolve '((P A)) '((not (P A))))))
    (should r)
    (should (cl-some #'null r))))

(ert-deftest test-resolve-no-match ()
  "Resolving {P(A)} with {Q(B)} => nothing."
  (setq atp--var-counter 100)
  (should-not (atp--resolve '((P A)) '((Q B)))))

;; ============================================================
;; SUBSTITUTION TESTS
;; ============================================================

(ert-deftest test-subst-basic ()
  (should (equal (atp--apply-subst '((_x . A)) '(P _x)) '(P A))))

(ert-deftest test-subst-nested ()
  (should (equal (atp--apply-subst '((_x . A) (_y . B)) '(P (f _x) _y))
                 '(P (f A) B))))

(ert-deftest test-subst-chain ()
  "x->y, y->A => x resolves to A."
  (should (equal (atp--apply-subst '((_x . _y) (_y . A)) '_x) 'A)))

(ert-deftest test-subst-self-ref ()
  "Self-referential binding _x -> _x should not loop."
  (should (equal (atp--apply-subst '((_x . _x)) '_x) '_x)))

;; ============================================================
;; KB INTERFACE TEST
;; ============================================================

(ert-deftest test-kb-interface ()
  (atp-clear-kb)
  (atp-assert '(forall (x) (implies (human x) (mortal x))))
  (atp-assert '(human socrates))
  (should (atp-prove '(mortal socrates)))
  (atp-clear-kb))

;; ============================================================
;; Helper for interactive debug
;; ============================================================

(defun run-test-with-debug (test-name)
  "Run TEST-NAME with debug trace."
  (let ((sym (intern test-name)))
    (funcall (ert-test-body (ert-get-test sym)))))

(provide 'emacs-atp-tests)
;;; emacs-atp-tests.el ends here
