# Emacs KB-ATP — Knowledge-Base Automated Theorem Prover

A first-order logic resolution theorem prover implemented in Emacs Lisp, with a companion dungeon crawl game whose entire world state is maintained as a FOL knowledge base.

Part of the [FRDCSA](https://github.com/aindilis/frdcsa) project (Formalized Research Database: Cluster, Study and Apply).

## Overview

**emacs-atp** implements a complete resolution refutation prover:

- **CNF conversion pipeline**: implication elimination → negation normal form → Skolemization → quantifier dropping → distribution of ∨ over ∧
- **Robinson unification** with occur check
- **Variable standardization apart** for safe resolution
- **Given-clause algorithm** with set-of-support strategy
- **Tautology elimination** and clause deduplication

**atp-dungeon** ("Dún na Sí — The Mound of the Fair Folk") is an Irish mythology–themed text adventure where:

- The game world IS a FOL theory
- Action preconditions are proved by the ATP (not pattern-matched)
- NPC dialog adapts based on what's provable from the current KB
- Puzzles require satisfying logical preconditions

## Quick Start

### Running the Prover

```elisp
;; Load the prover
(load-file "emacs-atp.el")

;; Classic syllogism: All humans are mortal. Socrates is human.
(prove '(mortal socrates)
       '((forall (x) (implies (human x) (mortal x)))
         (human socrates))
       t)  ; t enables debug output
;; => t (proved!)

;; Multi-step chain
(prove '(dies socrates)
       '((forall (x) (implies (mortal x) (dies x)))
         (forall (x) (implies (human x) (mortal x)))
         (human socrates)))
;; => t

;; Correctly fails when premises are missing
(prove '(mortal socrates)
       '((forall (x) (implies (human x) (mortal x))))
       nil 100)
;; => nil (cannot prove without the fact that Socrates is human)
```

### Knowledge Base Interface

```elisp
(atp-clear-kb)
(atp-assert '(forall (x) (implies (human x) (mortal x))))
(atp-assert '(human socrates))
(atp-assert '(human plato))

(atp-prove '(mortal socrates))  ; => t
(atp-prove '(mortal plato))     ; => t
(atp-prove '(mortal zeus))      ; => nil
```

### Running Tests

```sh
emacs --batch -Q -l emacs-atp.el -l emacs-atp-tests.el -f ert-run-tests-batch-and-exit
```

All 45 tests should pass (runs in ~10ms).

### Playing the Dungeon Game

```elisp
;; In an interactive Emacs session:
(load-file "emacs-atp.el")
(load-file "atp-dungeon.el")
M-x dungeon-start
```

## Formula Syntax

| Form | Syntax | Example |
|------|--------|---------|
| Predicate | `(pred arg1 arg2 ...)` | `(human socrates)` |
| Negation | `(not formula)` | `(not (human zeus))` |
| Implication | `(implies ante conseq)` | `(implies (human x) (mortal x))` |
| Universal | `(forall (var) formula)` | `(forall (x) (implies (P x) (Q x)))` |
| Existential | `(exists (var) formula)` | `(exists (x) (loves x juliet))` |
| Conjunction | `(and f1 f2 ...)` | `(and (P A) (Q B))` |
| Disjunction | `(or f1 f2 ...)` | `(or (P A) (Q A))` |

Variables in user formulas are any symbols bound by `forall` or `exists`. Everything else (including lowercase symbols like `socrates`) is treated as a constant or functor. Internally, bound variables are renamed to `_V1`, `_V2`, etc. during CNF conversion.

## File Listing

| File | Description |
|------|-------------|
| `emacs-atp.el` | The theorem prover (~470 lines) |
| `emacs-atp-tests.el` | 45 ERT tests (~310 lines) |
| `atp-dungeon.el` | Dungeon crawl game (~635 lines) |
| `sample-proof.txt` | Annotated proof traces |
| `CHANGELOG.md` | Development history and bugs fixed |
| `LICENSE` | GPL-3.0 |

## How the Dungeon Game Uses the ATP

The game maintains its world state as a list of FOL facts and rules. When the player attempts an action, the ATP tries to *prove* that the action's preconditions hold.

For example, to unlock the treasury:

```
Rules:  ∀k,d. has(player,k) ∧ key-for(k,d) ∧ locked(d) → can-unlock(player,d)
KB:     has(player, rusty-key), key-for(rusty-key, treasury), locked(treasury)
Query:  can-unlock(player, treasury)?
```

The ATP performs resolution refutation: it negates the goal, converts everything to clausal form, and searches for a contradiction. If it finds one, the goal is proved and the action succeeds. If not, the action is denied.

This means the game's logic is **sound** — you can't exploit edge cases in if/else chains because the rules are FOL axioms and the engine is a theorem prover. The Sword of Light truly must be in your inventory for the ATP to derive `can-fight(player, balor)`.

### Game Commands

```
go <room>              Travel to a connected room
look                   Look around
take <item>            Pick up an item
use <item>             Use an item
use <item> on <target> Use item on something
talk <npc>             Talk to someone
inventory              Check what you carry
query <expr>           Query the knowledge base (advanced)
help                   Show commands
quit                   Leave the game
```

Room names use hyphens: `crystal-cavern`, `dark-passage`, `great-hall`, etc.

## Implementation Notes

### The nil ≡ '() ≡ false Problem

The most subtle bug in the implementation was an Emacs Lisp–specific issue: `nil`, `'()` (empty list), and `false` are all the same value. When two terms are already identical, unification succeeds with an empty substitution — but the empty substitution `'()` is `nil`, which every `when`/`if` guard treats as failure.

The fix: every substitution is seeded with a harmless marker binding `((atp--marker . t))`. Since `atp--marker` starts with `a` (not `_`), it is never treated as a variable and never interferes with unification. But it makes successful substitutions non-nil.

This is worth noting for anyone implementing logic systems in Emacs Lisp.

### Variable Convention

User-facing formulas use any symbol names — `x`, `socrates`, `tweety` are all fine. During CNF conversion, all quantifier-bound variables are renamed to `_V1`, `_V2`, etc. After quantifier dropping, the rule is: a symbol is a variable iff it starts with `_` (but not `_sk` for Skolem symbols). This cleanly separates variables from constants without requiring any naming convention from the user.

### CNF Conversion Pipeline

```
User formula
  → rename quantified vars to _Vn
  → eliminate implications (P→Q becomes ¬P∨Q)
  → negation normal form (push ¬ inward)
  → Skolemize (remove ∃, introduce Skolem functions)
  → drop universal quantifiers (implicit in clausal form)
  → distribute ∨ over ∧
  → extract clauses
```

## Test Categories

The test suite is designed to be **non-trivial** — tests that would fail if the prover were broken:

- **Unification** (12 tests): compound terms, occur check, variable chains, arity/functor mismatches
- **CNF pipeline** (7 tests): implication elimination, De Morgan, double negation, Skolemization, distribution
- **Proofs** (10 tests): direct facts, modus ponens, multi-step chains, disjunctive syllogism, conjunction extraction
- **Negative tests** (5 tests): unrelated facts, wrong constants, missing premises, empty KB, wrong implication direction
- **Resolution** (2 tests): resolving to empty clause, no-match cases
- **Substitution** (4 tests): basic, nested, chains, self-reference safety
- **Infrastructure** (5 tests): variable collection, standardization apart, literal operations, tautology detection, KB interface

## Future Directions

### Binding Extraction for Queries

Currently the prover answers yes/no. The next priority is extracting variable bindings from proofs, enabling queries like:

```elisp
(atp-query '(mortal ?who)
           '((forall (x) (implies (human x) (mortal x)))
             (human socrates)
             (human plato)))
;; => ((?who . socrates) (?who . plato))
```

This would use an "answer literal" technique: thread a special literal through the refutation that collects substitutions, yielding Prolog-style query results with an iterator/generator interface.

### ACL2-Style Reasoning over Emacs Lisp

Define a pure-functional ELisp subset (no side effects), represent function definitions as FOL axioms, and use the ATP to prove properties about ELisp code:

```elisp
;; Define
(atp-defun my-append (x y)
  (if (null x) y (cons (car x) (my-append (cdr x) y))))

;; Prove
(atp-verify '(= (my-append (my-append x y) z)
               (my-append x (my-append y z))))
```

### Expanded Dungeon Game

- More rooms, items, and ATP-driven puzzles
- NPC dialog trees driven by logical inference
- Combat system using weapon/armor effectiveness axioms
- Procedurally generated content from knowledge base templates

### FRDCSA Integration

- Connect to Prolog-Agent via `emacs-pengines-client`
- Bridge to Free Life Planner for real-world task reasoning
- Use KM/NextKB/Scone concepts for frame-based reasoning layers
- Connect TESUJI Go analysis (positional concepts as FOL axioms)

### Performance

- Term indexing for faster clause selection
- Subsumption-based clause deletion
- More sophisticated selection heuristics (e.g., clause weight by symbol count)
- Support for equality reasoning (paramodulation)

## Presented At

- [EmacsConf 2019](https://emacsconf.org/2019/): "A.I. that Helps Play the Game of Your Life"

## License

GNU General Public License v3.0 — see [LICENSE](LICENSE).

## Author

Andrew Dougherty ([@aindilis](https://github.com/aindilis))
