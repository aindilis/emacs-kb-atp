# Changelog

## [2.0.0] — 2026-03-10

Complete rewrite of the theorem prover. The original implementation had tests that passed trivially — the prover did not actually work. This version has been verified with 45 non-trivial ERT tests on Emacs 30.1.

### Added

- **Dungeon crawl game** (`atp-dungeon.el`): "Dún na Sí — The Mound of the Fair Folk," an Irish mythology–themed text adventure where the game world is a FOL knowledge base and the ATP validates all action preconditions.
- **45 ERT tests** (`emacs-atp-tests.el`): covering unification, CNF conversion, resolution, proof search (positive and negative), and the KB interface. Tests are non-trivial — they fail if the prover is broken.
- **Existential quantifier support** with Skolemization (Skolem constants and Skolem functions).
- **Given-clause algorithm** with set-of-support strategy and lightest-clause selection.
- **Tautology elimination** and clause deduplication in the resolution loop.
- **KB interface**: `atp-clear-kb`, `atp-assert`, `atp-prove` for incremental knowledge base use.
- **Sample proof trace** (`sample-proof.txt`) with annotated examples.
- Comprehensive `README.md` with usage examples, implementation notes, and future directions.

### Fixed

- **Variable/constant confusion**: The original had no way to distinguish variables from constants after quantifier dropping. Lowercase symbols like `socrates` and `x` were indistinguishable. Fixed by renaming all quantifier-bound variables to `_Vn` form during CNF conversion.
- **nil ≡ '() ≡ false conflation**: In Emacs Lisp, the empty substitution (success with no bindings) is `nil`, which is the same as `false`. Every guard in unification and resolution treated successful unification of identical terms as failure. Fixed with the `atp--empty-subst` marker: every substitution is seeded with a harmless `((atp--marker . t))` binding that makes success non-nil.
- **Infinite recursion in apply-subst**: When `atp--reset-counters` reset the variable counter, `standardize-clause` regenerated the same `_V1`, `_V2` names, creating self-referential bindings `(_V1 . _V1)` that looped infinitely. Fixed with a self-reference guard in `apply-subst` and identity-binding skip in `standardize-clause`.
- **Unification of compound terms**: The original used `cl-mapcar` to zip term arguments, which had subtle failures. Replaced with recursive car/cdr unification — the textbook Robinson algorithm that works naturally with ELisp cons cells.
- **Parser error in dungeon game**: `?)` in a `cl-case` clause was read as a character literal (the character `)`) rather than the symbol `?`, consuming the closing paren and leaving the form unbalanced.

### Changed

- Replaced backtick/comma quasi-quote with explicit `list` calls in core functions for robustness across Emacs versions.
- Replaced `cl-mapcan` with `(apply #'append (mapcar ...))` for maximum compatibility.
- CNF distribution now appends `ai` to the end of `others` for consistent clause ordering.

## [1.0.0] — 2024

Initial implementation. Tests passed but were trivially satisfied — the prover did not correctly perform resolution. Known issues included broken unification, incorrect CNF conversion for nested quantifiers, and no variable standardization apart.
