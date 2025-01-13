# Emacs ATP - A First-Order Logic Theorem Prover

A lightweight automated theorem prover implemented in Emacs Lisp, supporting first-order logic resolution.

## Features

- First-order logic formula parsing and manipulation
- Resolution-based proof search
- Support for:
  - Universal quantification
  - Implications
  - Conjunctions and disjunctions
  - Negation
- Conversion pipeline:
  - CNF conversion
  - Implication elimination
  - Quantifier handling
  - Negation normal form
- Comprehensive test suite using ERT

## Usage

### Basic Proof

```elisp
(prove '(dies socrates)
       '((forall (x) (implies (mortal x) (dies x)))
         (forall (x) (implies (human x) (mortal x)))
         (human socrates))
       t)  ; t enables debug output
```

### Formula Syntax

- Predicates: `(predicate arg1 arg2 ...)`
- Negation: `(not formula)`
- Implication: `(implies antecedent consequent)`
- Universal quantification: `(forall (var) formula)`
- Conjunction: `(and formula1 formula2 ...)`
- Disjunction: `(or formula1 formula2 ...)`

### Example Proofs

```elisp
;; Simple transitivity
(prove '(eats tweety worms)
       '((forall (x) (implies (canary x) (bird x)))
         (forall (x) (implies (bird x) (eats x worms)))
         (canary tweety))
       t)

;; Multiple steps
(prove '(happy fluffy)
       '((forall (x) (implies (cat x) (likes x milk)))
         (forall (x) (implies (likes x milk) (happy x)))
         (cat fluffy))
       t)
```

### Running Tests

The system comes with a comprehensive test suite using ERT:

```elisp
;; Run all tests
(ert "^test-")

;; Run specific test
(ert 'test-socrates-mortality)

;; Run test with debug output
(run-test-with-debug "test-socrates-mortality")
```

## Implementation Details

The prover implements several key components:

1. **Formula Parsing**: Converts S-expressions to internal formula representation
2. **CNF Conversion Pipeline**:
   - Implication elimination
   - Quantifier handling
   - Conversion to negation normal form
   - Distribution of OR over AND
3. **Clause Formation**: Converts CNF formulas to clauses for resolution
4. **Resolution**: Implements basic resolution with unification
5. **Proof Search**: Uses a simple given-clause algorithm

## Limitations

Current limitations include:
- No support for equality reasoning
- Limited term indexing
- Basic clause selection heuristics
- No proof extraction/reconstruction
- No binding extraction for queries

## Future Enhancements

Planned improvements:
- Support for equality reasoning
- Advanced term indexing
- Improved selection heuristics
- Proof reconstruction
- Query binding extraction
- Support for more sophisticated strategies

## Testing

The system includes tests for:
- Basic syllogisms
- Transitive reasoning
- Multiple-step deductions
- Conjunction handling
- Double negation
- Complex inference chains
- Negative cases
- Contradiction handling

## License

GNU General Public License v3.0 (GPLv3)

This project is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

See [COPYING](https://www.gnu.org/licenses/gpl-3.0.txt) for details.

## Contributing

Contributions are welcome! Key areas for improvement:
- Additional test cases
- Performance optimizations
- Enhanced proof strategies
- Documentation improvements
- Bug fixes
