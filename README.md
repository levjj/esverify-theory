# Formalism and Proofs for esverify

This repository contains a formal definition of [esverify](https://esverify.org/)
and proves properties such as verification safety and type translation correctness.

The definitions and proofs are written in [LEAN](http://leanprover.github.io/).

## Important Files

[`src/syntax.lean`](src/syntax.lean)

- Inductive definitions of syntactical objects such as values. expressions, terms, propositions, etc.

[`src/definitions1.lean`](src/definitions1.lean)

- Variable substitution in terms and propositions
- Lifting of quantifiers in propositions (part of quantifier instantiation)

[`src/definitions2.lean`](src/definitions2.lean)

- Quantifier instantiation algorithm
- Evaluation of program expressions
- Axiomatization of SMT Logic
- Verification of program expressions

[`src/theorems.lean`](src/theorems.lean)

- Quantifier Instantiation Soundness Theorem
- Verification Safety/Soundness Theorem

*All other files contains lemmas and helper definitions but no axioms.*

## Proved Theorems

**Quantifier Instantiation**

Verification conditions are processed with a deterministic quantifier instantiation algorithm
in order to ensure that checking of verification conditions is deterministic and decidable.

The following theorem states that any proposition `P` that is valid with instantiations `⟪ P ⟫`
is also a valid proposition without quantifier instantiation `⦃ P ⦄`:

```
⟪ P ⟫ → ⦃ P ⦄
```

(The converse is not true. There are valid propositions that cannot be confirmed when the
quantifier instantiation algorithm is used. Instead of relying on heuristics, the instantiation
uses function calls in the source program as triggers.)

**Verification Safety**

The following theorem states that a verified source program `e` does not get stuck,
i.e. its evaluation always results either in a value or in a runtime stack `s` that can be further evaluated.
The proof internally uses lemmas for progress and preservation.

```
(value.true ⊢ e: Q) → ((env.empty, e) ⟶* s) → (is_value s ∨ ∃s', s ⟶ s')
```
*These theorems can be found in the file [src/theorems.lean](src/theorems.lean).*

## Checking the proof

Assuming [LEAN](http://leanprover.github.io/) is installed, the proofs can be checked by building the entire project:

```
$ leanpkg build
```

Alternatively, is it possible to specifically check certain files, e.g.

```
$ lean src/theorems.lean
```
