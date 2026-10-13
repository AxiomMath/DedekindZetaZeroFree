[![](logo.svg)](https://axiommath.ai/)

# Dedekind Zeta Zero-Free Region

This is a Lean formalization of Theorem 1.1 and Corollary 1.2 of
[A quasi-Riemann hypothesis for Dedekind zeta functions](https://hexagonmath.org/2610.00200v1).

The investigators, Dean Cureton and Jesse Thorner, directed the research and
made the mathematical judgments. AxiomProver generated the proofs and Lean
formalization. The work was developed at Axiom Math.

## Main Result

**Theorem 1.1.** If $K$ is any number field, then its Dedekind zeta function
$\zeta_K$ has no zeros in the half-plane

$$
\mathrm{Re}(s) > \frac{31}{32}.
$$

**Corollary 1.2.** The same zero-free region holds for finite-order Hecke
L-functions, with $s = 1$ included for nonprincipal characters.

The formal proof uses only Lean's three standard axioms: `propext`,
`Quot.sound`, and `Classical.choice`.

See [§Formal Challenge](#formal-challenge) for the formal statement and
verification instructions.

## Dependencies

This project depends on:

* [Mathlib](https://github.com/leanprover-community/mathlib4).
* [Tau Ceti](https://github.com/TauCetiProject/TauCeti).
* [FiniteAbelianGlobalReciprocityv2](https://github.com/PalomarArchive/n-yamaguchi-0729--FiniteAbelianGlobalReciprocityv2--ccc6f4bb14f4),
  vendored under `vendor/class-field-theory` with compatibility changes.

It also includes code adapted from Tau Ceti and:

* [LeanPool/lean-pool](https://github.com/LeanPool/lean-pool):
  Dedekind zeta functions and algebraic number theory.
* [openai/math](https://github.com/openai/math):
  analytic number theory.

## Formal Challenge

[Solution/DedekindZetaSolution.lean](Solution/DedekindZetaSolution.lean)
proves `DedekindZetaZeroFree.main` and `DedekindZetaZeroFree.heckeCorollary` from
[Challenge/DedekindZetaChallenge.lean](Challenge/DedekindZetaChallenge.lean),
using the library's [main theorem](DedekindZetaZeroFree/Main.lean) and
[Hecke corollary](DedekindZetaZeroFree/HeckeCorollary.lean).

To build:

```sh
lake exe cache get
lake build
```

To run comparator:

```sh
lake comparator --config comparator.json
```
