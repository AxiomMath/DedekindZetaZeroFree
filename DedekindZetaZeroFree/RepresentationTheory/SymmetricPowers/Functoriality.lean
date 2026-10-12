module

public import Mathlib.RepresentationTheory.Intertwining
public import DedekindZetaZeroFree.Algebra.SymmetricPower.TensorEmbedding

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/SymmetricPower.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open scoped TensorProduct

universe v w w'

variable {R : Type} {G : Type v} {M : Type w} {N : Type w'}

namespace Representation

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M]

noncomputable def symmetricPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (Sym[R]^d M) where
  toFun g := SymmetricPower.map (ι := Fin d) (ρ g)
  map_one' := by
    rw [ρ.map_one, Module.End.one_eq_id, SymmetricPower.map_id,
      Module.End.one_eq_id]
  map_mul' g h := by
    simpa only [map_mul, Module.End.mul_eq_comp] using
      (SymmetricPower.map_comp (ι := Fin d) (ρ h) (ρ g))

@[simp]
theorem symmetricPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.symmetricPower d g = SymmetricPower.map (ι := Fin d) (ρ g) :=
  (rfl)

theorem symmetricPower_apply_tprod (ρ : Representation R G M) (d : ℕ) (g : G) (m : Fin d → M) :
    ρ.symmetricPower d g (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, ρ g (m i) := by
  rw [symmetricPower_apply, SymmetricPower.map_tprod]

end CommSemiring

end Representation
