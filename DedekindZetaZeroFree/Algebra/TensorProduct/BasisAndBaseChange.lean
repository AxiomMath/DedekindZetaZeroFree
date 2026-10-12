module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import DedekindZetaZeroFree.Algebra.TensorProduct.ComponentsAndNaturality

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/TensorProduct/Basis.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open TensorProduct
open scoped TensorProduct

namespace TensorProduct

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

theorem tensor_eq_of_forall_tensorComponent_eq [Module.Projective R N] {x y : M ⊗[R] N}
    (h : ∀ φ : Module.Dual R N,
      _root_.LinearMap.tensorComponent (R := R) (M := M) φ x =
        _root_.LinearMap.tensorComponent (R := R) (M := M) φ y) :
    x = y := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R N)
  let b := Finsupp.basisSingleOne (R := R) (ι := N)
  have hcomponent (φ : (N →₀ R) →ₗ[R] R) (t : M ⊗[R] (N →₀ R)) :
      TensorProduct.rid R M (φ.lTensor M t) =
        _root_.LinearMap.tensorComponent φ t := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m n => simp
  have hmap : TensorProduct.map LinearMap.id s x = TensorProduct.map LinearMap.id s y := by
    apply (TensorProduct.equivFinsuppOfBasisRight b (M := M)).injective
    ext i
    rw [TensorProduct.equivFinsuppOfBasisRight_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply]
    calc
      TensorProduct.rid R M
          ((b.coord i).lTensor M (TensorProduct.map LinearMap.id s x)) =
          _root_.LinearMap.tensorComponent (b.coord i)
            (TensorProduct.map LinearMap.id s x) := by
            exact hcomponent (b.coord i) _
      _ = LinearMap.id (_root_.LinearMap.tensorComponent ((b.coord i).comp s) x) :=
        _root_.LinearMap.tensorComponent_map (b.coord i) LinearMap.id s x
      _ = LinearMap.id (_root_.LinearMap.tensorComponent ((b.coord i).comp s) y) := by
        rw [h ((b.coord i).comp s)]
      _ = _root_.LinearMap.tensorComponent (b.coord i)
          (TensorProduct.map LinearMap.id s y) :=
        (_root_.LinearMap.tensorComponent_map (b.coord i) LinearMap.id s y).symm
      _ = TensorProduct.rid R M
          ((b.coord i).lTensor M (TensorProduct.map LinearMap.id s y)) := by
            exact (hcomponent (b.coord i) _).symm
  let p : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R id
  have hleft (z : M ⊗[R] N) :
      TensorProduct.map LinearMap.id p (TensorProduct.map LinearMap.id s z) = z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m n =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply]
        rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  calc
    x = TensorProduct.map LinearMap.id p (TensorProduct.map LinearMap.id s x) := (hleft x).symm
    _ = TensorProduct.map LinearMap.id p (TensorProduct.map LinearMap.id s y) := congrArg _ hmap
    _ = y := hleft y

end TensorProduct

namespace Module.Basis

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable [AddCommMonoid N] [Module R N]

section EquivFinsuppOfBasisLeft

variable {ι : Type*} [DecidableEq ι] {P : Type*} [AddCommMonoid P] [Module R P]

variable (ℬ : Module.Basis ι R M)

@[simp]
theorem equivFinsuppOfBasisLeft_lTensor_apply (g : N →ₗ[R] P) (x : M ⊗[R] N) (i : ι) :
    equivFinsuppOfBasisLeft ℬ (g.lTensor M x) i = g (equivFinsuppOfBasisLeft ℬ x i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul m n => simp

end EquivFinsuppOfBasisLeft

end Module.Basis

namespace Module.Basis

universe u v w x

variable {R : Type u} [CommSemiring R]

variable {M : Type x} [AddCommMonoid M] [Module R M]

variable {ι : Type*}

section Repr

variable {S : Type v} [Semiring S] [Algebra R S]

variable {T : Type w} [Semiring T] [Algebra R T]

@[simp] theorem map_baseChange_repr (b : Basis ι R M) (φ : S →ₗ[R] T)
    (z : S ⊗[R] M) (i : ι) :
    φ ((b.baseChange S).repr z i) =
      (b.baseChange T).repr
        (TensorProduct.map φ LinearMap.id z) i := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul s m => simp

end Repr

section Matrix

variable {S : Type v} [CommSemiring S] [Algebra R S]

variable {T : Type w} [CommSemiring T] [Algebra R T]

@[simp] theorem baseChange_toMatrix_baseChange {ι' : Type*} (b : Basis ι R M)
    (b' : Basis ι' R M) :
    (b.baseChange S).toMatrix (b'.baseChange S) = (b.toMatrix b').map (algebraMap R S) := by
  ext i j
  simp [toMatrix_apply, baseChange_apply, Algebra.smul_def]

end Matrix

end Module.Basis
