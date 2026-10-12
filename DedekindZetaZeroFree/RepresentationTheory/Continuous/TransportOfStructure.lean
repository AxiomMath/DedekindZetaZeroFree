module

public import DedekindZetaZeroFree.RepresentationTheory.Continuous.MatrixCoefficients
public import DedekindZetaZeroFree.RepresentationTheory.Irreducible.SubrepresentationsAndEigenvectors

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/Transport.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

namespace ContRepresentation

section Congr

variable {𝕜 G V W : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

noncomputable def congr (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) :
    ContRepresentation 𝕜 G W :=
  .ofMonoidHom
    { toFun g := e.conjContinuousAlgEquiv (π g)
      map_one' := by simp
      map_mul' g h := by rw [map_mul, map_mul] }

omit [TopologicalSpace G] in

theorem congr_apply (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) (g : G) (x : W) :
    congr e π g x = e (π g (e.symm x)) :=
  (rfl)

omit [TopologicalSpace G] in

@[simp]
theorem coe_congr (e : V ≃L[𝕜] W) (π : ContRepresentation 𝕜 G V) :
    ⇑(congr e π) = fun g ↦ e.conjContinuousAlgEquiv (π g) := by
  funext g
  apply ContinuousLinearMap.ext
  intro x
  exact congr_apply e π g x

theorem continuous_congr (e : V ≃L[𝕜] W) {π : ContRepresentation 𝕜 G V} (hπ : Continuous π) :
    Continuous (congr e π) :=
  (map_continuous e.conjContinuousAlgEquiv).comp hπ

omit [TopologicalSpace G] in

theorem isIrreducible_congr (e : V ≃L[𝕜] W) {π : ContRepresentation 𝕜 G V}
    (hπ : π.toRepresentation.IsIrreducible) : (congr e π).toRepresentation.IsIrreducible :=
  Representation.isIrreducible_of_linearEquiv (e : V ≃ₗ[𝕜] W)
    (fun g v ↦ by simp [_root_.ContRepresentation.toMonoidHom_apply]) hπ

omit [TopologicalSpace G] in

@[simp]
theorem congr_refl (π : ContRepresentation 𝕜 G V) :
    congr (ContinuousLinearEquiv.refl 𝕜 V) π = π :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

omit [TopologicalSpace G] in

@[simp]
theorem congr_congr {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : V ≃L[𝕜] W)
    (f : W ≃L[𝕜] X) (π : ContRepresentation 𝕜 G V) :
    congr f (congr e π) = congr (e.trans f) π :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

end Congr

section CongrIsometry

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

@[simp]
theorem matrixCoeff_congr (e : V ≃ₗᵢ[𝕜] W) {π : ContRepresentation 𝕜 G V}
    (hπ : Continuous (congr e.toContinuousLinearEquiv π)) (v w : V) :
    matrixCoeff (congr e.toContinuousLinearEquiv π) hπ (e v) (e w) =
      matrixCoeff π (by simpa using continuous_congr e.toContinuousLinearEquiv.symm hπ) v w := by
  ext g
  simp

end CongrIsometry

end ContRepresentation

end DedekindZetaZeroFree.TauCeti
