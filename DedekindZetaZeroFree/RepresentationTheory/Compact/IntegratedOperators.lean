module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ContinuousAveraging
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.Characters
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.SchurLemma
public import DedekindZetaZeroFree.RepresentationTheory.Irreducible.SubrepresentationsAndEigenvectors

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/Integrated.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open _root_.ContRepresentation

open MeasureTheory

namespace DedekindZetaZeroFree.TauCeti

namespace ContRepresentation

section Conjugation

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjMap (h : G) : C(G, G) :=
  (ContinuousMap.mulLeft h⁻¹).comp (ContinuousMap.mulRight h)

private theorem conjMap_apply (h g : G) : conjMap h g = h⁻¹ * (g * h) :=
  (rfl)

variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

private theorem haarAverage_comp_conjMap {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] (F : C(G, W)) (h : G) :
    haarAverage G (𝕜 := 𝕜) (F.comp (conjMap h)) = haarAverage G (𝕜 := 𝕜) F := by
  rw [conjMap, ← ContinuousMap.comp_assoc, haarAverage_comp_mulRight, haarAverage_comp_mulLeft]

end Conjugation

section Integrated

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

omit [CompleteSpace V] in

noncomputable def weightFamily (f : C(G, 𝕜)) : C(G, V →L[𝕜] V) where
  toFun g := f g • π g
  continuous_toFun := f.continuous.smul hπ

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in

@[simp]
private theorem weightFamily_apply (f : C(G, 𝕜)) (g : G) :
    weightFamily π hπ f g = f g • π g :=
  (rfl)

omit [CompleteSpace V] in

noncomputable def integratedOperator (f : C(G, 𝕜)) : V →L[𝕜] V :=
  haarAverage G (𝕜 := 𝕜) (weightFamily π hπ f)

theorem integratedOperator_apply (f : C(G, 𝕜)) (v : V) :
    integratedOperator π hπ f v = ∫ g, f g • π g v ∂haarProb G := by
  have h := (ContinuousLinearMap.apply 𝕜 V v).haarAverage_comp_comm (G := G)
    (weightFamily π hπ f)
  simp only [ContinuousLinearMap.apply_apply] at h
  rw [integratedOperator, ← h, haarAverage_apply]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, ContinuousLinearMap.apply_apply,
    weightFamily_apply, smul_apply]

omit [CompleteSpace V] in
@[simp]
theorem integratedOperator_zero : integratedOperator π hπ (0 : C(G, 𝕜)) = 0 := by
  have hzero : weightFamily π hπ (0 : C(G, 𝕜)) = 0 := by
    ext g v
    simp
  rw [integratedOperator, hzero, map_zero]

omit [CompleteSpace V] in
@[simp]
theorem integratedOperator_add (f₁ f₂ : C(G, 𝕜)) :
    integratedOperator π hπ (f₁ + f₂)
      = integratedOperator π hπ f₁ + integratedOperator π hπ f₂ := by
  have hadd : weightFamily π hπ (f₁ + f₂) = weightFamily π hπ f₁ + weightFamily π hπ f₂ := by
    ext g v
    simp [add_smul]
  rw [integratedOperator, integratedOperator, integratedOperator, hadd, map_add]

omit [CompleteSpace V] in
@[simp]
theorem integratedOperator_smul (c : 𝕜) (f : C(G, 𝕜)) :
    integratedOperator π hπ (c • f) = c • integratedOperator π hπ f := by
  have hsmul : weightFamily π hπ (c • f) = c • weightFamily π hπ f := by
    ext g v
    simp [mul_smul]
  rw [integratedOperator, integratedOperator, hsmul, map_smul]

omit [CompleteSpace V] in

noncomputable def integratedOperatorₗ : C(G, 𝕜) →ₗ[𝕜] V →L[𝕜] V where
  toFun := integratedOperator π hπ
  map_add' := integratedOperator_add π hπ
  map_smul' := integratedOperator_smul π hπ

omit [CompleteSpace V] in
@[simp]
theorem integratedOperatorₗ_apply (f : C(G, 𝕜)) :
    integratedOperatorₗ π hπ f = integratedOperator π hπ f :=
  (rfl)

noncomputable def conjOp (h : G) : (V →L[𝕜] V) →L[𝕜] V →L[𝕜] V :=
  (ContinuousLinearMap.compL 𝕜 V V V (π h⁻¹)).comp
    ((ContinuousLinearMap.compL 𝕜 V V V).flip (π h))

omit hπ [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in

private theorem conjOp_apply (h : G) (S : V →L[𝕜] V) :
    conjOp π h S = (π h⁻¹).comp (S.comp (π h)) := by
  simp [conjOp, ContinuousLinearMap.compL_apply]

variable {f : C(G, 𝕜)} (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)

include hf

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in

private theorem conjOp_comp_weightFamily (h : G) :
    (conjOp π h : C(V →L[𝕜] V, V →L[𝕜] V)).comp (weightFamily π hπ f)
      = (weightFamily π hπ f).comp (conjMap h) := by
  ext g v
  have hclass : f (h⁻¹ * (g * h)) = f g := by
    have := hf g h⁻¹
    rwa [inv_inv, mul_assoc] at this
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, conjOp_apply,
    ContinuousLinearMap.comp_apply, weightFamily_apply, conjMap_apply, hclass, smul_apply,
    map_smul, map_mul π, mul_apply_eq_comp]

private theorem conjOp_integratedOperator (h : G) :
    conjOp π h (integratedOperator π hπ f) = integratedOperator π hπ f := by
  rw [integratedOperator, ← ContinuousLinearMap.haarAverage_comp_comm,
    conjOp_comp_weightFamily π hπ hf h, haarAverage_comp_conjMap]

theorem integratedOperator_comp (h : G) :
    (integratedOperator π hπ f).comp (π h) = (π h).comp (integratedOperator π hπ f) := by
  have hconj := conjOp_integratedOperator π hπ hf h
  rw [conjOp_apply] at hconj
  have hid : (π h).comp (π h⁻¹) = ContinuousLinearMap.id 𝕜 V := by
    rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_def]
  calc (integratedOperator π hπ f).comp (π h)
      = (ContinuousLinearMap.id 𝕜 V).comp ((integratedOperator π hπ f).comp (π h)) := by
        rw [ContinuousLinearMap.id_comp]
    _ = ((π h).comp (π h⁻¹)).comp ((integratedOperator π hπ f).comp (π h)) := by rw [hid]
    _ = (π h).comp ((π h⁻¹).comp ((integratedOperator π hπ f).comp (π h))) :=
        ContinuousLinearMap.comp_assoc _ _ _
    _ = (π h).comp (integratedOperator π hπ f) := by rw [hconj]

noncomputable def integratedIntertwiner : ContIntertwiningMap π π where
  __ := integratedOperator π hπ f
  isIntertwining' h := integratedOperator_comp π hπ hf h

@[simp]
theorem toContinuousLinearMap_integratedIntertwiner :
    (integratedIntertwiner π hπ hf).toContinuousLinearMap = integratedOperator π hπ f :=
  (rfl)

end Integrated

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceIntegrated : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

theorem trace_integratedOperator (f : C(G, 𝕜)) :
    LinearMap.trace 𝕜 V (integratedOperator π hπ f : V →ₗ[𝕜] V)
      = ∫ g, f g * character π hπ g ∂haarProb G := by
  have h := (traceCLM 𝕜 V).haarAverage_comp_comm (G := G) (weightFamily π hπ f)
  rw [← traceCLM_apply, integratedOperator, ← h, haarAverage_apply]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, weightFamily_apply, map_smul,
    traceCLM_apply, smul_eq_mul, character_apply]

variable [IsAlgClosed 𝕜] {f : C(G, 𝕜)} (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)

include hf

theorem integratedOperator_eq_smul_id
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    integratedOperator π hπ f
      = ((Module.finrank 𝕜 V : 𝕜)⁻¹ * ∫ g, f g * character π hπ g ∂haarProb G) •
        ContinuousLinearMap.id 𝕜 V := by
  have hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0 :=
    Representation.IsIrreducible.natCast_finrank_ne_zero hirr
  have h := π.eq_finrank_inv_mul_trace_smul_id_of_isIrreducible hdim hirr
    (integratedIntertwiner π hπ hf)
  rwa [toContinuousLinearMap_integratedIntertwiner, trace_integratedOperator] at h

theorem integratedOperator_eq_zero
    (hirr : Representation.IsIrreducible π.toRepresentation)
    (hzero : ∫ g, f g * character π hπ g ∂haarProb G = 0) :
    integratedOperator π hπ f = 0 := by
  rw [integratedOperator_eq_smul_id π hπ hf hirr, hzero, mul_zero, zero_smul]

end Trace

end ContRepresentation

end DedekindZetaZeroFree.TauCeti
