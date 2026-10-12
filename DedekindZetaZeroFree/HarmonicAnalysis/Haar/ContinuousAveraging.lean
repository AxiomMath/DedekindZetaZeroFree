module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactProbabilityMeasure

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Compact/Averaging.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

/-
https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md
-/

open MeasureTheory

namespace DedekindZetaZeroFree.TauCeti

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {V : Type*} [NormedAddCommGroup V]

theorem integrable_continuousMap (f : C(G, V)) :
    Integrable f (haarProb G) := by
  simpa only [integrableOn_univ] using
    f.continuous.continuousOn.integrableOn_compact' (μ := haarProb G) isCompact_univ
      MeasurableSet.univ

section NormedFieldScalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [SMulCommClass ℝ 𝕜 V]

noncomputable def haarAverage : C(G, V) →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ g, f g ∂haarProb G
      map_add' := fun f h ↦ integral_add
        (integrable_continuousMap G f) (integrable_continuousMap G h)
      map_smul' := fun c f ↦ integral_smul c f }
    1 fun f ↦ by
      rw [one_mul]
      simpa using norm_integral_le_of_norm_le_const
        (μ := haarProb G) (Filter.Eventually.of_forall f.norm_coe_le_norm)

theorem haarAverage_apply (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = ∫ g, f g ∂haarProb G :=
  (rfl)

@[simp]
theorem haarAverage_const [CompleteSpace V] (v : V) :
    haarAverage G (𝕜 := 𝕜) (ContinuousMap.const G v) = v := by
  simp [haarAverage_apply]

@[simp]
theorem haarAverage_comp_mulLeft (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulLeft g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulLeft]
  exact integral_mul_left_eq_self f g

@[simp]
theorem haarAverage_comp_mulRight (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulRight g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulRight]
  exact integral_mul_right_eq_self f g

@[simp]
theorem haarAverage_comp_inv (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) (f.comp (Homeomorph.inv G : C(G, G))) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_coe, Homeomorph.coe_inv]
  exact integral_inv_eq_self f (haarProb G)

end NormedFieldScalars

section RCLikeScalars

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]

@[simp]
theorem _root_.ContinuousLinearMap.haarAverage_comp_comm {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedSpace 𝕜 W] [SMulCommClass ℝ 𝕜 W] [CompleteSpace V] [CompleteSpace W]
    (L : V →L[𝕜] W) (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) ((L : C(V, W)).comp f) = L (haarAverage G (𝕜 := 𝕜) f) := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_coe]
  exact L.integral_comp_comm (integrable_continuousMap G f)

end RCLikeScalars

end CompactGroup

end DedekindZetaZeroFree.TauCeti
