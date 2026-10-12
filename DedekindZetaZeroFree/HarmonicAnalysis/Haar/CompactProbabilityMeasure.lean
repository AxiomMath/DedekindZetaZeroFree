module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Compact/Haar.lean`.
Original Apache-2.0 copyright and author notice retained above.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Only the enclosing namespace/module surface is adapted; proof bodies are unchanged.
Apache-2.0: https://www.apache.org/licenses/LICENSE-2.0
-/

/-
https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md
Source: Suggested.lean.
-/

open MeasureTheory Set

namespace DedekindZetaZeroFree.TauCeti

section LocallyCompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem haar_univ_ne_zero : (Measure.haar : Measure G) univ ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior (μ := Measure.haar) (by simp)).ne'

theorem isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : (Measure.map (· * g) μ).IsHaarMeasure :=
      Measure.isHaarMeasure_map_mul_right μ g
    have : IsProbabilityMeasure (Measure.map (· * g) μ) :=
      inferInstance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsInvInvariant := by
  have : μ.IsMulRightInvariant :=
    isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) μ
  constructor
  let : μ.inv.IsHaarMeasure := {
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsMulLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }
  let : IsProbabilityMeasure μ.inv := by
    rw [Measure.inv_def]
    infer_instance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end LocallyCompactGroup

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

noncomputable def haarFinite : FiniteMeasure G :=
  ⟨Measure.haar, inferInstance⟩

private theorem haarFinite_toMeasure : (haarFinite G : Measure G) = Measure.haar := by
  ext s hs
  rfl

private theorem haarFinite_ne_zero : haarFinite G ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff]
  apply ENNReal.coe_ne_zero.mp
  rw [FiniteMeasure.ennreal_mass, haarFinite_toMeasure]
  exact haar_univ_ne_zero G

noncomputable def haarProb : Measure G :=
  (haarFinite G).normalize

theorem haarProb_def :
    haarProb G = ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar :=
  by
    rw [haarProb,
      FiniteMeasure.toMeasure_normalize_eq_of_nonzero (haarFinite G) (haarFinite_ne_zero G)]
    rw [← haarFinite_toMeasure, ← FiniteMeasure.ennreal_mass, ← ENNReal.coe_inv]
    · rfl
    · exact (FiniteMeasure.mass_nonzero_iff (haarFinite G)).mpr (haarFinite_ne_zero G)

instance isProbabilityMeasure_haarProb : IsProbabilityMeasure (haarProb G) := by
  exact (haarFinite G).normalize.property

instance isMulLeftInvariant_haarProb : (haarProb G).IsMulLeftInvariant := by
  rw [haarProb_def]
  infer_instance

instance isHaarMeasure_haarProb : (haarProb G).IsHaarMeasure := by
  rw [haarProb_def]
  exact Measure.IsHaarMeasure.smul Measure.haar
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _))

instance isMulRightInvariant_haarProb : (haarProb G).IsMulRightInvariant :=
  isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) _

instance isInvInvariant_haarProb : (haarProb G).IsInvInvariant :=
  isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) _

theorem eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ = haarProb G :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end CompactGroup

end DedekindZetaZeroFree.TauCeti
