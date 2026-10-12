module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Algebra.Order.Positive.Field

@[expose] public section

open MeasureTheory
namespace DedekindZetaZeroFree.NormSheetsPositiveAxis
noncomputable section

abbrev Axis := {x : ℝ // 0 < x}

instance axisContinuousMul : ContinuousMul Axis where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)

instance axisContinuousInv : ContinuousInv Axis where
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.inv₀ (fun x : Axis => ne_of_gt x.property)

instance axisTopologicalGroup : IsTopologicalGroup Axis := ⟨⟩

instance axisLocallyCompact : LocallyCompactSpace Axis :=
  (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).locallyCompactSpace

def haar : Measure Axis :=
  Measure.comap Subtype.val
    (volume.withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹))

private theorem haar_left : haar.IsMulLeftInvariant := by
  let ev : MeasurableEmbedding (Subtype.val : Axis → ℝ) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).isOpenEmbedding_subtypeVal.measurableEmbedding
  let D := fun x : ℝ => ENNReal.ofReal x⁻¹
  have hD : Measurable D := by dsimp [D]; fun_prop
  constructor
  intro g
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  change (volume.withDensity D).comap Subtype.val ((fun x => g * x) ⁻¹' s) =
    (volume.withDensity D).comap Subtype.val s
  rw [ev.comap_apply, ev.comap_apply]
  have hpre : Subtype.val '' ((fun x => g * x) ⁻¹' s) =
      (fun x : ℝ => (g : ℝ) * x) ⁻¹' (Subtype.val '' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨g * u, hu, rfl⟩
    · rintro ⟨u, hu, he⟩
      refine ⟨g⁻¹ * u, ?_, ?_⟩
      · simpa using hu
      · change (g : ℝ)⁻¹ * (u : ℝ) = x
        rw [he]
        simp [ne_of_gt g.property]
  rw [hpre, withDensity_apply _ (by exact (ev.measurableSet_image.mpr hs).preimage (by fun_prop)),
    withDensity_apply _ (ev.measurableSet_image.mpr hs)]
  have hscale := Real.map_volume_mul_left (ne_of_gt g.property)
  rw [abs_of_pos (inv_pos.mpr g.property), ENNReal.ofReal_inv_of_pos g.property] at hscale
  have hmul (x : ℝ) : D ((g : ℝ) * x) = (ENNReal.ofReal (g : ℝ))⁻¹ * D x := by
    dsimp [D]
    rw [mul_inv, ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr g.property)),
      ENNReal.ofReal_inv_of_pos g.property]
  have hm := setLIntegral_map (μ := volume) (g := fun x : ℝ => (g : ℝ) * x)
    (s := Subtype.val '' s) (ev.measurableSet_image.mpr hs) hD (by fun_prop)
  rw [hscale, Measure.restrict_smul, lintegral_smul_measure] at hm
  simp only [ENNReal.smul_def, smul_eq_mul] at hm
  simp_rw [hmul] at hm
  rw [lintegral_const_mul _ hD] at hm
  exact (ENNReal.mul_right_inj (by simp) (by simp [g.property])).mp hm.symm

theorem density_and_haar :
    Measure.map Subtype.val haar =
      (volume.withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹)).restrict (Set.Ioi 0) ∧
    haar.IsHaarMeasure := by
  refine ⟨map_comap_subtype_coe measurableSet_Ioi _, ?_⟩
  let ev : MeasurableEmbedding (Subtype.val : Axis → ℝ) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).isOpenEmbedding_subtypeVal.measurableEmbedding
  let D := fun x : ℝ => ENNReal.ofReal x⁻¹
  have hD : Measurable D := by dsimp [D]; fun_prop
  letI := haar_left
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds (1 : Axis)
  have hint : (interior K).Nonempty := ⟨1, mem_interior_iff_mem_nhds.mpr hKmem⟩
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK hint
  · change (volume.withDensity D).comap Subtype.val K ≠ 0
    rw [ev.comap_apply]
    apply mt (withDensity_apply_eq_zero (μ := volume) (s := Subtype.val '' K) hD).mp
    have heq : {x | D x ≠ 0} ∩ (Subtype.val '' K) = Subtype.val '' K := by
      apply Set.inter_eq_right.mpr
      rintro x ⟨u, hu, rfl⟩
      exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr u.property)).ne'
    rw [heq]
    have hpos : 0 < volume (Subtype.val '' interior K) :=
      ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).isOpenEmbedding_subtypeVal.isOpenMap
        _ isOpen_interior).measure_pos volume (hint.image _)
    exact (hpos.trans_le (measure_mono (Set.image_mono interior_subset))).ne'
  · change (volume.withDensity D).comap Subtype.val K ≠ ⊤
    rw [ev.comap_apply, withDensity_apply _ ((hK.image continuous_subtype_val).measurableSet)]
    have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Subtype.val '' K) := by
      apply ContinuousOn.inv₀ continuousOn_id
      rintro x ⟨u, hu, rfl⟩
      exact ne_of_gt u.property
    have hi := ContinuousOn.integrableOn_compact (μ := volume)
      (hK.image continuous_subtype_val) hc
    change (∫⁻ x in Subtype.val '' K, ENNReal.ofReal x⁻¹ ∂volume) ≠ ⊤
    rw [← ofReal_integral_eq_lintegral_ofReal hi ?_]
    · exact ENNReal.ofReal_ne_top
    · filter_upwards [ae_restrict_mem (ev.measurableSet_image.mpr hK.measurableSet)] with x hx
      rcases hx with ⟨u, hu, rfl⟩
      exact le_of_lt (inv_pos.mpr u.property)

instance haar_isHaarMeasure : haar.IsHaarMeasure := density_and_haar.2

end
end DedekindZetaZeroFree.NormSheetsPositiveAxis
