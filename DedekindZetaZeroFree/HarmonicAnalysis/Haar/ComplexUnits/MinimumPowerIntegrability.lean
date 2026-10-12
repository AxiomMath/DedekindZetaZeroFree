module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LocalUnitsTensorIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.SheetPowerMinIntegrability
noncomputable section
open MeasureTheory Set

private lemma scalar_integrable (a b : ℝ) (ha : 0 < a) (hb : b < 0) :
    IntegrableOn (fun r : ℝ => min (r ^ (a-1)) (r ^ (b-1))) (Ioi 0) := by
  have hm : Measurable (fun r : ℝ => min (r ^ (a-1)) (r ^ (b-1))) := by fun_prop
  have hn : IntegrableOn (fun r : ℝ => min (r ^ (a-1)) (r ^ (b-1))) (Ioc 0 1) := by
    have hi : IntegrableOn (fun r : ℝ => r ^ (a-1)) (Ioo 0 1) := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)]
      linarith
    have hi' : IntegrableOn (fun r : ℝ => r ^ (a-1)) (Ioc 0 1) :=
      hi.congr_set_ae Ioo_ae_eq_Ioc.symm
    apply hi'.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg hr.1.le _) (Real.rpow_nonneg hr.1.le _))]
    exact min_le_left _ _
  have hf : IntegrableOn (fun r : ℝ => min (r ^ (a-1)) (r ^ (b-1))) (Ioi 1) := by
    have hi := integrableOn_Ioi_rpow_of_lt (a := b-1) (c := 1) (by linarith) (by norm_num)
    apply hi.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := le_trans (by norm_num) hr.le
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.rpow_nonneg hr0 _) (Real.rpow_nonneg hr0 _))]
    exact min_le_right _ _
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)] using hn.union hf

private lemma complex_integrable (a b : ℝ) (ha : 0 < a) (hb : b < 0) :
    Integrable (fun z : ℂ => min (‖z‖ ^ a) (‖z‖ ^ b))
      (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Real.pi*‖z‖^2)⁻¹))) := by
  have hd : Measurable (fun z : ℂ => ENNReal.ofReal ((Real.pi*‖z‖^2)⁻¹)) := by fun_prop
  rw [integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have hi : Integrable (fun z : ℂ => min (‖z‖ ^ (a-2)) (‖z‖ ^ (b-2))) volume := by
    apply (integrable_fun_norm_addHaar (E := ℂ)
      (f := fun r : ℝ => min (r ^ (a-2)) (r ^ (b-2))) volume).mpr
    apply (scalar_integrable a b ha hb).congr_fun _ measurableSet_Ioi
    intro r hr
    simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
    rw [mul_min_of_nonneg _ _ (le_of_lt hr)]
    congr 1
    · conv_rhs => lhs; rw [← Real.rpow_one r]
      rw [← Real.rpow_add hr]
      congr 1
      ring
    · conv_rhs => lhs; rw [← Real.rpow_one r]
      rw [← Real.rpow_add hr]
      congr 1
      ring
  apply (hi.const_mul Real.pi⁻¹).congr
  filter_upwards [(volume : Measure ℂ).ae_ne 0] with z hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hp (c : ℝ) : ‖z‖ ^ (c-2) = (‖z‖^2)⁻¹ * ‖z‖^c := by
    rw [Real.rpow_sub hz0, Real.rpow_two]
    exact div_eq_inv_mul _ _
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  rw [hp a, hp b, ← mul_min_of_nonneg _ _ (by positivity), mul_inv_rev]
  ring

theorem complex_units_min_powers_integrable (a b : ℝ) (ha : 0 < a) (hb : b < 0)
    (ν : Measure ℂˣ) [ν.IsHaarMeasure] :
    Integrable (fun z : ℂˣ => min (‖z.val‖ ^ a) (‖z.val‖ ^ b)) ν := by
  letI : BorelSpace ℂˣ := ⟨by
    change (borel ℂ).comap Units.val = borel _
    rw [← borel_comap, ← Units.isOpenEmbedding_val.isEmbedding.isInducing.eq_induced]⟩
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  let μ₀ : Measure ℂˣ := Measure.comap Units.val
    (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Real.pi*‖z‖^2)⁻¹)))
  letI : μ₀.IsHaarMeasure := ProbeSheetFourierMellinBounds.complexUnits_density_isHaarMeasure volume
  have hi : Integrable (fun z : ℂˣ => min (‖z.val‖ ^ a) (‖z.val‖ ^ b)) μ₀ :=
    IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding.integrableOn_range_iff_comap.mp
      (complex_integrable a b ha hb).integrableOn
  rw [Measure.isMulLeftInvariant_eq_smul ν μ₀]
  exact hi.smul_measure ENNReal.coe_ne_top

end
end DedekindZetaZeroFree.SheetPowerMinIntegrability
