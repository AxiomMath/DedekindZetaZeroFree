module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

theorem exists_full_tube_l2_transfer_constant_ae {E V X : Type*}
    [MeasurableSpace E] [MeasurableSpace V] [MeasurableSpace X]
    (μ : Measure E) (ν : Measure V) (m : Measure X) [SFinite μ] [IsFiniteMeasure ν]
    (tube : E × V → X) (htube : AEMeasurable tube (μ.prod ν))
    {a : ℝ≥0∞} (ha : a ≠ ∞) (hdom : Measure.map tube (μ.prod ν) ≤ a • m)
    (hν : ν Set.univ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : X → ℂ), MemLp f 2 m →
      ∀ (g : E → ℂ), (f ∘ tube =ᵐ[μ.prod ν] fun p => g p.1) →
        MemLp g 2 μ ∧ lpNorm g 2 μ ≤ C * lpNorm f 2 m := by
  let w := ν Set.univ
  let b := (w⁻¹ * a) ^ (1 / (2 : ℝ≥0∞)).toReal
  have hwT : w ≠ ∞ := measure_ne_top _ _
  have hw : w ≠ 0 := hν
  have hb : b ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hν) ha)
  refine ⟨b.toReal + 1, by positivity, ?_⟩
  intro f hf g hinv
  have hfm := hf.of_measure_le_smul ha hdom
  have hfp := (hfm.comp_of_map htube).ae_eq hinv
  have hν' : ν ≠ 0 := by intro h; exact hν (by simp [h])
  have hga := hfp.aestronglyMeasurable.of_comp_fst hν'
  have hgm : MemLp g 2 (w • μ) := by
    rw [← Measure.map_fst_prod]
    apply (memLp_map_measure_iff (by
      simpa only [Measure.map_fst_prod] using hga.smul_measure w)
      measurable_fst.aemeasurable).mpr
    exact hfp
  have hg : MemLp g 2 μ := by
    have hh := hgm.smul_measure (c := w⁻¹) (ENNReal.inv_ne_top.mpr hν)
    simpa only [smul_smul, ENNReal.inv_mul_cancel hw hwT, one_smul] using hh
  refine ⟨hg, ?_⟩
  have hmap : eLpNorm f 2 (Measure.map tube (μ.prod ν)) =
      eLpNorm (fun p : E × V => g p.1) 2 (μ.prod ν) :=
    (eLpNorm_map_measure hfm.aestronglyMeasurable htube).trans (eLpNorm_congr_ae hinv)
  have hfst : eLpNorm (fun p : E × V => g p.1) 2 (μ.prod ν) = eLpNorm g 2 (w • μ) := by
    have ham : AEStronglyMeasurable g (Measure.map Prod.fst (μ.prod ν)) := by
      simpa only [Measure.map_fst_prod] using hga.smul_measure w
    exact (eLpNorm_map_measure ham measurable_fst.aemeasurable).symm.trans
      (by rw [Measure.map_fst_prod])
  have hscale : μ = w⁻¹ • (w • μ) := by
    rw [smul_smul, ENNReal.inv_mul_cancel hw hwT, one_smul]
  have he : eLpNorm g 2 μ ≤ b * eLpNorm f 2 m := by
    calc
      eLpNorm g 2 μ = w⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm g 2 (w • μ) := by
        conv_lhs => rw [hscale]
        rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
        rfl
      _ ≤ w⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal *
          (a ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm f 2 m) := by
        apply mul_le_mul_right
        rw [← hfst, ← hmap]
        exact eLpNorm_le_of_measure_le_smul hdom
      _ = b * eLpNorm f 2 m := by rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hb hf.eLpNorm_ne_top) he
  calc
    lpNorm g 2 μ ≤ b.toReal * lpNorm f 2 m := by simpa only [lpNorm, ENNReal.toReal_mul] using ht
    _ ≤ (b.toReal + 1) * lpNorm f 2 m := mul_le_mul_of_nonneg_right (by linarith) lpNorm_nonneg

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
