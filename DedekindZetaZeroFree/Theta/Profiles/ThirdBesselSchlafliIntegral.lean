module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

open MeasureTheory Asymptotics Filter

noncomputable section

def thirdBesselSchlafliIntegrand (z u : ℝ) : ℝ :=
  Real.exp (-z * Real.cosh u) * Real.cosh (u / 3)

def KThird (z : ℝ) : ℝ :=
  if 0 < z then ∫ u in Set.Ioi (0 : ℝ), thirdBesselSchlafliIntegrand z u else 0

private lemma thirdBesselSchlafliIntegrand_le (z : ℝ) (hz : 0 < z) (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-z * Real.cosh u) * Real.cosh (u / 3)
      ≤ (Real.exp (-1) / (z / 2)) * Real.exp (-(2 / 3) * u) := by
  have hcosh_ge : (z / 2) * Real.exp u ≤ z * Real.cosh u := by
    have h2 : Real.exp u ≤ 2 * Real.cosh u := by
      rw [Real.cosh_eq]
      linarith [Real.exp_nonneg (-u)]
    nlinarith [hz]
  have hstep1 : Real.exp (-z * Real.cosh u) ≤ Real.exp (-((z / 2) * Real.exp u)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hstep2 : Real.cosh (u / 3) ≤ Real.exp (u / 3) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(u / 3)) ≤ Real.exp (u / 3) := by
      apply Real.exp_le_exp.mpr
      linarith
    linarith
  have hmul : Real.exp (-z * Real.cosh u) * Real.cosh (u / 3)
      ≤ Real.exp (-((z / 2) * Real.exp u)) * Real.exp (u / 3) :=
    mul_le_mul hstep1 hstep2 (Real.cosh_pos _).le (Real.exp_nonneg _)
  have hkey : Real.exp (-((z / 2) * Real.exp u)) * Real.exp (u / 3)
      ≤ (Real.exp (-1) / (z / 2)) * Real.exp (-(2 / 3) * u) := by
    have hypos : 0 < (z / 2) * Real.exp u := by positivity
    have hb := Real.mul_exp_neg_le_exp_neg_one ((z / 2) * Real.exp u)
    have hdiv : Real.exp (-((z / 2) * Real.exp u))
        ≤ Real.exp (-1) / ((z / 2) * Real.exp u) := by
      rw [le_div_iff₀ hypos]
      simpa [mul_comm] using hb
    have h2 : Real.exp (-((z / 2) * Real.exp u)) * Real.exp (u / 3)
        ≤ (Real.exp (-1) / ((z / 2) * Real.exp u)) * Real.exp (u / 3) := by
      gcongr
    refine h2.trans (le_of_eq ?_)
    field_simp
    rw [← Real.exp_add]
    congr 1
    ring
  exact hmul.trans hkey

theorem thirdBesselSchlafliIntegrand_integrable (z : ℝ) (hz : 0 < z) :
    IntegrableOn (thirdBesselSchlafliIntegrand z) (Set.Ioi (0 : ℝ)) := by
  refine integrable_of_isBigO_exp_neg (a := 0) (b := 2 / 3) (by norm_num) ?_ ?_
  · apply Continuous.continuousOn
    unfold thirdBesselSchlafliIntegrand
    fun_prop
  · refine IsBigO.of_bound (Real.exp (-1) / (z / 2)) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    have h := thirdBesselSchlafliIntegrand_le z hz u hu
    have hFnn : 0 ≤ thirdBesselSchlafliIntegrand z u := by
      unfold thirdBesselSchlafliIntegrand; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [thirdBesselSchlafliIntegrand] using h

theorem KThird_eq_integral (z : ℝ) (hz : 0 < z) :
    KThird z = ∫ u in Set.Ioi (0 : ℝ), thirdBesselSchlafliIntegrand z u := by
  simp [KThird, hz]

theorem KThird_pos (z : ℝ) (hz : 0 < z) : 0 < KThird z := by
  rw [KThird_eq_integral z hz]
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_
    (thirdBesselSchlafliIntegrand_integrable z hz)).2 ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u _
    exact mul_nonneg (Real.exp_nonneg _) (Real.cosh_pos _).le
  · have hsupp : Function.support (thirdBesselSchlafliIntegrand z) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      rw [Set.inter_eq_right]
      intro u _
      simp only [Function.mem_support, ne_eq]
      exact mul_ne_zero (Real.exp_ne_zero _) (Real.cosh_pos _).ne'
    rw [hsupp, Real.volume_Ioi]
    exact ENNReal.zero_lt_top

theorem KThird_continuousOn : ContinuousOn KThird (Set.Ioi (0 : ℝ)) := by
  rw [isOpen_Ioi.continuousOn_iff]
  intro z₀ hz₀
  have hz₀' : 0 < z₀ := hz₀
  have hmain : ContinuousAt
      (fun z => ∫ u, thirdBesselSchlafliIntegrand z u
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) z₀ := by
    refine continuousAt_of_dominated
      (bound := fun u => (Real.exp (-1) / (z₀ / 4)) * Real.exp (-(2 / 3) * u)) ?_ ?_ ?_ ?_
    · filter_upwards with z
      apply Continuous.aestronglyMeasurable
      unfold thirdBesselSchlafliIntegrand
      fun_prop
    · filter_upwards [eventually_gt_nhds (show z₀ / 2 < z₀ by linarith)] with z hz
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have h := thirdBesselSchlafliIntegrand_le z (by linarith) u hu.le
      have hFnn : 0 ≤ thirdBesselSchlafliIntegrand z u := by
        unfold thirdBesselSchlafliIntegrand; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
      refine h.trans ?_
      have hz2 : z₀ / 4 ≤ z / 2 := by linarith
      have hle : Real.exp (-1) / (z / 2) ≤ Real.exp (-1) / (z₀ / 4) :=
        div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hz2
      exact mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    · exact (exp_neg_integrableOn_Ioi 0 (show (0 : ℝ) < 2 / 3 by norm_num)).const_mul
        (Real.exp (-1) / (z₀ / 4))
    · filter_upwards with u
      unfold thirdBesselSchlafliIntegrand
      fun_prop
  exact hmain.congr
    (eventually_of_mem (Ioi_mem_nhds hz₀') (fun z hz => (KThird_eq_integral z hz).symm))

end

end DedekindZetaZeroFree
