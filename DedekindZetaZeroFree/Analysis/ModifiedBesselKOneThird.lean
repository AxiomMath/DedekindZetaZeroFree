module

public import DedekindZetaZeroFree.Theta.Profiles.ThirdBesselSchlafliIntegral

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxBessel

open MeasureTheory Set

noncomputable def modifiedBesselK (ν z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-z * Real.cosh t) * Real.cosh (ν * t)

noncomputable def schlafliKernel (a z t : ℝ) : ℝ :=
  Real.rpow t a * Real.exp (-t - z ^ 2 / (4 * t))

noncomputable def besselKThird (z : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.rpow (z / 2) (-(1 / 3 : ℝ)) *
    ∫ t in Ioi (0 : ℝ), schlafliKernel (-(2 / 3 : ℝ)) z t

theorem schlafliKernel_neg_two_thirds_integrable (z : ℝ) (hz : 0 < z) :
    IntegrableOn (schlafliKernel (-(2 / 3 : ℝ)) z) (Ioi 0) := by
  have hmajor := Real.GammaIntegral_convergent (s := (1 / 3 : ℝ)) (by norm_num)
  refine hmajor.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    unfold schlafliKernel
    apply (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))).mul
    apply ContinuousOn.rexp
    apply continuousOn_id.neg.sub
    exact continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun t ht => mul_ne_zero (by norm_num) (ne_of_gt ht))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    have hp : 0 < schlafliKernel (-(2 / 3 : ℝ)) z t :=
      mul_pos (Real.rpow_pos_of_pos ht' _) (Real.exp_pos _)
    rw [Real.norm_eq_abs, abs_of_pos hp, schlafliKernel]
    change t ^ (-(2 / 3 : ℝ)) * Real.exp (-t - z ^ 2 / (4 * t)) ≤
      Real.exp (-t) * t ^ ((1 / 3 : ℝ) - 1)
    norm_num
    rw [mul_comm (Real.exp (-t))]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht'.le _)
    apply Real.exp_le_exp.mpr
    have : 0 ≤ z ^ 2 / (4 * t) := by positivity
    linarith

private lemma schlafli_exponential (z u : ℝ) (hz : 0 < z) :
    Real.exp u * schlafliKernel (-(2 / 3 : ℝ)) z ((z / 2) * Real.exp u) =
      (z / 2) ^ (-(2 / 3 : ℝ)) *
        (Real.exp (-z * Real.cosh u) * Real.exp (u / 3)) := by
  have hc : 0 < z / 2 := by linarith
  unfold schlafliKernel
  change Real.exp u * (((z / 2) * Real.exp u) ^ (-(2 / 3 : ℝ)) * _) = _
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
  have he : -(z / 2 * Real.exp u) - z ^ 2 / (4 * (z / 2 * Real.exp u)) =
      -z * Real.cosh u := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
    ring
  rw [he]
  have hp : Real.exp u * Real.exp (u * (-(2 / 3 : ℝ))) = Real.exp (u / 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination (z / 2) ^ (-(2 / 3 : ℝ)) * Real.exp (-z * Real.cosh u) * hp

theorem besselKThird_eq_modifiedBesselK (z : ℝ) (hz : 0 < z) :
    besselKThird z = modifiedBesselK (1 / 3 : ℝ) z := by
  let c : ℝ := z / 2
  let F : ℝ → ℝ := fun u => Real.exp (-z * Real.cosh u) * Real.exp (u / 3)
  let H : ℝ → ℝ := fun u => Real.exp (-z * Real.cosh u) * Real.cosh ((1 / 3 : ℝ) * u)
  have hc : 0 < c := by dsimp [c]; linarith
  have hs : IntegrableOn (fun t => schlafliKernel (-(2 / 3 : ℝ)) z (c * t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff _ 0 hc).mpr
    simpa only [mul_zero] using schlafliKernel_neg_two_thirds_integrable z hz
  have hexp := (integrable_comp_exp _).mpr hs
  have hCF : Integrable (fun u => c ^ (-(2 / 3 : ℝ)) * F u) := by
    apply hexp.congr
    exact Filter.Eventually.of_forall (fun u => by
      simpa only [smul_eq_mul, c, F] using schlafli_exponential z u hz)
  have hF : Integrable F :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos hc _).ne') F).mp hCF
  have hsum : (fun u => F u + F (-u)) = fun u => 2 * H u := by
    funext u
    dsimp [F, H]
    rw [Real.cosh_neg, Real.cosh_eq ((1 / 3 : ℝ) * u)]
    have he : (1 / 3 : ℝ) * u = u / 3 := by ring
    rw [he]
    have hn : -u / 3 = -(u / 3) := by ring
    rw [hn]
    ring
  have hIF : (∫ u, F u) = ∫ u, H u := by
    have h := integral_add hF hF.comp_neg
    rw [show (fun u => F u + F (-u)) = (fun u => 2 * H u) from hsum,
      integral_const_mul, integral_neg_eq_self F volume] at h
    linarith
  have hHabs : (fun u => H |u|) = H := by
    funext u
    dsimp [H]
    rw [Real.cosh_abs]
    have he : (1 / 3 : ℝ) * |u| = |(1 / 3 : ℝ) * u| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
    rw [he, Real.cosh_abs]
  have hIH : (∫ u, H u) = 2 * modifiedBesselK (1 / 3 : ℝ) z := by
    rw [← hHabs]
    exact integral_comp_abs
  have hI : (∫ t in Ioi (0 : ℝ), schlafliKernel (-(2 / 3 : ℝ)) z t) =
      c * (c ^ (-(2 / 3 : ℝ)) * (∫ u, F u)) := by
    have hscale := integral_comp_mul_left_Ioi (schlafliKernel (-(2 / 3 : ℝ)) z) 0 hc
    have hsub := integral_comp_exp (fun t => schlafliKernel (-(2 / 3 : ℝ)) z (c * t))
    have hp : (∫ u, Real.exp u • schlafliKernel (-(2 / 3 : ℝ)) z (c * Real.exp u)) =
        c ^ (-(2 / 3 : ℝ)) * (∫ u, F u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => by
        simpa only [smul_eq_mul, c, F] using schlafli_exponential z u hz)
    rw [hp] at hsub
    rw [← hsub] at hscale
    simp only [mul_zero, smul_eq_mul] at hscale
    rw [hscale]
    field_simp
  have hconst : c ^ (-(1 / 3 : ℝ)) * c * c ^ (-(2 / 3 : ℝ)) = 1 := by
    calc
      _ = c ^ (-(1 / 3 : ℝ)) * c ^ (1 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = 1 := by rw [← Real.rpow_add hc, ← Real.rpow_add hc]; norm_num
  unfold besselKThird
  change (1 / 2 : ℝ) * c ^ (-(1 / 3 : ℝ)) * _ = _
  rw [hI, hIF, hIH]
  linear_combination modifiedBesselK (1 / 3 : ℝ) z * hconst

theorem besselKThird_pos (z : ℝ) (hz : 0 < z) : 0 < besselKThird z := by
  unfold besselKThird
  apply mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _))
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_
    (schlafliKernel_neg_two_thirds_integrable z hz)).2 ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_nonneg _)
  · have hsupp : Function.support (schlafliKernel (-(2 / 3 : ℝ)) z) ∩ Ioi 0 = Ioi 0 := by
      rw [Set.inter_eq_right]
      intro t ht
      exact (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)).ne'
    rw [hsupp, Real.volume_Ioi]
    exact ENNReal.zero_lt_top

end DedekindZetaZeroFree.KPCplxBessel
