module

public import DedekindZetaZeroFree.Geometry.HyperbolicActionMetricAndVolume

@[expose] public section

namespace DedekindZetaZeroFree.KPRadialCoercivity

open MeasureTheory Filter
open scoped ContDiff

noncomputable section

def density (d t : ℝ) : ℝ := Real.exp (-2 * d * t)

def weightedMass (d : ℝ) (v : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, density d t * ‖v t‖ ^ 2

def mass (w : ℝ → ℂ) : ℝ := ∫ t : ℝ, ‖w t‖ ^ 2

def conjugate (d : ℝ) (v : ℝ → ℂ) (t : ℝ) : ℂ :=
  Real.exp (-d * t) • v t

def undoConjugation (d : ℝ) (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  Real.exp (d * t) • w t

def weightedEnergy (d : ℝ) (a e : ℝ → ℝ) (v : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, density d t *
    (d⁻¹ * ‖deriv v t‖ ^ 2 + (a t - e t) * ‖v t‖ ^ 2)

def conjugatedEnergy (d : ℝ) (a e : ℝ → ℝ) (w : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, d⁻¹ * ‖deriv w t‖ ^ 2 + (d + a t - e t) * ‖w t‖ ^ 2

private lemma density_mul_exp_sq (d t : ℝ) :
    density d t * (Real.exp (d * t)) ^ 2 = 1 := by
  have hc2 : (Real.exp (d * t)) ^ 2 = Real.exp (2 * (d * t)) := by
    rw [sq, ← Real.exp_add]
    rw [show d * t + d * t = 2 * (d * t) by ring]
  rw [density, hc2, ← Real.exp_add]
  rw [show -2 * d * t + 2 * (d * t) = 0 by ring, Real.exp_zero]

private lemma deriv_undoConjugation (d : ℝ) (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w) (t : ℝ) :
    deriv (undoConjugation d w) t = Real.exp (d * t) • (d • w t + deriv w t) := by
  have hlin : HasDerivAt (fun s : ℝ => Real.exp (d * s)) (Real.exp (d * t) * d) t :=
    (Real.hasDerivAt_exp (d * t)).comp t (hasDerivAt_const_mul (x := t) d)
  have hw' : HasDerivAt w (deriv w t) t := (hw.differentiable (by simp) t).hasDerivAt
  have hsmul := hlin.smul hw'
  change deriv ((fun s : ℝ => Real.exp (d * s)) • w) t =
    Real.exp (d * t) • (d • w t + deriv w t)
  rw [hsmul.deriv, smul_add, smul_smul, add_comm]

private lemma integrand_identity (d : ℝ) (hd : d ≠ 0) (a e : ℝ → ℝ)
    (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w) (t : ℝ) :
    density d t *
        (d⁻¹ * ‖deriv (undoConjugation d w) t‖ ^ 2 +
          (a t - e t) * ‖undoConjugation d w t‖ ^ 2) =
      (d⁻¹ * ‖deriv w t‖ ^ 2 + (d + a t - e t) * ‖w t‖ ^ 2) +
        2 * inner ℝ (w t) (deriv w t) := by
  have hderiv := deriv_undoConjugation d w hw t
  have hcpos : 0 < Real.exp (d * t) := Real.exp_pos _
  have hnorm1 : ‖deriv (undoConjugation d w) t‖ ^ 2 =
      (Real.exp (d * t)) ^ 2 * ‖d • w t + deriv w t‖ ^ 2 := by
    rw [hderiv, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    ring
  have hnorm2 : ‖undoConjugation d w t‖ ^ 2 = (Real.exp (d * t)) ^ 2 * ‖w t‖ ^ 2 := by
    rw [undoConjugation, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    ring
  have hinner : ‖d • w t + deriv w t‖ ^ 2 =
      ‖deriv w t‖ ^ 2 + 2 * d * inner ℝ (w t) (deriv w t) + d ^ 2 * ‖w t‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [hnorm1, hnorm2, hinner]
  calc density d t *
        (d⁻¹ * ((Real.exp (d * t)) ^ 2 *
              (‖deriv w t‖ ^ 2 + 2 * d * inner ℝ (w t) (deriv w t) + d ^ 2 * ‖w t‖ ^ 2)) +
          (a t - e t) * ((Real.exp (d * t)) ^ 2 * ‖w t‖ ^ 2))
      = (density d t * (Real.exp (d * t)) ^ 2) *
          (d⁻¹ * (‖deriv w t‖ ^ 2 + 2 * d * inner ℝ (w t) (deriv w t) +
              d ^ 2 * ‖w t‖ ^ 2) + (a t - e t) * ‖w t‖ ^ 2) := by ring
    _ = d⁻¹ * (‖deriv w t‖ ^ 2 + 2 * d * inner ℝ (w t) (deriv w t) + d ^ 2 * ‖w t‖ ^ 2) +
          (a t - e t) * ‖w t‖ ^ 2 := by rw [density_mul_exp_sq, one_mul]
    _ = (d⁻¹ * ‖deriv w t‖ ^ 2 + (d + a t - e t) * ‖w t‖ ^ 2) +
          2 * inner ℝ (w t) (deriv w t) := by
        field_simp
        try ring

private lemma hasCompactSupport_mul_norm_sq (c : ℝ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) : HasCompactSupport (fun t => c * ‖w t‖ ^ 2) := by
  refine hc.mono' (fun x hx => ?_)
  rw [Function.mem_support] at hx
  exact subset_tsupport w (Function.mem_support.mpr (fun hv0 => hx (by simp [hv0])))

private lemma integral_inner_deriv_eq_zero (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport w) :
    ∫ t, 2 * inner ℝ (w t) (deriv w t) = 0 := by
  have hderiv : ∀ t, HasDerivAt (fun s => ‖w s‖ ^ 2)
      (2 * inner ℝ (w t) (deriv w t)) t := by
    intro t
    have h1 : HasDerivAt w (deriv w t) t := (hw.differentiable (by simp) t).hasDerivAt
    simpa using h1.norm_sq
  have hcont' : Continuous (fun t => 2 * inner ℝ (w t) (deriv w t)) :=
    continuous_const.mul (hw.continuous.inner (hw.continuous_deriv (by simp)))
  have hc' : HasCompactSupport (fun t => 2 * inner ℝ (w t) (deriv w t)) := by
    refine hc.mono' (fun x hx => ?_)
    rw [Function.mem_support] at hx
    exact subset_tsupport w (Function.mem_support.mpr (fun hv0 => hx (by simp [hv0])))
  have hcont_mass : Continuous (fun t => ‖w t‖ ^ 2) := hw.continuous.norm.pow 2
  have hc_mass : HasCompactSupport (fun t => ‖w t‖ ^ 2) := by
    simpa using hasCompactSupport_mul_norm_sq 1 w hc
  exact integral_eq_zero_of_hasDerivAt_of_integrable hderiv
    (hcont'.integrable_of_hasCompactSupport hc')
    (hcont_mass.integrable_of_hasCompactSupport hc_mass)

private lemma integrable_conj_integrand (d : ℝ) (a e : ℝ → ℝ) (ha : Continuous a)
    (he : Continuous e) (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) :
    Integrable (fun t => d⁻¹ * ‖deriv w t‖ ^ 2 + (d + a t - e t) * ‖w t‖ ^ 2) := by
  have hcont : Continuous
      (fun t => d⁻¹ * ‖deriv w t‖ ^ 2 + (d + a t - e t) * ‖w t‖ ^ 2) :=
    (continuous_const.mul (((hw.continuous_deriv (by simp)).norm).pow 2)).add
      (((continuous_const.add ha).sub he).mul (hw.continuous.norm.pow 2))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine hc.mono' (fun x hx => ?_)
  by_contra hx'
  rw [Function.mem_support] at hx
  exact hx (by simp [deriv_of_notMem_tsupport hx', image_eq_zero_of_notMem_tsupport hx'])

private lemma integrable_inner_deriv (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport w) :
    Integrable (fun t => 2 * inner ℝ (w t) (deriv w t)) := by
  have hcont : Continuous (fun t => 2 * inner ℝ (w t) (deriv w t)) :=
    continuous_const.mul (hw.continuous.inner (hw.continuous_deriv (by simp)))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine hc.mono' (fun x hx => ?_)
  rw [Function.mem_support] at hx
  exact subset_tsupport w (Function.mem_support.mpr (fun hv0 => hx (by simp [hv0])))

theorem scalar_conjugation_identity (d : ℝ) (hd : 0 < d)
    (a e : ℝ → ℝ) (ha : Continuous a) (he : Continuous e)
    (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) :
    weightedMass d (undoConjugation d w) = mass w ∧
      weightedEnergy d a e (undoConjugation d w) =
        conjugatedEnergy d a e w := by
  have hdne : d ≠ 0 := hd.ne'
  refine ⟨?_, ?_⟩
  · rw [weightedMass, mass]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show density d t * ‖undoConjugation d w t‖ ^ 2 = ‖w t‖ ^ 2
    have hnorm2 : ‖undoConjugation d w t‖ ^ 2 =
        (Real.exp (d * t)) ^ 2 * ‖w t‖ ^ 2 := by
      rw [undoConjugation, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      ring
    rw [hnorm2, ← mul_assoc, density_mul_exp_sq, one_mul]
  · rw [weightedEnergy, conjugatedEnergy]
    rw [show (∫ t, density d t *
          (d⁻¹ * ‖deriv (undoConjugation d w) t‖ ^ 2 +
            (a t - e t) * ‖undoConjugation d w t‖ ^ 2)) =
        ∫ t, ((d⁻¹ * ‖deriv w t‖ ^ 2 + (d + a t - e t) * ‖w t‖ ^ 2) +
          2 * inner ℝ (w t) (deriv w t)) from
      integral_congr_ae (Eventually.of_forall fun t => integrand_identity d hdne a e w hw t)]
    rw [integral_add (integrable_conj_integrand d a e ha he w hw hc)
      (integrable_inner_deriv w hw hc), integral_inner_deriv_eq_zero w hw hc, add_zero]

private lemma conj_energy_lower_bound (d : ℝ) (hd : 0 < d) (a : ℝ → ℝ)
    (ha : Continuous a) (hapos : ∀ t : ℝ, 0 ≤ a t)
    (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) :
    d * mass w ≤ conjugatedEnergy d a (fun _ => 0) w := by
  rw [conjugatedEnergy, mass, ← integral_const_mul]
  refine integral_mono
    ((continuous_const.mul (hw.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_norm_sq d w hc))
    (integrable_conj_integrand d a (fun _ => 0) ha continuous_const w hw hc)
    (fun t => ?_)
  simp only [Pi.zero_apply, sub_zero]
  nlinarith [hapos t, sq_nonneg (‖w t‖), norm_nonneg (deriv w t), inv_pos.mpr hd]

theorem scalar_zero_mode_lower_bound (d : ℝ) (hd : 0 < d)
    (a : ℝ → ℝ) (ha : Continuous a) (hapos : ∀ t : ℝ, 0 ≤ a t)
    (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) :
    d * weightedMass d v ≤ weightedEnergy d a (fun _ => 0) v := by
  have hfun : conjugate d v = fun t : ℝ => Real.exp (-d * t) • v t := rfl
  have hw_smooth : ContDiff ℝ ∞ (conjugate d v) := by
    rw [hfun]
    exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).smul hv
  have hw_compact : HasCompactSupport (conjugate d v) := by
    rw [hfun]
    refine hc.mono' (fun x hx => ?_)
    rw [Function.mem_support] at hx
    exact subset_tsupport v (Function.mem_support.mpr (fun hv0 => hx (by simp [hv0])))
  have hveq : ∀ t : ℝ, undoConjugation d (conjugate d v) t = v t := by
    intro t
    have hthis : undoConjugation d (conjugate d v) t =
        Real.exp (d * t) • (Real.exp (-d * t) • v t) := rfl
    rw [hthis, smul_smul, ← Real.exp_add]
    rw [show d * t + -d * t = 0 by ring, Real.exp_zero, one_smul]
  obtain ⟨h1, h2⟩ := scalar_conjugation_identity d hd a (fun _ => 0) ha
    continuous_const (conjugate d v) hw_smooth hw_compact
  have hveq_fun : undoConjugation d (conjugate d v) = v := funext hveq
  have hmass : weightedMass d v = mass (conjugate d v) := by
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show density d t * ‖v t‖ ^ 2 = density d t * ‖undoConjugation d (conjugate d v) t‖ ^ 2
    rw [hveq_fun]
  have henergy : weightedEnergy d a (fun _ => 0) v =
      conjugatedEnergy d a (fun _ => 0) (conjugate d v) := by
    rw [← h2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show density d t * (d⁻¹ * ‖deriv v t‖ ^ 2 + (a t - (fun _ => 0) t) * ‖v t‖ ^ 2) =
      density d t * (d⁻¹ * ‖deriv (undoConjugation d (conjugate d v)) t‖ ^ 2 +
        (a t - (fun _ => 0) t) * ‖undoConjugation d (conjugate d v) t‖ ^ 2)
    rw [hveq_fun]
  rw [hmass, henergy]
  exact conj_energy_lower_bound d hd a ha hapos (conjugate d v) hw_smooth hw_compact

end
end DedekindZetaZeroFree.KPRadialCoercivity
