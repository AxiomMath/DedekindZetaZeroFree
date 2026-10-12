module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.MellinSpectrumRecovery

@[expose] public section

noncomputable section
open scoped Classical ContDiff Topology
open Asymptotics

namespace DedekindZetaZeroFree.LargeSieve

private theorem mellinConvergent_of_contDiff_hasCompactSupport {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent h s := by
  have hfc : MeasureTheory.LocallyIntegrableOn h (Set.Ioi 0) MeasureTheory.volume :=
    hh.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htop : h =O[Filter.atTop] (fun t : ℝ => t ^ (-(s.re + 1))) := by
    have hz : h =ᶠ[Filter.atTop] (0 : ℝ → ℂ) := by
      rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hhc
      exact hhc.filter_mono atTop_le_cocompact
    exact hz.trans_isBigO (isBigO_zero _ _)
  have hbot : h =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    have h1 : h =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
      isBigO_const_of_tendsto
        (hh.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) one_ne_zero
    simpa [Real.rpow_zero] using h1
  exact mellinConvergent_of_isBigO_rpow hfc htop (by linarith) hbot hs

private theorem mellinConvergent_comp_sq {f : ℝ → ℂ} (hf : MellinConvergent f (1 / 2)) :
    MellinConvergent (fun t : ℝ => f (t ^ 2)) 1 := by
  have h2 := (MellinConvergent.comp_rpow (f := f) (s := 1) (a := 2) (by norm_num)).mpr
    (by simpa using hf)
  simpa [MellinConvergent, Complex.cpow_zero, sub_self, one_smul, Real.rpow_ofNat] using h2

private lemma Gammaℂ_half_ne_zero : Complex.Gammaℂ (1 / 2 : ℂ) ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos ?_)
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · norm_num

private lemma Gammaℂ_half_pow_mul_inv_pow_mul_div (r : ℕ) (hr : 1 ≤ r) (m : ℂ) :
    Complex.Gammaℂ (1 / 2 : ℂ) ^ r * ((Complex.Gammaℂ (1 / 2 : ℂ))⁻¹) ^ (r - 1) *
        (m / Complex.Gammaℂ (1 / 2 : ℂ)) = m := by
  have hg := Gammaℂ_half_ne_zero
  have hstep : ((Complex.Gammaℂ (1 / 2 : ℂ))⁻¹) ^ (r - 1) *
        (Complex.Gammaℂ (1 / 2 : ℂ))⁻¹ = ((Complex.Gammaℂ (1 / 2 : ℂ))⁻¹) ^ r := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  calc Complex.Gammaℂ (1 / 2 : ℂ) ^ r * ((Complex.Gammaℂ (1 / 2 : ℂ))⁻¹) ^ (r - 1) *
        (m / Complex.Gammaℂ (1 / 2 : ℂ))
      = Complex.Gammaℂ (1 / 2 : ℂ) ^ r *
          (((Complex.Gammaℂ (1 / 2 : ℂ))⁻¹) ^ (r - 1) *
            (Complex.Gammaℂ (1 / 2 : ℂ))⁻¹) * m := by
        rw [div_eq_mul_inv]; ring
    _ = Complex.Gammaℂ (1 / 2 : ℂ) ^ r * ((Complex.Gammaℂ (1 / 2 : ℂ))⁻¹) ^ r * m := by
        rw [hstep]
    _ = (Complex.Gammaℂ (1 / 2 : ℂ) * (Complex.Gammaℂ (1 / 2 : ℂ))⁻¹) ^ r * m := by
        rw [← mul_pow]
    _ = m := by rw [mul_inv_cancel₀ hg, one_pow, one_mul]

theorem B_half_eq_mellin (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    B D r h (1 / 2 : ℂ) = mellin h (1 / 2 : ℂ) := by
  have hq := Vendor.originMellinQ_eq_mellin_div_Gammaℂ h hh hhc (1 / 2 : ℂ) (by norm_num)
  rw [B, show (1 / 2 : ℂ) - 1 / 2 = 0 by norm_num, Complex.cpow_zero, one_mul,
    show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hq]
  exact Gammaℂ_half_pow_mul_inv_pow_mul_div r hr _

theorem compact_comp_sq_integrableOn (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
    MeasureTheory.IntegrableOn (fun x : ℝ => h (x ^ 2))
      (Set.Ioi 0) MeasureTheory.volume := by
  have hm := mellinConvergent_of_contDiff_hasCompactSupport hh hhc (by norm_num : (0:ℝ) < (1 / 2 : ℂ).re)
  have h2 := mellinConvergent_comp_sq hm
  simpa [MellinConvergent, Complex.cpow_zero, sub_self, one_smul] using h2

end DedekindZetaZeroFree.LargeSieve

end
