module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.SourceDerivativePositiveStripBounds

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped NumberField Classical ContDiff Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem mellin_deriv_eq_neg_mul (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (s : ℂ) (hs : 0 < s.re) :
    mellin (deriv h) (s + 1) = -s * mellin h s := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hsne : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]; linarith
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x :=
    fun x hx => hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hsne
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h x) x :=
    fun x _ => (hh1.differentiable_one x).hasDerivAt
  have huv' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * deriv h x) (Ioi 0) := by
    have h := mellinConvergent_iteratedDeriv_of_pos hh hc 1 hs1
    simpa [MellinConvergent, iteratedDeriv_one, smul_eq_mul, add_sub_cancel_right] using h
  have hu'v : IntegrableOn (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * h x) (Ioi 0) := by
    have h0 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * h x) (Ioi 0) := by
      have h := mellinConvergent_iteratedDeriv_of_pos hh hc 0 hs
      simpa [MellinConvergent, iteratedDeriv_zero, smul_eq_mul] using h
    have h1 : Integrable (fun x : ℝ => s * ((x : ℂ) ^ (s - 1) * h x))
        (volume.restrict (Ioi 0)) := h0.const_mul s
    simpa only [mul_assoc, IntegrableOn] using h1
  have hzero : Tendsto (fun x : ℝ => (x : ℂ) ^ s * h x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (x : ℂ) ^ s) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      have h := (Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).tendsto
      simp only [Complex.ofReal_zero] at h
      rw [Complex.zero_cpow hsne] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0)) :=
      hh1.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h1.mul h2
  have hinfty : Tendsto (fun x : ℝ => (x : ℂ) ^ s * h x) atTop (𝓝 0) := by
    have hev : h =ᶠ[atTop] (0 : ℝ → ℂ) := by
      rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hc
      exact hc.filter_mono atTop_le_cocompact
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with x hx
    simp [hx]
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ))
    (u := fun x : ℝ => (x : ℂ) ^ s) (u' := fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    (v := h) (v' := deriv h) (a' := 0) (b' := 0)
    hu hv huv' hu'v hzero hinfty
  simp only [mellin]
  rw [show ((s + 1) - 1) = s by ring]
  simp only [smul_eq_mul]
  rw [key]
  have key2 : (∫ x : ℝ in Ioi (0 : ℝ), (s * (x : ℂ) ^ (s - 1)) * h x)
      = s * ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * h x := by
    simp only [mul_assoc]
    rw [integral_const_mul]
  rw [key2]
  ring

theorem integral_Ioi_deriv_eq_neg_at_zero (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    (∫ x : ℝ in Set.Ioi 0, deriv h x) = -h 0 := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  exact hc.integral_Ioi_deriv_eq hh1 0

end DedekindZetaZeroFree.LargeSieve.Vendor

end
