module

public import DedekindZetaZeroFree.Theta.Profiles.AmplitudeOscillatoryIntegrals
public import DedekindZetaZeroFree.Analysis.Complex.LogarithmicRadialDerivatives

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ThetaArchInducedMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPCplxRotatedRapidDecay KPCplxRotatedKernelEstimates MeasureTheory

private lemma flow_radialUnit (t ρ : ℝ) (u : ℂˣ) (hρ : 0 < ρ) :
    logarithmicRadialFlow t (radialUnit ρ u) = radialUnit (Real.exp (t / 2) * ρ) u := by
  apply Units.ext
  simp only [logarithmicRadialFlow, radialUnit, dite_eq_left hρ,
    dite_eq_left (mul_pos (Real.exp_pos _) hρ), Units.val_mk0, Complex.ofReal_mul]
  ring

private lemma induced_amplitude_logarithmic_transport (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter)
    (hf : HasInducedAmplitudeEstimates β κ f) (F : ℂˣ → ℂ)
    (hF : ∀ (u : ℂˣ) (ρ : ℝ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
      F (radialUnit ρ u) = ∫ x : ℂ,
        Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
          rotatedAmplitude β κ f u ρ x ∂euclideanArea)
    (j : ℕ) (hj : j ≤ 2) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (ρ : ℝ) (hρ : 0 < ρ) :
    ((logarithmicDerivative^[j]) F) (radialUnit ρ u) = ((2 : ℂ)⁻¹) ^ j *
      ∫ x : ℂ, Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
        amplitudeDerivative β κ f u j 0 ρ x ∂euclideanArea := by
  revert ρ
  induction j with
  | zero => intro ρ hρ; simpa [amplitudeDerivative] using hF u ρ hu hρ
  | succ j ih =>
    intro ρ hρ
    rw [Function.iterate_succ_apply', logarithmicDerivative]
    have hscale : HasDerivAt (fun t : ℝ => Real.exp (t / 2) * ρ) (ρ / 2) 0 := by
      convert (((Real.hasDerivAt_exp (0 / 2)).comp 0
        ((hasDerivAt_id (0 : ℝ)).div_const 2)).mul_const ρ) using 1 <;> simp; ring
    have hi := hasDerivAt_integral_exp_mul_amplitudeDerivative β κ f hf u hu j hj ρ hρ
    have hi' : HasDerivAt (fun r : ℝ => ∫ x : ℂ,
        Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
          amplitudeDerivative β κ f u j 0 r x ∂euclideanArea)
        ((ρ : ℂ)⁻¹ * ∫ x : ℂ,
          Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
            amplitudeDerivative β κ f u (j + 1) 0 ρ x ∂euclideanArea)
        (Real.exp (0 / 2) * ρ) := by simpa using hi
    have hd := (hi'.scomp 0 hscale).const_mul (((2 : ℂ)⁻¹) ^ j)
    have he : (fun t : ℝ =>
        (logarithmicDerivative^[j]) F (logarithmicRadialFlow t (radialUnit ρ u))) =
        fun t : ℝ => ((2 : ℂ)⁻¹) ^ j * ∫ x : ℂ,
          Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
            amplitudeDerivative β κ f u j 0 (Real.exp (t / 2) * ρ) x ∂euclideanArea := by
      funext t
      rw [flow_radialUnit t ρ u hρ, ih (by omega) _ (mul_pos (Real.exp_pos _) hρ)]
    rw [he]
    convert hd.deriv using 1
    · rfl
    · simp only [Complex.real_smul, Complex.ofReal_div,
        Complex.ofReal_ofNat, pow_succ]
      field_simp [Complex.ofReal_ne_zero.mpr hρ.ne']

lemma exists_norm_iterate_logarithmicDerivative_le (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter)
    (hf : HasInducedAmplitudeEstimates β κ f) (F : ℂˣ → ℂ)
    (hF : ∀ (u : ℂˣ) (ρ : ℝ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
      F (radialUnit ρ u) = ∫ x : ℂ,
        Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
          rotatedAmplitude β κ f u ρ x ∂euclideanArea)
    (j h : ℕ) (hj : j ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℂˣ,
      ‖((logarithmicDerivative^[j]) F) y‖ ≤ C * ‖(y : ℂ)‖ ^ ((2 / 3 : ℝ) - (h : ℝ)) := by
  obtain ⟨C, hC, hb⟩ :=
    exists_norm_integral_exp_mul_amplitudeDerivative_zero_le β κ f hf j h hj
  refine ⟨‖((2 : ℂ)⁻¹) ^ j‖ * C, mul_nonneg (norm_nonneg _) hC.le, ?_⟩
  intro y
  obtain ⟨u, hu, hy⟩ := exists_norm_eq_one_radialUnit_eq y
  have hρ : 0 < ‖(y : ℂ)‖ := norm_pos_iff.mpr y.ne_zero
  have he := induced_amplitude_logarithmic_transport β κ f hf F hF j hj u hu ‖(y : ℂ)‖ hρ
  rw [hy] at he
  rw [he, norm_mul]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hb u ‖(y : ℂ)‖ hu hρ) (norm_nonneg (((2 : ℂ)⁻¹) ^ j))

end DedekindZetaZeroFree.ThetaArchInducedMajorant

end
