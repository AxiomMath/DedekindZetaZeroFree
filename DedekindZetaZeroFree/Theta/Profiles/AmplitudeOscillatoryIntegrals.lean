module

public import DedekindZetaZeroFree.Theta.Profiles.AmplitudeIntegralBounds

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ThetaArchInducedMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxRotatedKernelEstimates
open MeasureTheory

private lemma amplitude_diff (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (_hf : HasInducedAmplitudeEstimates β κ f) (u : ℂˣ) (_hu : ‖(u : ℂ)‖ = 1)
    (j h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    Differentiable ℝ (amplitudeDerivative β κ f u j h ρ) := by
  intro x
  exact ((amplitudeDerivative_contDiffAt β κ f u j h (ρ, x) hρ).differentiableAt
    (by simp)).comp x (by fun_prop)

private lemma amplitude_next (β κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (hf : HasInducedAmplitudeEstimates β κ f) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (j h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) :
    amplitudeDerivative β κ f u j (h + 1) ρ x =
      fderiv ℝ (amplitudeDerivative β κ f u j h ρ) x 1 := by
  have hh : HasDerivAt (fun t : ℝ => (⟨t, x.im⟩ : ℂ)) 1 x.re := by
    convert (Complex.ofRealCLM.hasDerivAt (x := x.re)).add_const
      ((x.im : ℂ) * Complex.I) using 1
    · funext t
      apply Complex.ext <;> simp
    · simp
  have hd := ((amplitude_diff β κ f hf u hu j h ρ hρ x).hasFDerivAt.comp_hasDerivAt
    x.re hh).deriv
  simpa [amplitudeDerivative, Function.iterate_succ_apply', horizontalRealDerivative,
    Function.comp_def] using hd

private lemma phase_hasDerivAt (c : ℝ) (x : ℂ) :
    HasDerivAt
      (fun t : ℝ => Complex.exp (-Complex.I * ((c * (x + (t : ℂ)).re : ℝ) : ℂ)))
      (-Complex.I * (c : ℂ) * Complex.exp (-Complex.I * ((c * x.re : ℝ) : ℂ))) 0 := by
  convert
    ((((hasDerivAt_id (0 : ℝ)).const_add x.re).const_mul c).ofReal_comp.const_mul
      (-Complex.I)).cexp using 1
  · simp
  · simp
    ring

private lemma phase_deriv (c : ℝ) (x : ℂ) :
    fderiv ℝ (fun z : ℂ => Complex.exp (-Complex.I * ((c * z.re : ℝ) : ℂ))) x 1 =
      -Complex.I * (c : ℂ) * Complex.exp (-Complex.I * ((c * x.re : ℝ) : ℂ)) := by
  have hd : Differentiable ℝ
      (fun z : ℂ => Complex.exp (-Complex.I * ((c * z.re : ℝ) : ℂ))) := by
    fun_prop
  have ht : HasDerivAt (fun t : ℝ => x + (t : ℂ)) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add x
  have hx : HasFDerivAt
      (fun z : ℂ => Complex.exp (-Complex.I * ((c * z.re : ℝ) : ℂ)))
      (fderiv ℝ (fun z : ℂ => Complex.exp (-Complex.I * ((c * z.re : ℝ) : ℂ))) x)
      (x + (0 : ℝ)) := by
    simpa using (hd x).hasFDerivAt
  have ht' := hx.comp_hasDerivAt 0 ht
  have hh : HasDerivAt
      ((fun z : ℂ => Complex.exp (-Complex.I * ((c * z.re : ℝ) : ℂ))) ∘
        (fun t : ℝ => x + (t : ℂ)))
      (-Complex.I * (c : ℂ) * Complex.exp (-Complex.I * ((c * x.re : ℝ) : ℂ))) 0 :=
    phase_hasDerivAt c x
  simpa using ht'.unique hh

private lemma weighted_amplitude_integrable (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (hf : HasInducedAmplitudeEstimates β κ f)
    (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (j h : ℕ) (hj : j ≤ 2)
    (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (fun x : ℂ =>
      Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
        amplitudeDerivative β κ f u j h ρ x) euclideanArea := by
  have hc : Continuous (fun x : ℂ =>
      Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ))) := by
    fun_prop
  exact ((hf.2.2 j h hj u ρ hu hρ).1).bdd_mul hc.aestronglyMeasurable
    (c := 1) (by filter_upwards with x; simp [Complex.norm_exp, Complex.mul_re])

private lemma induced_amplitude_integration_by_parts (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (hf : HasInducedAmplitudeEstimates β κ f)
    (j h : ℕ) (hj : j ≤ 2) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ‖∫ x : ℂ, Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
        amplitudeDerivative β κ f u j h ρ x ∂euclideanArea‖ =
      characterScale β ^ h *
        ‖∫ x : ℂ, Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
          amplitudeDerivative β κ f u j 0 ρ x ∂euclideanArea‖ := by
  have step (h : ℕ) :
      (∫ x : ℂ, Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
          amplitudeDerivative β κ f u j (h + 1) ρ x ∂euclideanArea) =
        Complex.I * (characterScale β : ℂ) *
          (∫ x : ℂ, Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
            amplitudeDerivative β κ f u j h ρ x ∂euclideanArea) := by
    have hi := weighted_amplitude_integrable β κ f hf u hu j h hj ρ hρ
    have hi' := weighted_amplitude_integrable β κ f hf u hu j (h + 1) hj ρ hρ
    have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := euclideanArea)
      (f := fun x : ℂ => Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)))
      (g := amplitudeDerivative β κ f u j h ρ) (v := (1 : ℂ))
      (by simpa only [phase_deriv, mul_assoc] using
        hi.const_mul (-Complex.I * (characterScale β : ℂ)))
      (by simpa only [← amplitude_next β κ f hf u hu j h ρ hρ] using hi') hi
      (fun x _ => by fun_prop) (fun x _ => amplitude_diff β κ f hf u hu j h ρ hρ x)
    simp_rw [phase_deriv (characterScale β)] at hb
    simpa only [← amplitude_next β κ f hf u hu j h ρ hρ, mul_assoc,
      neg_mul, integral_neg, integral_const_mul, neg_neg] using hb
  induction h with
  | zero => simp
  | succ h ih =>
    rw [step, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (characterScale_pos β), ih]
    simp only [pow_succ]
    ring

lemma exists_norm_integral_exp_mul_amplitudeDerivative_zero_le (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (hf : HasInducedAmplitudeEstimates β κ f)
    (j h : ℕ) (hj : j ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℂˣ) (ρ : ℝ), ‖(u : ℂ)‖ = 1 → 0 < ρ →
      ‖∫ x : ℂ, Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
          amplitudeDerivative β κ f u j 0 ρ x ∂euclideanArea‖ ≤
        C * ρ ^ ((2 / 3 : ℝ) - (h : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_integral_exp_mul_amplitudeDerivative_le β κ f hf j h hj
  refine ⟨(characterScale β ^ h)⁻¹ * C,
    mul_pos (inv_pos.mpr (pow_pos (characterScale_pos β) h)) hC, ?_⟩
  intro u ρ hu hρ
  have hh := hb u ρ hu hρ
  rw [induced_amplitude_integration_by_parts β κ f hf j h hj u hu ρ hρ] at hh
  have hp : 0 < characterScale β ^ h := pow_pos (characterScale_pos β) h
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hp.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul] using hh'

private lemma amplitude_radius_hasDerivAt (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (_hf : HasInducedAmplitudeEstimates β κ f)
    (u : ℂˣ) (_hu : ‖(u : ℂ)‖ = 1) (j : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) :
    HasDerivAt (fun r : ℝ => amplitudeDerivative β κ f u j 0 r x)
      ((ρ : ℂ)⁻¹ * amplitudeDerivative β κ f u (j + 1) 0 ρ x) ρ := by
  have hd : DifferentiableAt ℝ (fun r : ℝ => amplitudeDerivative β κ f u j 0 r x) ρ :=
    ((amplitudeDerivative_contDiffAt β κ f u j 0 (ρ, x) hρ).comp ρ
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  convert hd.hasDerivAt using 1
  change (ρ : ℂ)⁻¹ * ((radiusLogDerivative^[j + 1]) (rotatedAmplitude β κ f u)) ρ x = _
  rw [Function.iterate_succ_apply']
  change (ρ : ℂ)⁻¹ * ((ρ : ℂ) * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne'), one_mul]
  rfl

lemma hasDerivAt_integral_exp_mul_amplitudeDerivative (β κ : ℂˣ)
    (f : PrincipalSeries positiveParameter) (hf : HasInducedAmplitudeEstimates β κ f)
    (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (j : ℕ) (hj : j + 1 ≤ 2)
    (ρ : ℝ) (hρ : 0 < ρ) :
    HasDerivAt (fun r : ℝ => ∫ x : ℂ,
      Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
        amplitudeDerivative β κ f u j 0 r x ∂euclideanArea)
      ((ρ : ℂ)⁻¹ * ∫ x : ℂ,
        Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
          amplitudeDerivative β κ f u (j + 1) 0 ρ x ∂euclideanArea) ρ := by
  obtain ⟨B, hB, hb⟩ := exists_integrable_amplitudeDerivative_dominator β κ f hf (j + 1) hj
    (ρ / 2) (2 * ρ) (by positivity) (by linarith)
  have hs : Set.Ioo (ρ / 2) (2 * ρ) ∈ nhds ρ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hm : ∀ᶠ r in nhds ρ, AEStronglyMeasurable (fun x : ℂ =>
      Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
        amplitudeDerivative β κ f u j 0 r x) euclideanArea := by
    filter_upwards [hs] with r hr
    exact (weighted_amplitude_integrable β κ f hf u hu j 0 (by omega) r
      (by linarith [hr.1])).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm
    (weighted_amplitude_integrable β κ f hf u hu j 0 (by omega) ρ hρ)
    ((weighted_amplitude_integrable β κ f hf u hu (j + 1) 0 hj ρ hρ).const_mul
      (ρ : ℂ)⁻¹).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => fun r hr => show
      ‖(r : ℂ)⁻¹ * (Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ)) *
        amplitudeDerivative β κ f u (j + 1) 0 r x)‖ ≤ (ρ / 2)⁻¹ * B x from by
      have hrp : 0 < r := by linarith [hr.1]
      have hb' := hb u r x hu ⟨hr.1.le, hr.2.le⟩
      have hn : 0 ≤ B x := le_trans (norm_nonneg _) hb'
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
      simpa [Complex.norm_exp, Complex.mul_re] using
        mul_le_mul ((inv_le_inv₀ hrp (by positivity)).mpr hr.1.le) hb'
          (norm_nonneg _) (by positivity)))
    (hB.const_mul (ρ / 2)⁻¹)
    (Filter.Eventually.of_forall (fun x => fun r hr => by
      convert (amplitude_radius_hasDerivAt β κ f hf u hu j r
        (by linarith [hr.1]) x).const_mul
        (Complex.exp (-Complex.I * ((characterScale β * x.re : ℝ) : ℂ))) using 1; ring))
  simpa only [integral_const_mul] using hd.2

end DedekindZetaZeroFree.ThetaArchInducedMajorant

end
