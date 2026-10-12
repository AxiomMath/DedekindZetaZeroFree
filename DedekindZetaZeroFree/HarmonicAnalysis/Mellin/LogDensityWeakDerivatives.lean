module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.SmoothLogPushforwardDensities

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

private theorem hasCompactSupport_iteratedDeriv_realLogMellinTest {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    ∀ n : ℕ, HasCompactSupport (iteratedDeriv n f) := by
  intro n
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem IsLogMellinDensity.iteratedDeriv_test_identity
    {F : Type} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    {ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _))}
    {h : SLocalProduct F S → ℂ} {a b : ℝ} {p : ℝ → ℝ → ℂ}
    (hp : IsLogMellinDensity S ν h a b p)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (n : ℕ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ y : (SLocalProduct F S)ˣ,
      (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
        ((iteratedDeriv n φ (Real.log (ProbeWeight.modulus F S y)) : ℝ) : ℂ) ∂ν) =
      ∫ t : ℝ, ((iteratedDeriv n φ t : ℝ) : ℂ) * p σ t := by
  have hcont : Continuous (fun t : ℝ => ((iteratedDeriv n φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_iteratedDeriv n (by simp))
  have hcs : HasCompactSupport (fun t : ℝ => ((iteratedDeriv n φ t : ℝ) : ℂ)) :=
    (hasCompactSupport_iteratedDeriv_realLogMellinTest hφc n).comp_left Complex.ofReal_zero
  have hb : ∃ C : ℝ, ∀ t, ‖((iteratedDeriv n φ t : ℝ) : ℂ)‖ ≤ C :=
    hcs.exists_bound_of_continuous hcont
  rw [hp.2.2 σ hσ (fun t : ℝ => ((iteratedDeriv n φ t : ℝ) : ℂ)) hcont hb]
  apply integral_congr_ae
  filter_upwards with t
  exact mul_comm _ _

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open MeasureTheory

private theorem hasCompactSupport_iteratedDeriv_realTest {φ : ℝ → ℝ}
    (h : HasCompactSupport φ) (n : ℕ) : HasCompactSupport (iteratedDeriv n φ) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem integral_iteratedDeriv_test_mul
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ t : ℝ, ((iteratedDeriv n φ t : ℝ) : ℂ) * f t) =
      (-1 : ℂ) ^ n * ∫ t : ℝ, φ t • iteratedDeriv n f t := by
  revert hf f
  induction n with
  | zero =>
    intro f hf
    simp [Complex.real_smul]
  | succ n ih =>
    intro f hf
    have hf' : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
    have hcs : HasCompactSupport (fun t => ((iteratedDeriv n φ t : ℝ) : ℂ)) := by
      simpa only [Function.comp_def] using
        (hasCompactSupport_iteratedDeriv_realTest hφc n).comp_left
          (g := Complex.ofReal) Complex.ofReal_zero
    have hcs' : HasCompactSupport (fun t => ((iteratedDeriv (n + 1) φ t : ℝ) : ℂ)) := by
      simpa only [Function.comp_def] using
        (hasCompactSupport_iteratedDeriv_realTest hφc (n + 1)).comp_left
          (g := Complex.ofReal) Complex.ofReal_zero
    have hcont : Continuous (fun t => ((iteratedDeriv n φ t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hφ.continuous_iteratedDeriv n (by simp))
    have hcont' : Continuous (fun t => ((iteratedDeriv (n + 1) φ t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hφ.continuous_iteratedDeriv (n + 1) (by simp))
    have hi0 : Integrable (fun t => ((iteratedDeriv n φ t : ℝ) : ℂ) * f t) :=
      (hcont.mul hf.continuous).integrable_of_hasCompactSupport hcs.mul_right
    have hi1 : Integrable (fun t => ((iteratedDeriv n φ t : ℝ) : ℂ) * deriv f t) :=
      (hcont.mul (hf.continuous_deriv (by simp))).integrable_of_hasCompactSupport
        hcs.mul_right
    have hi2 : Integrable (fun t => ((iteratedDeriv (n + 1) φ t : ℝ) : ℂ) * f t) :=
      (hcont'.mul hf.continuous).integrable_of_hasCompactSupport hcs'.mul_right
    have hGu : ∀ x, HasDerivAt (fun t => ((iteratedDeriv n φ t : ℝ) : ℂ))
        (((iteratedDeriv (n + 1) φ x : ℝ) : ℂ)) x := by
      intro x
      have hd : HasDerivAt (iteratedDeriv n φ) (iteratedDeriv (n + 1) φ x) x := by
        rw [iteratedDeriv_succ]
        exact (((hφ.of_le (by simp)).differentiable_iteratedDeriv' n).differentiableAt).hasDerivAt
      exact hd.ofReal_comp
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun t => ((iteratedDeriv n φ t : ℝ) : ℂ))
      (v := f)
      (u' := fun t => ((iteratedDeriv (n + 1) φ t : ℝ) : ℂ))
      (v' := deriv f)
      (fun x _ => hGu x)
      (fun x _ => (hf.differentiable (by simp)).differentiableAt.hasDerivAt)
      hi1 hi2 hi0
    have hIBP : (∫ t : ℝ, ((iteratedDeriv (n + 1) φ t : ℝ) : ℂ) * f t) =
        - ∫ t : ℝ, ((iteratedDeriv n φ t : ℝ) : ℂ) * deriv f t := by
      rw [hibp]; simp
    have hih := ih (deriv f) hf'
    have hInt : (∫ t : ℝ, φ t • iteratedDeriv n (deriv f) t) =
        ∫ t : ℝ, φ t • iteratedDeriv (n + 1) f t := by
      rw [← iteratedDeriv_succ']
    calc
      (∫ t : ℝ, ((iteratedDeriv (n + 1) φ t : ℝ) : ℂ) * f t)
          = - ∫ t : ℝ, ((iteratedDeriv n φ t : ℝ) : ℂ) * deriv f t := hIBP
      _ = - ((-1 : ℂ) ^ n * ∫ t : ℝ, φ t • iteratedDeriv n (deriv f) t) := by
            rw [hih]
      _ = (-1 : ℂ) ^ (n + 1) * ∫ t : ℝ, φ t • iteratedDeriv (n + 1) f t := by
            rw [hInt, pow_succ]; ring

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology

private theorem schwartz_iteratedDeriv (k : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ K : SchwartzMap ℝ ℂ, (K : ℝ → ℂ) = iteratedDeriv n k := by
  induction n with
  | zero => exact ⟨k, by simp⟩
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨SchwartzMap.derivCLM ℝ ℂ K, ?_⟩
    ext t
    rw [SchwartzMap.derivCLM_apply, iteratedDeriv_succ, ← hK]

private theorem weighted_translates_integrable
    (μ : Measure ℝ) [IsFiniteMeasure μ] (w k : ℝ → ℂ)
    (hw : Integrable w μ) (hk : Integrable k) :
    Integrable (fun p : ℝ × ℝ => w p.1 * k (p.2 - p.1)) (μ.prod volume) := by
  have hT : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2 - p.1))
      (μ.prod volume) (μ.prod volume) := by
    have h := (MeasurePreserving.id μ).skew_product
      (measurable_snd.sub measurable_fst)
      (Filter.Eventually.of_forall fun s =>
        (measurePreserving_add_right volume (-s)).map_eq)
    simpa only [id_eq, sub_eq_add_neg] using h
  exact hT.integrable_comp_of_integrable (hw.mul_prod hk)

private theorem weighted_translates_pairing
    (μ : Measure ℝ) [IsFiniteMeasure μ] (w k : ℝ → ℂ)
    (hw : Integrable w μ) (hk : Integrable k)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (hb : ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) :
    (∫ t : ℝ, (∫ s : ℝ, w s * k (t - s) ∂μ) * φ t) =
      ∫ s : ℝ, w s * (∫ t : ℝ, k (t - s) * φ t) ∂μ := by
  obtain ⟨C, hC⟩ := hb
  have hi := (weighted_translates_integrable μ w k hw hk).mul_bdd
    (hφ.measurable.comp measurable_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hC p.2)
  have hs := integral_integral_swap
    (f := fun s t : ℝ => (w s * k (t - s)) * φ t) hi
  simpa only [Function.uncurry_def, ← integral_mul_const, ← integral_const_mul,
    mul_assoc] using hs.symm

theorem schwartzTensor_log_pushforward_integrable_weak_derivative
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ)
    (hh : ProbeSheetVerticalDecay.IsSchwartzTensor F S h)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) :
    ∃ q : ℝ → ℂ, Integrable q ∧
      ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ y : (SLocalProduct F S)ˣ,
          (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
            ((iteratedDeriv n φ (Real.log (ProbeWeight.modulus F S y)) : ℝ) : ℂ) ∂ν) =
          (-1 : ℂ) ^ n * ∫ t : ℝ, φ t • q t := by
  obtain ⟨μ, hμ, w, k, hw, hk, hpair⟩ :=
    ProbeSheetLogDensityRegularity.schwartzTensor_log_pushforward_radial_factorization
      S ν hν h hh σ hσ
  letI : IsFiniteMeasure μ := hμ
  have hkernel : ∃ K : SchwartzMap ℝ ℂ, (K : ℝ → ℂ) = k := by
    rcases hk with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · obtain ⟨K, hK⟩ :=
        ProbeSheetLogDensityRegularity.real_signed_log_kernel_isSchwartz g σ hσ
      exact ⟨K, funext hK⟩
    · obtain ⟨K, hK⟩ :=
        ProbeSheetLogDensityRegularity.complex_angular_log_kernel_isSchwartz g σ hσ
      exact ⟨K, funext hK⟩
  obtain ⟨K, rfl⟩ := hkernel
  obtain ⟨Kn, hKn⟩ := schwartz_iteratedDeriv K n
  refine ⟨(fun t => ∫ s : ℝ, w s * Kn (t - s) ∂μ),
    (weighted_translates_integrable μ w Kn hw Kn.integrable).integral_prod_right, ?_⟩
  intro φ hφ hφc
  have hc : HasCompactSupport (iteratedDeriv n φ) := by
    clear hKn
    induction n with
    | zero => simpa using hφc
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hcont := hφ.continuous_iteratedDeriv n (by simp)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hcont
  have he := hpair (fun t => ((iteratedDeriv n φ t : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hcont)
    ⟨C, fun t => by simpa using hC t⟩
  rw [weighted_translates_pairing μ w K hw K.integrable
    (fun t => ((iteratedDeriv n φ t : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hcont)
    ⟨C, fun t => by simpa using hC t⟩] at he
  obtain ⟨D, hD⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have he' := weighted_translates_pairing μ w Kn hw Kn.integrable
    (fun t => (φ t : ℂ)) (Complex.continuous_ofReal.comp hφ.continuous)
    ⟨D, fun t => by simpa using hD t⟩
  simp only [Complex.real_smul] at ⊢
  simp_rw [mul_comm (↑(φ _) : ℂ)]
  rw [he, he', ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    have hks : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => K (t - s)) :=
      (K.smooth (⊤ : ℕ∞)).comp (contDiff_id.sub contDiff_const)
    have hibp := integral_iteratedDeriv_test_mul (fun t => K (t - s)) hks n φ hφ hφc
    rw [iteratedDeriv_comp_sub_const, ← hKn] at hibp
    simp only [Complex.real_smul] at hibp
    simp_rw [mul_comm (K (_ - s))]
    rw [hibp]
    simp_rw [mul_comm (Kn (_ - s))]
    ring

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

set_option maxHeartbeats 800000

theorem iteratedDeriv_integrable_of_test_pairing
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (q : ℝ → ℂ) (hq : Integrable q)
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ t : ℝ, φ t • iteratedDeriv n f t) = ∫ t : ℝ, φ t • q t) :
    Integrable (iteratedDeriv n f) := by
  have hc : Continuous (iteratedDeriv n f) :=
    hf.continuous_iteratedDeriv n (by simp)
  have he : iteratedDeriv n f =ᵐ[volume] q :=
    ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable hq.locallyIntegrable htest
  exact hq.congr he.symm

theorem schwartzTensor_log_density_iteratedDeriv_integrable
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ)
    (hh : ProbeSheetVerticalDecay.IsSchwartzTensor F S h)
    (a b : ℝ)
    (p : ℝ → ℝ → ℂ) (hp : IsLogMellinDensity S ν h a b p)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (hσpos : 0 < σ) (n : ℕ) :
    Integrable (iteratedDeriv n (p σ)) := by
  by_cases hn : n = 0
  · subst n
    simpa only [iteratedDeriv_zero] using hp.2.1 σ hσ
  · obtain ⟨q, hq, hweak⟩ :=
      schwartzTensor_log_pushforward_integrable_weak_derivative S ν hν h hh σ hσpos n
    apply iteratedDeriv_integrable_of_test_pairing (p σ) (hp.1 σ hσ) n q hq
    intro φ hφ hφc
    have hpair : (-1 : ℂ) ^ n * (∫ t : ℝ, φ t • iteratedDeriv n (p σ) t) =
        (-1 : ℂ) ^ n * (∫ t : ℝ, φ t • q t) := by
      calc
        _ = ∫ t : ℝ, ((iteratedDeriv n φ t : ℝ) : ℂ) * p σ t :=
          (integral_iteratedDeriv_test_mul (p σ) (hp.1 σ hσ) n φ hφ hφc).symm
        _ = ∫ y : (SLocalProduct F S)ˣ,
            (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
              ((iteratedDeriv n φ (Real.log (ProbeWeight.modulus F S y)) : ℝ) : ℂ) ∂ν :=
          (hp.iteratedDeriv_test_identity σ hσ n φ hφ hφc).symm
        _ = _ := hweak φ hφ hφc
    exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)) hpair

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end
