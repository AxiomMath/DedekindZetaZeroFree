module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.IntegrableLogPushforwardDensity
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.RadialLogDensityFactorization

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity
noncomputable section
open MeasureTheory
open scoped Convolution
open scoped ContDiff

private lemma bddAbove_range_norm_schwartz (g : SchwartzMap ℝ ℂ) :
    BddAbove (Set.range fun x : ℝ => ‖g x‖) :=
  ⟨(SchwartzMap.seminorm ℝ 0 0) g, by
    rintro _ ⟨x, rfl⟩
    exact SchwartzMap.norm_le_seminorm ℝ g x⟩

 def schwartzIterDeriv (k : SchwartzMap ℝ ℂ) (m : ℕ) : SchwartzMap ℝ ℂ :=
  ((fun g : SchwartzMap ℝ ℂ => SchwartzMap.derivCLM ℝ ℂ g)^[m]) k

private lemma schwartzIterDeriv_zero (k : SchwartzMap ℝ ℂ) : schwartzIterDeriv k 0 = k := by
  simp [schwartzIterDeriv]

private lemma schwartzIterDeriv_succ (k : SchwartzMap ℝ ℂ) (m : ℕ) :
    schwartzIterDeriv k (m + 1) = SchwartzMap.derivCLM ℝ ℂ (schwartzIterDeriv k m) := by
  simp [schwartzIterDeriv, Function.iterate_succ_apply']

private lemma schwartzIterDeriv_succ_apply (k : SchwartzMap ℝ ℂ) (m : ℕ) (x : ℝ) :
    schwartzIterDeriv k (m + 1) x = deriv (schwartzIterDeriv k m) x := by
  rw [schwartzIterDeriv_succ, SchwartzMap.derivCLM_apply]

theorem schwartz_weighted_translates_smooth_integrable
    (k : SchwartzMap ℝ ℂ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (w : ℝ → ℂ) (hw : Integrable w μ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ∫ s : ℝ, w s * k (t - s) ∂μ) ∧
    Integrable (fun t : ℝ => ∫ s : ℝ, w s * k (t - s) ∂μ) := by
  classical
  have hMeasK : ∀ (g : SchwartzMap ℝ ℂ) (x : ℝ),
      AEStronglyMeasurable (fun s : ℝ => w s * g (x - s)) μ := by
    intro g x
    exact hw.aestronglyMeasurable.mul
      (g.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hIntK : ∀ (g : SchwartzMap ℝ ℂ) (x : ℝ),
      Integrable (fun s : ℝ => w s * g (x - s)) μ := by
    intro g x
    refine Integrable.mono' (hw.norm.mul_const ((SchwartzMap.seminorm ℝ 0 0) g))
      (hMeasK g x) (Filter.Eventually.of_forall fun s => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ g (x - s)) (norm_nonneg _)
  have hIntK' : ∀ (g : SchwartzMap ℝ ℂ) (x : ℝ),
      Integrable (fun a : ℝ =>
        ContinuousLinearMap.toSpanSingleton ℝ (w a * g (x - a))) μ := by
    intro g x
    refine Integrable.mono' (hw.norm.mul_const ((SchwartzMap.seminorm ℝ 0 0) g))
      ?_ (Filter.Eventually.of_forall fun a => ?_)
    · exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℂ)).continuous
        |>.comp_aestronglyMeasurable (hMeasK g x)
    · rw [ContinuousLinearMap.norm_toSpanSingleton, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.norm_le_seminorm ℝ g (x - a)) (norm_nonneg _)
  have hCont : ∀ m : ℕ,
      Continuous (fun x : ℝ => ∫ s, w s * schwartzIterDeriv k m (x - s) ∂μ) := by
    intro m
    have h : Continuous (fun x : ℝ =>
        (w ⋆[ContinuousLinearMap.lsmul ℝ ℂ, μ] (schwartzIterDeriv k m)) x) :=
      (bddAbove_range_norm_schwartz (schwartzIterDeriv k m))
        |>.continuous_convolution_right_of_integrable (ContinuousLinearMap.lsmul ℝ ℂ) hw
          (schwartzIterDeriv k m).continuous
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      using h
  have hIntOut : ∀ m : ℕ,
      Integrable (fun x : ℝ => ∫ s, w s * schwartzIterDeriv k m (x - s) ∂μ) volume := by
    intro m
    have hg : Integrable (fun x : ℝ => (schwartzIterDeriv k m : ℝ → ℂ) x) volume :=
      SchwartzMap.integrable (schwartzIterDeriv k m)
    have hprod : Integrable
        (fun p : ℝ × ℝ =>
          ContinuousLinearMap.lsmul ℝ ℂ (w p.2) (schwartzIterDeriv k m (p.1 - p.2)))
        (volume.prod μ) :=
      Integrable.convolution_integrand (μ := volume) (ν := μ) (f := w)
        (g := fun x : ℝ => (schwartzIterDeriv k m : ℝ → ℂ) x)
        (ContinuousLinearMap.lsmul ℝ ℂ) hw hg
    have h := hprod.integral_prod_left
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h
  have hDeriv : ∀ (m : ℕ) (x : ℝ),
      HasDerivAt (fun y : ℝ => ∫ s, w s * schwartzIterDeriv k m (y - s) ∂μ)
        (∫ s, w s * schwartzIterDeriv k (m + 1) (x - s) ∂μ) x := by
    intro m x
    have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := μ)
      (F := fun y a => w a * schwartzIterDeriv k m (y - a))
      (F' := fun y a =>
        ContinuousLinearMap.toSpanSingleton ℝ (w a * schwartzIterDeriv k (m + 1) (y - a)))
      (bound := fun a => ‖w a‖ * (SchwartzMap.seminorm ℝ 0 0) (schwartzIterDeriv k (m + 1)))
      (s := Set.univ) (x₀ := x)
      (by simp)
      (Filter.Eventually.of_forall fun y => hMeasK _ y)
      (hIntK _ x)
      (by
        exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℂ)).continuous
          |>.comp_aestronglyMeasurable (hMeasK (schwartzIterDeriv k (m + 1)) x))
      (Filter.Eventually.of_forall fun a => by
        intro y _
        rw [ContinuousLinearMap.norm_toSpanSingleton, norm_mul]
        exact mul_le_mul_of_nonneg_left
          (SchwartzMap.norm_le_seminorm ℝ (schwartzIterDeriv k (m + 1)) (y - a)) (norm_nonneg _))
      (hw.norm.mul_const _)
      (Filter.Eventually.of_forall fun a => by
        intro y _
        have hgd : HasDerivAt (schwartzIterDeriv k m)
            (schwartzIterDeriv k (m + 1) (y - a)) (y - a) := by
          have h := (schwartzIterDeriv k m).hasDerivAt (y - a)
          rw [schwartzIterDeriv_succ_apply]
          exact h
        exact ((hgd.comp_sub_const y a).const_mul (w a)).hasFDerivAt)
    have h := hmain.hasDerivAt
    rw [ContinuousLinearMap.integral_apply (hIntK' _ x)] at h
    rw [show (∫ a, ContinuousLinearMap.toSpanSingleton ℝ
            (w a * schwartzIterDeriv k (m + 1) (x - a)) 1 ∂μ)
          = ∫ a, w a * schwartzIterDeriv k (m + 1) (x - a) ∂μ from
        integral_congr_ae (Filter.Eventually.of_forall fun a =>
          ContinuousLinearMap.toSpanSingleton_apply_one ℝ _)] at h
    exact h
  have hQ : ∀ n : ℕ, ∀ m : ℕ,
      ContDiff ℝ (n : ℕ∞ω) (fun x : ℝ => ∫ s, w s * schwartzIterDeriv k m (x - s) ∂μ) := by
    intro n
    induction n with
    | zero =>
      intro m
      simpa using hCont m
    | succ n ih =>
      intro m
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = ((n : ℕ∞ω) + 1) from by push_cast; rfl,
        contDiff_succ_iff_hasFDerivAt]
      refine ⟨fun x => ContinuousLinearMap.toSpanSingleton ℝ
        (∫ s, w s * schwartzIterDeriv k (m + 1) (x - s) ∂μ), ?_, ?_⟩
      · exact (ContinuousLinearEquiv.contDiff
          (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℂ))).comp (ih (m + 1))
      · intro x
        exact hasDerivAt_iff_hasFDerivAt.2 (hDeriv m x)
  constructor
  · rw [contDiff_infty]
    intro n
    simpa only [schwartzIterDeriv_zero] using hQ n 0
  · simpa only [schwartzIterDeriv_zero] using hIntOut 0

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

theorem log_pushforward_density_ae_unique
    (p q : ℝ → ℂ) (hp : Integrable p) (hq : Integrable q)
    (htest : ∀ φ : ℝ → ℂ, Continuous φ →
      (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
      (∫ t : ℝ, p t * φ t) = ∫ t : ℝ, q t * φ t) :
    p =ᵐ[volume] q := by
  apply ae_eq_of_integral_contDiff_smul_eq hp.locallyIntegrable hq.locallyIntegrable
  intro φ hφ hc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ.continuous
  have hi := htest (fun t => (φ t : ℂ))
    (Complex.continuous_ofReal.comp hφ.continuous)
    ⟨C, fun t => by simpa using hC t⟩
  simpa only [Complex.real_smul, mul_comm] using hi

theorem smooth_representative_of_log_density_test_identity
    (q : ℝ → ℂ) (hq : Integrable q)
    (hex : ∃ r : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) r ∧ Integrable r ∧
      ∀ φ : ℝ → ℂ, Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
        (∫ t : ℝ, r t * φ t) = ∫ t : ℝ, q t * φ t) :
    ∃ r : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) r ∧ r =ᵐ[volume] q := by
  obtain ⟨r, hr, hri, htest⟩ := hex
  exact ⟨r, hr, log_pushforward_density_ae_unique r q hri hq htest⟩

theorem schwartzTensor_log_pushforward_smooth_representative
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ)
    (hh : ProbeSheetVerticalDecay.IsSchwartzTensor F S h)
    (σ : ℝ) (hσ : 0 < σ)
    (q : ℝ → ℂ) (hq : Integrable q)
    (htest : ∀ φ : ℝ → ℂ,
      Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
      (∫ y : (SLocalProduct F S)ˣ,
        (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
          φ (Real.log (ProbeWeight.modulus F S y)) ∂ν) =
        ∫ t : ℝ, q t * φ t) :
    ∃ r : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) r ∧ r =ᵐ[volume] q := by
  obtain ⟨μ, hμ, w, k, hw, hk, hpair⟩ :=
    ProbeSheetLogDensityRegularity.schwartzTensor_log_pushforward_radial_factorization
      S ν hν h hh σ hσ
  letI : IsFiniteMeasure μ := hμ
  have hkernel : ∃ K : SchwartzMap ℝ ℂ, ∀ t, K t = k t := by
    rcases hk with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact ProbeSheetLogDensityRegularity.real_signed_log_kernel_isSchwartz g σ hσ
    · exact ProbeSheetLogDensityRegularity.complex_angular_log_kernel_isSchwartz g σ hσ
  obtain ⟨K, hK⟩ := hkernel
  have hmix :=
    ProbeSheetLogDensityRegularity.schwartz_weighted_translates_smooth_integrable
      K μ w hw
  have hKeq : (K : ℝ → ℂ) = k := funext hK
  rw [hKeq] at hmix
  apply smooth_representative_of_log_density_test_identity q hq
  refine ⟨(fun t => ∫ s : ℝ, w s * k (t - s) ∂μ), hmix.1, hmix.2, ?_⟩
  intro φ hφ hb
  exact (hpair φ hφ hb).symm.trans (htest φ hφ hb)

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

def IsLogMellinDensity
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (h : SLocalProduct F S → ℂ) (a b : ℝ) (p : ℝ → ℝ → ℂ) : Prop :=
  (∀ σ ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (p σ)) ∧
  (∀ σ ∈ Set.Icc a b, Integrable (p σ)) ∧
  (∀ σ ∈ Set.Icc a b, ∀ φ : ℝ → ℂ,
    Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
    (∫ y : (SLocalProduct F S)ˣ,
      (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
        φ (Real.log (ProbeWeight.modulus F S y)) ∂ν) =
    ∫ t : ℝ, p σ t * φ t)

theorem schwartzTensor_smooth_log_disintegration
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ)
    (hh : ProbeSheetVerticalDecay.IsSchwartzTensor F S h)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ p : ℝ → ℝ → ℂ, IsLogMellinDensity S ν h a b p  := by
  classical
  have hlocal : ∀ σ : ℝ, ∃ r : ℝ → ℂ, σ ∈ Set.Icc a b →
      ContDiff ℝ (⊤ : ℕ∞) r ∧ Integrable r ∧
        ∀ φ : ℝ → ℂ, Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
          (∫ y : (SLocalProduct F S)ˣ,
            (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
              φ (Real.log (ProbeWeight.modulus F S y)) ∂ν) =
            ∫ t : ℝ, r t * φ t := by
    intro σ
    by_cases hσ : σ ∈ Set.Icc a b
    · have hpos : 0 < σ := lt_of_lt_of_le ha hσ.1
      obtain ⟨q, hq, htest⟩ :=
        schwartzTensor_integrable_log_pushforward_density S ν hν h hh σ hpos
      obtain ⟨r, hr, hrq⟩ :=
        schwartzTensor_log_pushforward_smooth_representative S ν hν h hh
          σ hpos q hq htest
      refine ⟨r, fun _ => ⟨hr, hq.congr hrq.symm, ?_⟩⟩
      intro φ hφ hb
      rw [htest φ hφ hb]
      apply integral_congr_ae
      filter_upwards [hrq] with t ht
      rw [ht]
    · exact ⟨fun _ => 0, fun hs => (hσ hs).elim⟩
  choose p hp using hlocal
  exact ⟨p, (fun σ hσ => (hp σ hσ).1),
    (fun σ hσ => (hp σ hσ).2.1), (fun σ hσ => (hp σ hσ).2.2)⟩

end
end DedekindZetaZeroFree.ProbeSheetLogDensity

end
