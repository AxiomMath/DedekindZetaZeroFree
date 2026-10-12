module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.UniformRationalCoefficientMajorant

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaRationalFourierSummation

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical

def freq (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F) (q : KPAdditiveQuotient F) : ℂ :=
  ψ.toAddChar (QuotientAddGroup.mk (-(algebraMap F (KPAdeles F) ν * Quotient.out q)))

private theorem freq_mk (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F) (x : KPAdeles F) :
    freq F ψ ν (QuotientAddGroup.mk x) =
      ψ.toAddChar (QuotientAddGroup.mk (-(algebraMap F (KPAdeles F) ν * x))) := by
  unfold freq
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add
    (NumberField.AdeleRing.principalSubgroup (𝓞 F) F) x
  obtain ⟨s, hs⟩ := r.property
  rw [hr]
  apply congrArg ψ.toAddChar
  apply QuotientAddGroup.eq.mpr
  refine ⟨ν * s, ?_⟩
  rw [map_mul, hs]
  ring

private theorem freq_add (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F) (q r : KPAdditiveQuotient F) :
    freq F ψ ν (q + r) = freq F ψ ν q * freq F ψ ν r := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective r
  rw [← QuotientAddGroup.mk_add, freq_mk, freq_mk, freq_mk, mul_add, neg_add,
    QuotientAddGroup.mk_add, ψ.toAddChar.map_add_eq_mul]

private theorem freq_zero_scalar (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (q : KPAdditiveQuotient F) :
    freq F ψ 0 q = 1 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [freq_mk, map_zero, zero_mul, neg_zero, QuotientAddGroup.mk_zero,
    ψ.toAddChar.map_zero_eq_one]

private theorem freq_zero (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F) : freq F ψ ν 0 = 1 := by
  simpa only [mul_zero, neg_zero, QuotientAddGroup.mk_zero,
    ψ.toAddChar.map_zero_eq_one] using
    freq_mk F ψ ν (0 : KPAdeles F)

private theorem norm_freq (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F) (q : KPAdditiveQuotient F) :
    ‖freq F ψ ν q‖ = 1 := ψ.unitary _

private theorem freq_continuous (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F) : Continuous (freq F ψ ν) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (NumberField.AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  change Continuous (fun x : KPAdeles F => freq F ψ ν (QuotientAddGroup.mk x))
  simp_rw [freq_mk]
  exact ψ.continuous_toFun.comp
    (QuotientAddGroup.continuous_mk.comp ((continuous_const.mul continuous_id).neg))

private theorem freq_add_scalar (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν η : F) (q : KPAdditiveQuotient F) :
    freq F ψ (ν + η) q = freq F ψ ν q * freq F ψ η q := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [freq_mk, freq_mk, freq_mk, map_add, add_mul, neg_add, QuotientAddGroup.mk_add,
    ψ.toAddChar.map_add_eq_mul]

private theorem freq_integral_zero (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    [MeasurableSpace (KPAdditiveQuotient F)] [BorelSpace (KPAdditiveQuotient F)]
    (μ : Measure (KPAdditiveQuotient F)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (ν : F) (hν : ν ≠ 0) :
    (∫ q, freq F ψ ν q ∂μ) = 0 := by
  obtain ⟨q, hq⟩ := hψ
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  let y : KPAdeles F := -(algebraMap F (KPAdeles F) ν⁻¹ * x)
  have hy : freq F ψ ν (QuotientAddGroup.mk y) ≠ 1 := by
    rw [freq_mk]
    have heq : -(algebraMap F (KPAdeles F) ν * y) = x := by
      dsimp [y]
      rw [mul_neg, neg_neg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hν, map_one, one_mul]
    rw [heq]
    exact hq
  have hi := integral_add_right_eq_self (μ := μ) (freq F ψ ν) (QuotientAddGroup.mk y)
  simp_rw [freq_add] at hi
  rw [integral_mul_const] at hi
  by_contra hn
  exact hy ((mul_eq_left₀ hn).mp hi)

private theorem freq_exhaustion (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    (χ : AddChar (KPAdditiveQuotient F) Circle)
    (hc : Continuous χ) (hne : χ ≠ 1) :
    ∃ ν : F, ν ≠ 0 ∧ ∀ q, (χ q : ℂ) = freq F ψ ν q := by
  let S := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  let ψA : AddChar (KPAdeles F) Circle :=
    { toFun := fun x => ⟨ψ.toAddChar (QuotientAddGroup.mk x),
        mem_sphere_zero_iff_norm.mpr (ψ.unitary (QuotientAddGroup.mk x))⟩
      map_zero_eq_one' := by ext; simp
      map_add_eq_mul' := by
        intros x y
        ext
        change ψ.toAddChar (QuotientAddGroup.mk (x + y)) =
          ψ.toAddChar (QuotientAddGroup.mk x) * ψ.toAddChar (QuotientAddGroup.mk y)
        rw [QuotientAddGroup.mk_add, ψ.toAddChar.map_add_eq_mul] }
  have hcont : Continuous ψA :=
    (ψ.continuous_toFun.comp QuotientAddGroup.continuous_mk).subtype_mk _
  have hnA : ψA ≠ 1 := by
    obtain ⟨q, hq⟩ := hψ
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    intro h
    exact hq (congrArg (fun f : AddChar (KPAdeles F) Circle => (f x : ℂ)) h)
  have hF (t : F) : ψA (algebraMap F (KPAdeles F) t) = 1 := by
    have hz : (QuotientAddGroup.mk (algebraMap F (KPAdeles F) t) : KPAdditiveQuotient F) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨t, rfl⟩
    ext
    change ψ.toAddChar (QuotientAddGroup.mk (algebraMap F (KPAdeles F) t)) = 1
    rw [hz, ψ.toAddChar.map_zero_eq_one]
  obtain ⟨t, ⟨ht, hf⟩, _⟩ := kp_adelic_character_exhaustion F ψA hcont hnA hF χ hc hne
  refine ⟨-t, neg_ne_zero.mpr ht, ?_⟩
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [freq_mk, map_neg, neg_mul, neg_neg]
  exact congrArg (fun z : Circle => (z : ℂ)) (hf x)

private theorem series_integral (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    [MeasurableSpace (KPAdditiveQuotient F)] [BorelSpace (KPAdditiveQuotient F)]
    (μ : Measure (KPAdditiveQuotient F)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (c : F → ℂ) (hs : Summable (fun ν => ‖c ν‖)) (η : F) :
    (∫ q, (∑' ν, c ν * freq F ψ (-ν) q) * freq F ψ η q ∂μ) = c η := by
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  let t : F → KPAdditiveQuotient F → ℂ := fun ν q =>
    c ν * freq F ψ (-ν) q * freq F ψ η q
  have htc (ν : F) : Continuous (t ν) :=
    (continuous_const.mul (freq_continuous F ψ _)).mul (freq_continuous F ψ _)
  have hti (ν : F) : Integrable (t ν) μ :=
    integrableOn_univ.mp ((htc ν).continuousOn.integrableOn_compact isCompact_univ)
  have hnorm (ν : F) (q : KPAdditiveQuotient F) : ‖t ν q‖ = ‖c ν‖ := by
    simp only [t, norm_mul, norm_freq, mul_one]
  have hn : Summable (fun ν => ∫ q, ‖t ν q‖ ∂μ) := by
    simpa only [hnorm, integral_const, probReal_univ, one_smul] using hs
  have hsum (q : KPAdditiveQuotient F) :
      (∑' ν, t ν q) = (∑' ν, c ν * freq F ψ (-ν) q) * freq F ψ η q := by
    have hp : Summable (fun ν => c ν * freq F ψ (-ν) q) :=
      hs.of_norm_bounded (fun ν => by
        simp only [norm_mul, norm_freq, mul_one]; exact le_rfl)
    exact hp.tsum_mul_right _
  rw [← integral_congr_ae (Filter.Eventually.of_forall hsum),
    ← integral_tsum_of_summable_integral_norm hti hn]
  have hm (ν : F) : (∫ q, t ν q ∂μ) = if ν = η then c η else 0 := by
    simp_rw [t, mul_assoc, ← freq_add_scalar, integral_const_mul]
    by_cases h : ν = η
    · subst ν
      simp only [neg_add_cancel, freq_zero_scalar, integral_const, probReal_univ,
        one_smul, mul_one, if_pos rfl, ↓reduceIte]
    · rw [freq_integral_zero F ψ hψ μ _ (by
        intro hh
        exact h (sub_eq_zero.mp (by simpa only [neg_add_eq_sub] using hh)).symm)]
      simp [h]
  simp_rw [hm]
  rw [tsum_eq_single η (fun ν hν => by simp [hν])]
  simp

theorem hasSum_of_summable_coefficients (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    [MeasurableSpace (KPAdditiveQuotient F)] [BorelSpace (KPAdditiveQuotient F)]
    (μ : Measure (KPAdditiveQuotient F)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (f : KPAdditiveQuotient F → ℂ) (hf : Continuous f)
    (hs : Summable (fun ν : F => ‖∫ q, f q * freq F ψ ν q ∂μ‖)) :
    HasSum (fun ν : F => ∫ q, f q * freq F ψ ν q ∂μ) (f 0) := by
  let c : F → ℂ := fun ν => ∫ q, f q * freq F ψ ν q ∂μ
  let s : KPAdditiveQuotient F → ℂ := fun q => ∑' ν, c ν * freq F ψ (-ν) q
  have hscont : Continuous s := continuous_tsum
    (fun ν => continuous_const.mul (freq_continuous F ψ _)) hs
    (fun ν q => by simp only [norm_mul, norm_freq, mul_one]; exact le_rfl)
  have hi (η : F) : (∫ q, (f q - s q) * freq F ψ η q ∂μ) = 0 := by
    have hfint : Integrable (fun q => f q * freq F ψ η q) μ :=
      integrableOn_univ.mp ((hf.mul (freq_continuous F ψ η)).continuousOn.integrableOn_compact
        isCompact_univ)
    have hsint : Integrable (fun q => s q * freq F ψ η q) μ :=
      integrableOn_univ.mp ((hscont.mul (freq_continuous F ψ η)).continuousOn.integrableOn_compact
        isCompact_univ)
    simp_rw [sub_mul]
    rw [integral_sub hfint hsint, series_integral F ψ hψ μ c hs η]
    exact sub_self _
  have huniq := KPCompactFourier.uniqueness_of_characters_separate μ
    (AdelicSeparation.additiveAdeleQuotient_characters_separate F)
    (fun q => f q - s q) (hf.sub hscont) (by
      intro χ hc hn
      obtain ⟨ν, hν, hχ⟩ := freq_exhaustion F ψ hψ χ hc hn
      simp_rw [hχ]
      exact hi ν)
  have hmean : (∫ q, f q - s q ∂μ) = 0 := by
    simpa only [freq_zero_scalar, mul_one] using hi 0
  have hval := huniq 0
  rw [hmean, sub_eq_zero] at hval
  have heq : s 0 = ∑' ν, c ν := by
    simp only [s, freq_zero, mul_one]
  rw [heq] at hval
  exact hval.symm ▸ hs.of_norm.hasSum

end DedekindZetaZeroFree.ThetaRationalFourierSummation

end
