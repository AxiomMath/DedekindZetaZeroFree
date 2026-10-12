module

public import DedekindZetaZeroFree.LFunctions.Tate.Local.AnnularFourierMellin

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TateFiniteShellFourierIntegrals

variable (F : Type) [Field F] [NumberField F]

 instance finiteShellWeightedFourierAdicCompletionMeasurableSpace (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
 instance finiteShellWeightedFourierAdicCompletionBorelSpace (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem finiteShell_weighted_fourier_integral_ne_zero
    (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (∫ z in ({0}ᶜ : Set (v.adicCompletion F)),
      TateFiniteShell.fourier F v (localFiniteCharacter F v)
        (localNormalizedHaar F v) (TateFiniteShell.annularTest F v) z *
        (‖z‖ ^ (s - 1) : ℝ) ∂localNormalizedHaar F v) ≠ 0 := by
  let μ := Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F v)
  have hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1 :=
    Measure.addHaarMeasure_self
  let m : ℤ := -(localDifferentExponent F v : ℤ)
  let a : v.adicCompletion F := finiteCompletionUniformizer F v ^ m
  have ha : Valued.v a = WithZero.exp (-m) := by
    simp [a, map_zpow₀, finiteCompletionUniformizer_valuation, ← WithZero.exp_zsmul]
  have ha0 : a ≠ 0 := zpow_ne_zero _ (finiteCompletionUniformizer_ne_zero F v)
  let ψ := TateFiniteShell.rescaledCharacter F v (localFiniteCharacter F v) a
  have hψ : Continuous ψ := TateFiniteShell.rescaledCharacter_continuous F v
    (localFiniteCharacter F v) (continuous_localFiniteCharacter F v) a
  have hc : TateFiniteShell.HasConductor F v ψ 0 :=
    TateFiniteShell.rescaledCharacter_conductorZero F v (localFiniteCharacter F v)
      m (TateFiniteShell.canonicalTrace_adapter F v).1 a ha
  let f := TateFiniteShell.fourier F v ψ μ (TateFiniteShell.annularTest F v)
  let g := TateFiniteShell.fourier F v (localFiniteCharacter F v)
    (localNormalizedHaar F v) (TateFiniteShell.annularTest F v)
  have hg : g = fun y => (localHalfDifferentFactor F v : ℂ) * f (y / a) := by
    funext y
    dsimp only [g, f, ψ]
    rw [← (TateFiniteShell.canonicalTrace_adapter F v).2.1,
      TateFiniteShell.fourier_conductorHaar,
      TateFiniteShell.fourier_rescaledCharacter F v _ μ _ a ha0]
    simp only [localHalfDifferentFactor, Int.cast_neg, Int.cast_natCast]
    rfl
  have hz := TateFiniteShell.mellin_fourier_annularTest F v ψ hψ hc μ hμ s hs hs1
  have hn : TateFiniteShell.mellin F v μ g s ≠ 0 := by
    rw [hg]
    unfold TateFiniteShell.mellin
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    change (localHalfDifferentFactor F v : ℂ) *
      TateFiniteShell.mellin F v μ (fun y => f (y / a)) s ≠ 0
    rw [TateFiniteShell.mellin_dilate_test F v μ f a ha0 s]
    apply mul_ne_zero
    · exact_mod_cast (localHalfDifferentFactor_pos F v).ne'
    · apply mul_ne_zero
      · exact_mod_cast (Real.rpow_pos_of_pos (norm_pos_iff.mpr ha0) s).ne'
      · exact hz.2.2.2
  letI : NullSingletonClass μ := KPRankOneMellin.completion_addHaar_nullSingletonClass F v μ
  have hm : TateFiniteShell.mellin F v μ g s =
      (↑((1 - (TateFiniteShell.q F v : ℝ)⁻¹)⁻¹) : ℂ) *
        (∫ y in ({0}ᶜ : Set (v.adicCompletion F)), g y * (‖y‖ ^ (s - 1) : ℝ) ∂μ) := by
    unfold TateFiniteShell.mellin
    rw [TateFiniteShell.realMellinIntegrand_eq_complex,
      TateFiniteShell.multiplicativeHaar_eq_smul, integral_smul_measure]
    rw [ENNReal.toReal_ofReal]
    · rw [Complex.real_smul]
      congr 1
      change KPRankOneMellin.mellin F v μ g (s : ℂ) = _
      rw [KPRankOneMellin.mellin_eq_additive_integral]
      have hr : μ.restrict ({0}ᶜ : Set (v.adicCompletion F)) = μ := by simp
      rw [hr]
      apply integral_congr_ae
      filter_upwards with y
      rw [Complex.ofReal_cpow (norm_nonneg y) (s - 1)]
      simp only [Complex.ofReal_sub, Complex.ofReal_one]
    · have hq : 1 < (TateFiniteShell.q F v : ℝ) := by
        exact_mod_cast finiteCompletion_residueCard_gt_one F v
      exact inv_nonneg.mpr (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le))
  have hi : (∫ y in ({0}ᶜ : Set (v.adicCompletion F)),
      g y * (‖y‖ ^ (s - 1) : ℝ) ∂μ) ≠ 0 := by
    intro hi
    exact hn (by rw [hm, hi, mul_zero])
  change (∫ y in ({0}ᶜ : Set (v.adicCompletion F)),
    g y * (‖y‖ ^ (s - 1) : ℝ) ∂localNormalizedHaar F v) ≠ 0
  unfold localNormalizedHaar
  rw [Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (localHalfDifferentFactor_pos F v).le, Complex.real_smul]
  exact mul_ne_zero (by exact_mod_cast (localHalfDifferentFactor_pos F v).ne') hi

end DedekindZetaZeroFree.TateFiniteShellFourierIntegrals

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TateFiniteShellFourierIntegrals

variable (F : Type) [Field F] [NumberField F]

private instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
private instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

end DedekindZetaZeroFree.TateFiniteShellFourierIntegrals

end
end
