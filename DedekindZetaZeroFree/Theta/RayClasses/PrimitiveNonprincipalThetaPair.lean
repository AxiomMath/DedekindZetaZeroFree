module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.WeightOneFunctionalEquationPairs
public import DedekindZetaZeroFree.Theta.Inversion.ScalarUnitarity
public import DedekindZetaZeroFree.Theta.RayClasses.AggregatePoissonInversion
public import DedekindZetaZeroFree.Theta.RayClasses.KernelNonvanishing
public import DedekindZetaZeroFree.Theta.RayClasses.RamifiedDualConjugacy
public import DedekindZetaZeroFree.Theta.RayClasses.UnramifiedDualConjugacy
public import DedekindZetaZeroFree.Theta.RayClasses.RegularityAndTailBounds

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open scoped NumberField

theorem primitiveNonprincipalThetaPair
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hprim : η.IsPrimitive) (hnon : ¬ η.IsPrincipal) :
    ∃ P : WeakFEPair ℂ,
      P.k = 1 ∧ P.f₀ = 0 ∧ P.g₀ = 0 ∧ ‖P.ε‖ = 1 ∧
      ContinuousOn P.f (Set.Ioi 0) ∧ ContinuousOn P.g (Set.Ioi 0) ∧
      (∀ t : ℝ, 0 < t → P.g t = (starRingEnd ℂ) (P.f t)) ∧
      (∃ C b p : ℝ, 0 < C ∧ 0 < b ∧ 0 < p ∧
        ∀ t : ℝ, 1 ≤ t →
          ‖P.f t‖ ≤ C * Real.exp (-b * t ^ p) ∧
          ‖P.g t‖ ≤ C * Real.exp (-b * t ^ p)) ∧
      (∀ s : ℂ, 1 < s.re →
        MellinConvergent P.f s ∧ MellinConvergent P.g s ∧
        HasSum (fun I : Ideal (𝓞 F) =>
          (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
            Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
            (η I * (Ideal.absNorm I : ℂ) ^ (-s))) (mellin P.f s) ∧
        HasSum (fun I : Ideal (𝓞 F) =>
          (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
            Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
            ((starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s))) (mellin P.g s)) := by
  classical
  let D := Theta.chooseRayThetaRepresentatives F m hm
  let χ := Theta.chooseRayCharacterData (hm := hm) η
  obtain ⟨w, hw, hdual⟩ : ∃ w : ℂ, w ≠ 0 ∧ ∀ t : ℝ, 0 < t →
      Theta.normalizedRayDualTheta D χ.ψ t =
        w * Theta.normalizedRayConjugateTheta D χ.ψ t := by
    by_cases htop : m = ⊤
    · exact Theta.normalizedRayDualTheta_eq_unramified_conjugate hF htop D χ hnon
    · exact Theta.normalizedRayDualTheta_eq_ramified_conjugate hF htop D χ hprim hnon
  have hinv (t : ℝ) (ht : 0 < t) :
      Theta.normalizedRayTheta D χ.ψ t =
        w * (t : ℂ)⁻¹ * (starRingEnd ℂ) (Theta.normalizedRayTheta D χ.ψ t⁻¹) := by
    rw [Theta.normalizedRayTheta_one_div D χ.ψ t ht,
      hdual t⁻¹ (inv_pos.mpr ht), Theta.normalizedRayConjugateTheta_eq_conj]
    ring
  have hwnorm : ‖w‖ = 1 := thetaInversionScalar_norm_eq_one _ w hinv
    (Theta.normalizedRayTheta_nonzero_somewhere F hF m hm η hnon D χ)
  have hfe (t : ℝ) (ht : 0 < t) :
      Theta.normalizedRayTheta D χ.ψ (1 / t) =
        w * (t : ℂ) * Theta.normalizedRayConjugateTheta D χ.ψ t := by
    simpa only [one_div, inv_inv, Complex.ofReal_inv] using
      (Theta.normalizedRayTheta_one_div D χ.ψ t⁻¹ (inv_pos.mpr ht)).trans
        (by rw [inv_inv, hdual t ht]; simp only [Complex.ofReal_inv, inv_inv]; ring)
  obtain ⟨hp, C, b, hC, hb, htail⟩ := Theta.normalizedRayTheta_tail_bound D χ hnon
  have hdecay (t : ℝ) (ht : 1 ≤ t) :
      ‖Theta.normalizedRayTheta D χ.ψ t‖ ≤
        C * Real.exp (-b * t ^ (2 / (Module.finrank ℚ F : ℝ))) ∧
      ‖Theta.normalizedRayConjugateTheta D χ.ψ t‖ ≤
        C * Real.exp (-b * t ^ (2 / (Module.finrank ℚ F : ℝ))) :=
    ⟨(htail t ht).1, (htail t ht).2.2⟩
  obtain ⟨P, hfP, hgP, hkP, hwP, haP, hbP, _⟩ :=
    existsStrongFEPair_weight_one
      (Theta.normalizedRayTheta D χ.ψ) (Theta.normalizedRayConjugateTheta D χ.ψ)
      w C b (2 / (Module.finrank ℚ F : ℝ))
      (Theta.normalizedRayTheta_locallyIntegrableOn D χ)
      (Theta.normalizedRayConjugateTheta_locallyIntegrableOn D χ)
      hw hC.le hb hp hfe hdecay
  refine ⟨P, hkP, haP, hbP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hwP]
  · rw [hfP]; exact Theta.normalizedRayTheta_continuousOn D χ
  · rw [hgP]; exact Theta.normalizedRayConjugateTheta_continuousOn D χ
  · intro t ht
    rw [hfP, hgP]
    exact Theta.normalizedRayConjugateTheta_eq_conj D χ.ψ t
  · refine ⟨C, b, 2 / (Module.finrank ℚ F : ℝ), hC, hb, hp, ?_⟩
    simpa only [hfP, hgP] using hdecay
  · intro s hs
    rw [hfP, hgP]
    obtain ⟨hf, hsumf⟩ := Theta.normalizedRayTheta_mellin_calibration hF D χ hnon s hs
    obtain ⟨hg, hsumg⟩ := Theta.normalizedRayConjugateTheta_mellin_calibration hF D χ hnon s hs
    exact ⟨hf, hg, hsumf, hsumg⟩

end DedekindZetaZeroFree.Hecke
