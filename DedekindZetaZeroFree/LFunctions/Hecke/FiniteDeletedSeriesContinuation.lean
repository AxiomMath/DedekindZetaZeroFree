module

public import DedekindZetaZeroFree.Moments.Reflected.AllRowEulerFactorization
public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalRayContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalRayContinuation

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

theorem deleted_exterior_series_continuation
    (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (D : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hD : D.Finite)
    (hSD : (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆ D)
    (a : A.Exterior → ℂ)
    (ha : ∀ I : A.Exterior,
      a I = Detector.deletedPrimitiveIdealCoefficient F ν D I.val) :
    ∃ l : ℂ → ℂ,
      (¬ ν.character.IsPrincipal → DifferentiableOn ℂ l {s : ℂ | 0 < s.re}) ∧
      ∀ s : ℂ, 1 < s.re → l s = InitialSeparatedEuler.dirichletSeries a s := by
  classical
  by_cases hnp : ν.character.IsPrincipal
  ·

    exact ⟨InitialSeparatedEuler.dirichletSeries a, fun h => absurd hnp h,
      fun s _ => rfl⟩
  ·

    have hF : NumberField.IsTotallyComplex F :=
      primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
    let H := nonprincipalRayHeckeData F hF ν.conductor ν.conductor_ne_zero
      ν.character ν.primitive hnp
    have hLmero : MeromorphicOn H.L {s : ℂ | 0 < s.re} :=
      (H.L_holo.analyticOnNhd
        (isOpen_lt continuous_const Complex.continuous_re)).meromorphicOn
    obtain ⟨hmask, -, hsum⟩ := Detector.deleted_primitive_L_continuation F ν D hD
      {s : ℂ | 0 < s.re} H.L hLmero H.series
    refine ⟨fun s => H.L s *
        Detector.finiteEulerDeletionMask F D (fun v => ν.character v.asIdeal) s,
      fun _ => H.L_holo.mul (hmask.differentiableOn.mono (Set.subset_univ _)), ?_⟩
    intro s hs

    have hzero : ∀ I : Ideal (𝓞 F), ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) →
        Detector.deletedPrimitiveIdealCoefficient F ν D I *
          (Ideal.absNorm I : ℂ) ^ (-s) = 0 := by
      intro I hn
      have hc : Detector.deletedPrimitiveIdealCoefficient F ν D I = 0 := by
        by_cases hbot : I = ⊥
        · subst hbot
          simp only [Detector.deletedPrimitiveIdealCoefficient]
          by_cases hex : ∃ v ∈ D, (⊥ : Ideal (𝓞 F)) ≤ v.asIdeal
          · simp [hex]
          · simp only [hex, if_false]
            exact (ν.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
        · have hsup : I ⊔ A.cS ≠ ⊤ := fun h => hn ⟨hbot, h⟩
          have hex : ∃ v ∈ D, I ≤ v.asIdeal := by
            have hA : ¬ ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                v ∈ A.Sf → I ⊔ v.asIdeal = ⊤ := by
              intro hall
              exact hsup ((SArithmeticData.exterior_iff A ⟨I, hbot⟩).mpr hall)
            push Not at hA
            obtain ⟨v, hvS, hvv⟩ := hA
            have heq : v.asIdeal = I ⊔ v.asIdeal :=
              v.isMaximal.eq_of_le hvv le_sup_right
            exact ⟨v, hSD (by simpa using hvS), le_sup_left.trans heq.symm.le⟩
          simp only [Detector.deletedPrimitiveIdealCoefficient]
          simp [hex]
      rw [hc, zero_mul]
    have hsupport : Function.support (fun I : Ideal (𝓞 F) =>
        Detector.deletedPrimitiveIdealCoefficient F ν D I *
          (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
        {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
      intro I hI
      by_contra hn
      exact hI (hzero I hn)
    show H.L s * Detector.finiteEulerDeletionMask F D
        (fun v => ν.character v.asIdeal) s =
      InitialSeparatedEuler.dirichletSeries a s
    rw [← (hsum s hs).tsum_eq]
    rw [InitialSeparatedEuler.dirichletSeries]
    rw [← tsum_subtype_eq_of_support_subset hsupport]
    apply tsum_congr
    intro I
    simp only [ExteriorIdealEuler.summand]
    rw [ha I]

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows
