module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ShellDilationAndGeometricRatio

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem actual_tail_shell_norm_step (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ (s : ℂ)
      (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
      (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q),
      (∫ x in actualShell F q ((m : ℤ) + 3),
        ‖actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x‖ ∂μ) =
      ‖actualShellRatio F q ε s‖ *
        (∫ x in actualShell F q (m : ℤ),
          ‖actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x‖ ∂μ) := by
  obtain ⟨M, hM⟩ := actual_tail_shell_pointwise F ζ hζ q S P J hJ ε π
  refine ⟨M, ?_⟩
  intro m hm s φ k h
  rw [actual_shell_dilation F q μ π hπ]
  have habs : Measurable (KPCubicHaar.abs (LocalField F q)) := by
    unfold KPCubicHaar.abs
    simpa only [KPCubicUnitIndices.residueCard, CubicUnitCharacters.residueCard] using
      KPRamifiedBetaConductorSeries.normalizedAbs_measurable (LocalField F q)
  have hset : MeasurableSet (actualShell F q (m : ℤ)) :=
    (measurableSet_lt measurable_const habs).inter (measurableSet_le habs measurable_const)
  have he := setIntegral_congr_fun (f := fun x =>
      ‖actualStandardIntegrand F ζ hζ q S P ε s φ.val k h
        (((π ^ 3 : (LocalField F q)ˣ) : LocalField F q)⁻¹ * x)‖)
      (g := fun x => ‖(deltaHalf S.borel (KPRankOneRootParameter.rootCubeLift S.borel π) *
        KPRankOneRootParameter.rootCharacter S.borel (sourceSign ε) (sourceParameter ε s) π)‖ *
        ‖actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x‖)
      (μ := μ) hset (fun x hx => by
        dsimp only
        rw [hM m hm x hx s φ k h, norm_mul])
  rw [he, integral_const_mul]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  have H := congrArg norm (actual_uniformizer_multiplier F ζ hζ q S ε s π hπ)
  rw [norm_mul] at H
  have hq : (0 : ℝ) < residueCardinality (LocalField F q) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (KPCubicUnitIndices.two_le_residueCard (LocalField F q)))
  have hn : ‖(residueCardinality (LocalField F q) : ℂ) ^ 3‖ =
      (residueCardinality (LocalField F q) : ℝ) ^ 3 := by
    rw [norm_pow]
    congr 1
    simp only [Complex.norm_natCast]
  rwa [hn] at H

end DedekindZetaZeroFree.KPRankOneShellRepair

end
