module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.FiniteLevelLaurentNumerator

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellContinuation
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
private theorem exists_uniformizer (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : ∃ π : Kˣ,
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hx0 : x ≠ 0 := by
    intro h
    have hh := congrArg e hx
    apply WithZero.exp_ne_zero (a := (-1 : ℤ))
    simpa [h, e] using hh.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  change e (valuation K x) = _
  rw [hx, e.apply_symm_apply]

theorem actual_existsUnique_level_numerator
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (ε : Sign) :
    ∃! p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε,
      IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J μ ε p := by
  obtain ⟨π, hπ⟩ := exists_uniformizer (LocalField F q)
  refine ⟨KPRankOneShellRepair.actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε,
    KPRankOneShellRepair.actualLevelNumerator_spec F ζ hζ q S P J hJ μ hμ π hπ ε, ?_⟩
  intro p hp
  exact level_numerator_unique (LocalField F q) S.borel P S.iwasawa J μ ε p _ hp
    (KPRankOneShellRepair.actualLevelNumerator_spec F ζ hζ q S P J hJ μ hμ π hπ ε)
end DedekindZetaZeroFree.KPRankOneShellContinuation

end
