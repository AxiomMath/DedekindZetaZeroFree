module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.FiniteLevelLaurentNumerator

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellContinuation
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)
  (P : Polarization S.heisenberg)
  (J : CompactOpenLevel (ActualCover F ζ hζ q))
  (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ε : Sign)

 theorem exists_uniformizer : ∃ π : (LocalField F q)ˣ,
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  obtain ⟨x, hx⟩ := valuation_surjective (K := LocalField F q) (e.symm (WithZero.exp (-1 : ℤ)))
  have hv : valuation (LocalField F q) x ≠ 0 := by
    rw [hx]
    exact (map_ne_zero e.symm).mpr (by simp)
  have hxn : x ≠ 0 := by
    intro h
    exact hv (by simp [h])
  refine ⟨Units.mk0 x hxn, ?_⟩
  change e (valuation (LocalField F q) x) = _
  rw [hx, e.apply_symm_apply]

def actualCanonicalLevelNumerator :
    LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε :=
  actualLevelNumerator F ζ hζ q S P J hJ μ hμ
    (exists_uniformizer F q).choose (exists_uniformizer F q).choose_spec ε

theorem actualCanonicalLevelNumerator_spec :
    IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J μ ε
      (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ ε) :=
  actualLevelNumerator_spec F ζ hζ q S P J hJ μ hμ
    (exists_uniformizer F q).choose (exists_uniformizer F q).choose_spec ε

theorem actualCanonicalLevelNumerator_eq_actual
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ ε =
      actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε :=
  level_numerator_unique (LocalField F q) S.borel P S.iwasawa J μ ε _ _
    (actualCanonicalLevelNumerator_spec F ζ hζ q S P J hJ μ hμ ε)
    (actualLevelNumerator_spec F ζ hζ q S P J hJ μ hμ π hπ ε)

theorem actualCanonicalLevelNumerator_unique
    (p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε)
    (hp : IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J μ ε p) :
    p = actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ ε :=
  level_numerator_unique (LocalField F q) S.borel P S.iwasawa J μ ε p _ hp
    (actualCanonicalLevelNumerator_spec F ζ hζ q S P J hJ μ hμ ε)

end DedekindZetaZeroFree.KPRankOneShellContinuation

end
