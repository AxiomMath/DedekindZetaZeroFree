module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.FiniteLevelLaurentNumerator

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
  (P : Polarization S.heisenberg)
  (J : CompactOpenLevel (ActualCover F ζ hζ q))
  (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
  (ε : Sign)

def actualContinuedLevel (s : ℂ) :
    compactLevel S.borel P S.iwasawa (sourceSign ε) J →ₗ[ℂ]
      compactLevel S.borel P S.iwasawa (targetSign ε) J :=
  continuedLevel (LocalField F q) S.borel P S.iwasawa J ε
    (actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε) s

theorem actualContinuedLevel_eq_integral (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    ((actualContinuedLevel F ζ hζ q S P J hJ μ hμ π hπ ε s φ).val.val k).val h =
      standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ.val k h :=
  continuedLevel_eq_integral_of_convergence (LocalField F q) S.borel P S.iwasawa J μ ε
    (actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε)
    (actualLevelNumerator_spec F ζ hζ q S P J hJ μ hμ π hπ ε) s hs φ k h

theorem actualLevelNumerator_unique
    (p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε)
    (hp : IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J μ ε p) :
    p = actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε :=
  level_numerator_unique (LocalField F q) S.borel P S.iwasawa J μ ε p _ hp
    (actualLevelNumerator_spec F ζ hζ q S P J hJ μ hμ π hπ ε)

end DedekindZetaZeroFree.KPRankOneShellRepair

end
