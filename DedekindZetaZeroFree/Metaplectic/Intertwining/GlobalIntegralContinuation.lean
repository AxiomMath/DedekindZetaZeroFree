module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.NormalizedLevelNumerator
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.LaurentContinuation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneActualShellCaller
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

include hμ in
 theorem integral_integrable_at_level
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (ε : Sign) (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    Integrable (fun x : LocalField F q =>
      ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)
        (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))).val
        (kernelW (LocalField F q) S.borel ε *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h) μ := by
  exact actual_integral_integrable_at_level_without_uniformizer F ζ hζ q S P μ hμ J hJ ε s hs φ g h

include hμ in
 theorem existsUnique_level_numerator
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (ε : Sign) :
    ∃! p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε,
      IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J μ ε p := by
  exact ⟨actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ ε,
    actualCanonicalLevelNumerator_spec F ζ hζ q S P J hJ μ hμ ε,
    fun p hp => actualCanonicalLevelNumerator_unique
      F ζ hζ q S P J hJ μ hμ ε p hp⟩

include hμ in
 theorem exists_global_intertwining_continuation :
    ∃ B : ∀ (ε : Sign) (_s : ℂ),
        compactPicture S.borel P S.iwasawa (sourceSign ε) →ₗ[ℂ]
          compactPicture S.borel P S.iwasawa (targetSign ε),
      ∀ (ε : Sign) (s : ℂ), denominator (LocalField F q) ε s ≠ 0 →
        (∀ (J : CompactOpenLevel (ActualCover F ζ hζ q))
          (_hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
          (p : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε),
          IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J μ ε p →
          ∀ (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J),
            B ε s (φ : compactPicture S.borel P S.iwasawa (sourceSign ε)) =
              (continuedLevel (LocalField F q) S.borel P S.iwasawa J ε p s φ :
                compactPicture S.borel P S.iwasawa (targetSign ε))) ∧
        (∀ (g : ActualCover F ζ hζ q)
          (f : sectionSpace S.borel P (sourceSign ε) (sourceParameter ε s)),
          transportToSections (LocalField F q) S.borel P S.iwasawa ε s (B ε s)
            (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g f) =
          principalSeries S.borel P (targetSign ε) (targetParameter ε s) g
            (transportToSections (LocalField F q) S.borel P S.iwasawa ε s (B ε s) f)) := by
  refine ⟨KPRankOneShellRepair.actualCanonicalContinued F q ζ hζ S P μ hμ, ?_⟩
  intro ε s hs
  constructor
  · intro J hJ p hp φ
    rw [actualCanonicalLevelNumerator_unique
      F ζ hζ q S P J hJ μ hμ ε p hp]
    exact KPRankOneShellRepair.actualCanonicalContinued_eq_level
      F q ζ hζ S P μ hμ ε s J hJ φ
  · exact KPRankOneShellRepair.actualCanonicalContinued_intertwines
      F q ζ hζ S P μ hμ ε s hs

end DedekindZetaZeroFree.KPRankOneActualShellCaller

end
