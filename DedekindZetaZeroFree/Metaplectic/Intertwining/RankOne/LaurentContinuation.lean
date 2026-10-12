module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ContinuedOperatorFamilies
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.GlobalContinuationFromLevelIntegrals

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellContinuation
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

include hμ in

theorem actual_integral_integrable_at_level_without_uniformizer
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
      S.iwasawa.compact.toOpenSubgroup)
    (ε : Sign) (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    Integrable (fun x : LocalField F q =>
      ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)
        (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))).val
        (kernelW (LocalField F q) S.borel ε *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h) μ := by
  exact actual_level_integrable_full_cover F ζ hζ q S P μ hμ
    (actualFamilyUniformizer F q) (actualFamilyUniformizer_spec F q) J hJ ε s hs φ g h

end DedekindZetaZeroFree.KPRankOneShellContinuation

end
