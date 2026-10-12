module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.MeromorphicGroupEquivariance

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
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))

include hμ π hπ in

theorem actual_exists_global_intertwining_continuation :
    ∃ B : ∀ (ε : Sign) (s : ℂ),
        compactPicture S.borel P S.iwasawa (sourceSign ε) →ₗ[ℂ]
          compactPicture S.borel P S.iwasawa (targetSign ε),
      ∀ (ε : Sign) (s : ℂ), denominator (LocalField F q) ε s ≠ 0 →
        (∀ (J : CompactOpenLevel (ActualCover F ζ hζ q))
          (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
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
  refine ⟨fun ε s => actualContinued F ζ hζ q S P μ hμ π hπ ε s, ?_⟩
  intro ε s hs
  constructor
  · intro J hJ p hp φ
    rw [actualLevelNumerator_unique F ζ hζ q S P J hJ μ hμ π hπ ε p hp]
    exact actualContinued_eq_level F ζ hζ q S P μ hμ π hπ ε s J hJ φ
  · exact actualContinued_section_intertwines F ζ hζ q S P μ hμ π hπ ε s hs
end DedekindZetaZeroFree.KPRankOneShellContinuation

end

section

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
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
include hμ π hπ in

theorem actual_level_integrable_full_cover
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
  exact actual_section_integrable F ζ hζ q S P μ hμ π hπ ε s hs _ g h

end DedekindZetaZeroFree.KPRankOneShellContinuation

end
end
