module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TranslatedLaurentSections
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ConvergenceChamberUniqueness

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
  (ε : Sign)

theorem actualContinued_section_intertwines (s : ℂ)
    (hs : denominator (LocalField F q) ε s ≠ 0)
    (g : ActualCover F ζ hζ q)
    (f : sectionSpace S.borel P (sourceSign ε) (sourceParameter ε s)) :
    transportToSections (LocalField F q) S.borel P S.iwasawa ε s
        (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
      (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g f) =
    principalSeries S.borel P (targetSign ε) (targetParameter ε s) g
      (transportToSections (LocalField F q) S.borel P S.iwasawa ε s
        (actualContinued F ζ hζ q S P μ hμ π hπ ε s) f) := by
  let φ := (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)).symm f
  apply Subtype.ext
  funext x
  apply Subtype.ext
  funext h
  have hL := KPRankOneTranslatedMeromorphy.translated_continued_section_regular
    F ζ hζ q S P μ hμ π hπ ε φ g x h
  have hR := KPRankOneTranslatedMeromorphy.continued_section_regular
    F ζ hζ q S P μ hμ π hπ ε φ (x * g) h
  have he := KPRankOneChamberUniqueness.chamber_identity_value ε hL.1 hR.1
    (fun t ht => congrArg (fun u => (u.val x).val h)
      (actualContinued_section_intertwines_chamber F ζ hζ q S P μ hμ π hπ ε t ht g
        (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε t) φ)))
    s (hL.2 s hs) (hR.2 s hs)
  change ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
    (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
    (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g f)).val x).val h =
    ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
      (actualContinued F ζ hζ q S P μ hμ π hπ ε s) f).val (x * g)).val h
  simpa only [φ, LinearEquiv.apply_symm_apply] using he

end DedekindZetaZeroFree.KPRankOneShellRepair

end
