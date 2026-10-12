module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ContinuedOperatorFamilies

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

def actualCanonicalReverseLinear :
    sectionSpace S.borel P .minus 0 →ₗ[ℂ] sectionSpace S.borel P .plus 0 :=
  (compactTrivialization S.borel P S.iwasawa .plus 0).toLinearMap.comp
    ((actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0).comp
      (compactTrivialization S.borel P S.iwasawa .minus 0).symm.toLinearMap)

theorem actualCanonicalReverseLinear_intertwines
    (g : ActualCover F ζ hζ q) (f : sectionSpace S.borel P .minus 0) :
    actualCanonicalReverseLinear F ζ hζ q S P μ hμ (IMinus S.borel P g f) =
      IPlus S.borel P g (actualCanonicalReverseLinear F ζ hζ q S P μ hμ f) := by
  let f' : sectionSpace S.borel P (sourceSign .minus) (sourceParameter .minus 0) :=
    ⟨f.val, by simpa [sourceSign, sourceParameter] using f.property⟩
  have H := actualCanonicalContinued_intertwines F q ζ hζ S P μ hμ .minus 0
    (denominator_ne_zero_at_zero (LocalField F q) .minus) g f'
  apply Subtype.ext
  funext x
  apply Subtype.ext
  funext h
  have he := congrArg (fun u => (u.val x).val h) H
  have hp : (compactTrivialization S.borel P S.iwasawa (sourceSign .minus)
      (sourceParameter .minus 0)).symm f' =
      (compactTrivialization S.borel P S.iwasawa .minus 0).symm f := by
    apply Subtype.ext
    funext k
    rfl
  have hg : (compactTrivialization S.borel P S.iwasawa (sourceSign .minus)
      (sourceParameter .minus 0)).symm
      (principalSeries S.borel P (sourceSign .minus) (sourceParameter .minus 0) g f') =
      (compactTrivialization S.borel P S.iwasawa .minus 0).symm (IMinus S.borel P g f) := by
    apply Subtype.ext
    funext k
    rfl
  change (inducingAction S.borel P .plus (targetParameter .minus 0) (S.iwasawa.borelPart x)
    (((actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0)
      ((compactTrivialization S.borel P S.iwasawa (sourceSign .minus) (sourceParameter .minus 0)).symm
        (principalSeries S.borel P (sourceSign .minus) (sourceParameter .minus 0) g f'))).val
          (S.iwasawa.compactPart x))).val h =
    (inducingAction S.borel P .plus (targetParameter .minus 0) (S.iwasawa.borelPart (x * g))
      (((actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0)
        ((compactTrivialization S.borel P S.iwasawa (sourceSign .minus) (sourceParameter .minus 0)).symm f')).val
          (S.iwasawa.compactPart (x * g)))).val h at he
  rw [hp, hg] at he
  have ht : targetParameter .minus (0 : ℂ) = 0 := by norm_num [targetParameter, sourceParameter]
  rw [ht] at he
  exact he

def actualCanonicalReverseMap : (IMinus S.borel P).IntertwiningMap (IPlus S.borel P) where
  toLinearMap := actualCanonicalReverseLinear F ζ hζ q S P μ hμ
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    exact actualCanonicalReverseLinear_intertwines F ζ hζ q S P μ hμ g f

theorem actualCanonicalReverseMap_level
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (φ : compactLevel S.borel P S.iwasawa .minus J) :
    actualCanonicalReverseMap F ζ hζ q S P μ hμ
      (compactTrivialization S.borel P S.iwasawa .minus 0 φ.val) =
      compactTrivialization S.borel P S.iwasawa .plus 0
        (continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus
          (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .minus) 0 φ).val := by
  change compactTrivialization S.borel P S.iwasawa .plus 0
    (actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0
      ((compactTrivialization S.borel P S.iwasawa .minus 0).symm
        (compactTrivialization S.borel P S.iwasawa .minus 0 φ.val))) = _
  rw [LinearEquiv.symm_apply_apply,
    actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .minus 0 J hJ φ]

end DedekindZetaZeroFree.KPRankOneShellRepair

end
