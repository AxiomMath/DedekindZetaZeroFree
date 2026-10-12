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

 def forwardIntegralContinuationLinearWitness :
    sectionSpace S.borel P .plus 0 →ₗ[ℂ] sectionSpace S.borel P .minus 0 :=
  (compactTrivialization S.borel P S.iwasawa .minus 0).toLinearMap.comp
    ((actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0).comp
      (compactTrivialization S.borel P S.iwasawa .plus 0).symm.toLinearMap)

private theorem forwardIntegralContinuationLinearWitness_intertwines
    (g : ActualCover F ζ hζ q) (f : sectionSpace S.borel P .plus 0) :
    forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ (IPlus S.borel P g f) =
      IMinus S.borel P g
        (forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ f) := by
  have H := actualCanonicalContinued_intertwines F q ζ hζ S P μ hμ .plus 0
    (denominator_ne_zero_at_zero (LocalField F q) .plus) g f
  apply Subtype.ext
  funext x
  apply Subtype.ext
  funext h
  have he := congrArg (fun u => (u.val x).val h) H
  change (inducingAction S.borel P .minus (-0) (S.iwasawa.borelPart x)
    (((actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0)
      ((compactTrivialization S.borel P S.iwasawa .plus 0).symm (IPlus S.borel P g f))).val
        (S.iwasawa.compactPart x))).val h =
    (inducingAction S.borel P .minus (-0) (S.iwasawa.borelPart (x * g))
      (((actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0)
        ((compactTrivialization S.borel P S.iwasawa .plus 0).symm f)).val
          (S.iwasawa.compactPart (x * g)))).val h at he
  change (inducingAction S.borel P .minus 0 (S.iwasawa.borelPart x)
    (((actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0)
      ((compactTrivialization S.borel P S.iwasawa .plus 0).symm (IPlus S.borel P g f))).val
        (S.iwasawa.compactPart x))).val h =
    (inducingAction S.borel P .minus 0 (S.iwasawa.borelPart (x * g))
      (((actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0)
        ((compactTrivialization S.borel P S.iwasawa .plus 0).symm f)).val
          (S.iwasawa.compactPart (x * g)))).val h
  simpa only [neg_zero] using he

 theorem forwardIntegralContinuationLinearWitness_eq_integral
    (f : sectionSpace S.borel P .plus 0)
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    ((forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ f).val g).val h =
      ∫ x : LocalField F q,
        (f.val (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h ∂μ := by
  have H := actualContinued_section_eq_integral F ζ hζ q S P μ hμ
    (actualFamilyUniformizer F q) (actualFamilyUniformizer_spec F q) .plus 0
    (by norm_num [convergenceHalfPlane]) f g h
  change (inducingAction S.borel P .minus (-0) (S.iwasawa.borelPart g)
    (((actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0)
      ((compactTrivialization S.borel P S.iwasawa .plus 0).symm f)).val
        (S.iwasawa.compactPart g))).val h = _ at H
  rw [neg_zero] at H
  exact H

def actualCanonicalForwardLinear :
    sectionSpace S.borel P .plus 0 →ₗ[ℂ] sectionSpace S.borel P .minus 0 where
  toFun f :=
    ⟨fun g => ⟨fun h => ∫ x : LocalField F q,
      (f.val (S.borel.liftedW⁻¹ *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h ∂μ, by
      have he := funext (fun h =>
        (forwardIntegralContinuationLinearWitness_eq_integral F ζ hζ q S P μ hμ
          f g h).symm)
      rw [he]
      exact ((forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ f).val g).property⟩, by
      convert (forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ f).property using 1
      funext g
      apply Subtype.ext
      funext h
      exact (forwardIntegralContinuationLinearWitness_eq_integral F ζ hζ q S P μ hμ
        f g h).symm⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext h
    have he := congrArg
      (fun u : sectionSpace S.borel P .minus 0 => (u.val g).val h)
      (map_add (forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ) f₁ f₂)
    change ((forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ (f₁ + f₂)).val g).val h =
      ((forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ f₁).val g).val h +
        ((forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ f₂).val g).val h at he
    change _ =
      (∫ x : LocalField F q,
        (f₁.val (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h ∂μ) +
      (∫ x : LocalField F q,
        (f₂.val (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h ∂μ)
    simpa only [forwardIntegralContinuationLinearWitness_eq_integral] using he
  map_smul' c f := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext h
    have he := congrArg
      (fun u : sectionSpace S.borel P .minus 0 => (u.val g).val h)
      (map_smul (forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ) c f)
    change ((forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ (c • f)).val g).val h =
      c • ((forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ f).val g).val h at he
    change _ = c •
      (∫ x : LocalField F q,
        (f.val (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h ∂μ)
    simpa only [forwardIntegralContinuationLinearWitness_eq_integral] using he

theorem forwardIntegralLinear_eq_continuationWitness :
    actualCanonicalForwardLinear F ζ hζ q S P μ hμ =
      forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  apply Subtype.ext
  funext h
  exact (forwardIntegralContinuationLinearWitness_eq_integral F ζ hζ q S P μ hμ
    f g h).symm

theorem actualCanonicalForwardLinear_intertwines
    (g : ActualCover F ζ hζ q) (f : sectionSpace S.borel P .plus 0) :
    actualCanonicalForwardLinear F ζ hζ q S P μ hμ (IPlus S.borel P g f) =
      IMinus S.borel P g (actualCanonicalForwardLinear F ζ hζ q S P μ hμ f) := by
  simpa only [forwardIntegralLinear_eq_continuationWitness] using
    forwardIntegralContinuationLinearWitness_intertwines F ζ hζ q S P μ hμ g f

def actualCanonicalForwardMap : (IPlus S.borel P).IntertwiningMap (IMinus S.borel P) where
  toLinearMap := actualCanonicalForwardLinear F ζ hζ q S P μ hμ
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    exact actualCanonicalForwardLinear_intertwines F ζ hζ q S P μ hμ g f

theorem actualCanonicalForwardMap_eq_integral
    (f : sectionSpace S.borel P .plus 0)
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    ((actualCanonicalForwardMap F ζ hζ q S P μ hμ f).val g).val h =
      ∫ x : LocalField F q,
        (f.val (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h ∂μ := by
  rfl

include hμ in

theorem actualCanonicalForwardMap_integrable
    (f : sectionSpace S.borel P .plus 0)
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    Integrable (fun x : LocalField F q =>
      (f.val (S.borel.liftedW⁻¹ *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * g)).val h) μ := by
  exact actualCanonicalContinued_integrable F q ζ hζ S P μ hμ .plus 0
    (by norm_num [convergenceHalfPlane]) f g h

end DedekindZetaZeroFree.KPRankOneShellRepair

end
