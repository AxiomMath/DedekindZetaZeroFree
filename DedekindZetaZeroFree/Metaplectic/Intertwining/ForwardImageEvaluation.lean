module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ForwardIntegralOperator
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PrincipalSeries.OpenBruhatCellTestVectors

@[expose] public section

noncomputable section
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

theorem actualCanonicalForwardMap_evaluation_one_surjective :
    Function.Surjective (fun f : sectionSpace S.borel P .plus 0 ↦
      (actualCanonicalForwardMap F ζ hζ q S P μ hμ f).val 1) := by
  intro v
  obtain ⟨f, _, hf⟩ :=
    KPRankOneForwardTestVector.ActualSource.integer_open_cell_section F ζ hζ q S P v
  refine ⟨f, ?_⟩
  apply Subtype.ext
  funext t
  rw [actualCanonicalForwardMap_eq_integral]
  have he : (fun x : LocalField F q ↦
      (f.val (S.borel.liftedW⁻¹ *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * 1)).val t) =
      ((valuation (LocalField F q)).integer : Set (LocalField F q)).indicator
        (fun _ ↦ v.val t) := by
    funext x
    rw [mul_one, hf]
    by_cases hx : x ∈ (valuation (LocalField F q)).integer <;> simp [hx]
  rw [he, integral_indicator_const _
    (valuation (LocalField F q)).isOpen_integer.measurableSet]
  simp [Measure.real, hμ]

theorem actualCanonicalForwardMap_evaluation_surjective (g : ActualCover F ζ hζ q) :
    Function.Surjective (fun f : sectionSpace S.borel P .plus 0 ↦
      (actualCanonicalForwardMap F ζ hζ q S P μ hμ f).val g) := by
  intro v
  obtain ⟨f, hf⟩ := actualCanonicalForwardMap_evaluation_one_surjective F ζ hζ q S P μ hμ v
  refine ⟨IPlus S.borel P g⁻¹ f, ?_⟩
  have he := actualCanonicalForwardLinear_intertwines F ζ hζ q S P μ hμ g⁻¹ f
  have he' := congrArg (fun z : sectionSpace S.borel P .minus 0 ↦ z.val g) he
  change (actualCanonicalForwardMap F ζ hζ q S P μ hμ
    (IPlus S.borel P g⁻¹ f)).val g = _ at he'
  change (actualCanonicalForwardLinear F ζ hζ q S P μ hμ f).val 1 = v at hf
  exact he'.trans (by simpa [IMinus, principalSeries, vectorRightTranslation] using hf)

end DedekindZetaZeroFree.KPRankOneShellRepair

end
