module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ScalarNumeratorLinearity

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
  (ε : Sign)

include hJ in

theorem actual_standard_integrand_right_level (s : ℂ)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (j : J.toOpenSubgroup) (k k' : S.iwasawa.compact.toOpenSubgroup)
    (hk : (k' : ActualCover F ζ hζ q) = k * j)
    (h : actualTorus F ζ hζ q) (x : LocalField F q) :
    actualStandardIntegrand F ζ hζ q S P ε s φ.val k' h x =
      actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x := by
  let f := compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ.val
  have hf := (compact_level_identification S.borel P S.iwasawa (sourceSign ε) J hJ
    (sourceParameter ε s) φ.val).mp φ.property
  have he := congrArg Subtype.val (hf j)
  have hx := congrFun he (kernelW (LocalField F q) S.borel ε *
    (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * k)
  change _ = f.val _ at hx
  simpa [actualStandardIntegrand, f, hk, principalSeries, vectorRightTranslation, mul_assoc] using
    congrArg (fun V : InducedModule P => V.val h) hx

include hJ in

theorem actual_standard_integral_right_level
    (μ : Measure (LocalField F q)) (s : ℂ)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (j : J.toOpenSubgroup) (k k' : S.iwasawa.compact.toOpenSubgroup)
    (hk : (k' : ActualCover F ζ hζ q) = k * j) (h : actualTorus F ζ hζ q) :
    standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ.val k' h =
      standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ.val k h := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (actual_standard_integrand_right_level F ζ hζ q S P J hJ ε s φ j k k' hk h)

theorem actual_scalar_numerator_right_level
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (j : J.toOpenSubgroup) (k k' : S.iwasawa.compact.toOpenSubgroup)
    (hk : (k' : ActualCover F ζ hζ q) = k * j) (h : actualTorus F ζ hζ q) :
    actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k' h =
      actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h := by
  apply KPTameTransposeUnitNumeratorSteps.Augmentation.scalar_laurent_chamber_unique (LocalField F q) ε
  intro s hs
  have h1 := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k' h) s hs
  have h2 := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k h) s hs
  rw [actual_standard_integral_right_level F ζ hζ q S P J hJ ε μ s φ j k k' hk h] at h1
  exact h1.symm.trans h2

end DedekindZetaZeroFree.KPRankOneShellRepair

end
