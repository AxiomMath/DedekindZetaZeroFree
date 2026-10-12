module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.LaurentCoefficientSections

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

 def coefficientSection
    (n : ℤ) (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
    compactLevel S.borel P S.iwasawa (targetSign ε) J :=
  (actual_scalar_coefficients_target_level F ζ hζ q S P J hJ μ hμ π hπ ε φ n).choose

 theorem coefficientSection_coordinate
    (n : ℤ) (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    ((coefficientSection F ζ hζ q S P J hJ μ hμ π hπ ε n φ).val.val k).val h =
      actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h n :=
  (actual_scalar_coefficients_target_level F ζ hζ q S P J hJ μ hμ π hπ ε φ n).choose_spec k h

def actualCoefficientOperator (n : ℤ) :
    compactLevel S.borel P S.iwasawa (sourceSign ε) J →ₗ[ℂ]
      compactLevel S.borel P S.iwasawa (targetSign ε) J where
  toFun := coefficientSection F ζ hζ q S P J hJ μ hμ π hπ ε n
  map_add' φ ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Subtype.ext
    funext h
    change ((coefficientSection F ζ hζ q S P J hJ μ hμ π hπ ε n (φ + ψ)).val.val k).val h =
      ((coefficientSection F ζ hζ q S P J hJ μ hμ π hπ ε n φ).val.val k).val h +
      ((coefficientSection F ζ hζ q S P J hJ μ hμ π hπ ε n ψ).val.val k).val h
    simp only [coefficientSection_coordinate]
    exact congrArg (fun r : ℤ →₀ ℂ => r n)
      ((actual_scalar_numerator_linear F ζ hζ q S P J hJ μ hμ π hπ ε k h).map_add φ ψ)
  map_smul' c φ := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Subtype.ext
    funext h
    change ((coefficientSection F ζ hζ q S P J hJ μ hμ π hπ ε n (c • φ)).val.val k).val h =
      c * ((coefficientSection F ζ hζ q S P J hJ μ hμ π hπ ε n φ).val.val k).val h
    simp only [coefficientSection_coordinate]
    exact congrArg (fun r : ℤ →₀ ℂ => r n)
      ((actual_scalar_numerator_linear F ζ hζ q S P J hJ μ hμ π hπ ε k h).map_smul c φ)

theorem actualCoefficientOperator_coordinate
    (n : ℤ) (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    ((actualCoefficientOperator F ζ hζ q S P J hJ μ hμ π hπ ε n φ).val.val k).val h =
      actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h n :=
  coefficientSection_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε n φ k h

end DedekindZetaZeroFree.KPRankOneShellRepair

end
