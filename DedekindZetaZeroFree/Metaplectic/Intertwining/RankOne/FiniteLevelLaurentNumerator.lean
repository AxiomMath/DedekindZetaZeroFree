module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.LaurentCoefficientFiniteSupport

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

def actualLevelNumerator : LevelLaurentOperator (LocalField F q) S.borel P S.iwasawa J ε :=
  Finsupp.ofSupportFinite (actualCoefficientOperator F ζ hζ q S P J hJ μ hμ π hπ ε)
    (actualCoefficientOperator_finite_support F ζ hζ q S P J hJ μ hμ π hπ ε)

theorem actualLevelNumerator_coordinate
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    Finsupp.mapRange
      (fun M : compactLevel S.borel P S.iwasawa (sourceSign ε) J →ₗ[ℂ]
          compactLevel S.borel P S.iwasawa (targetSign ε) J => (M φ).val.val k |>.val h)
      (by rfl) (actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε) =
      actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h := by
  apply Finsupp.ext
  intro n
  exact actualCoefficientOperator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε n φ k h

theorem actualLevelNumerator_spec :
    IsLevelNumerator (LocalField F q) S.borel P S.iwasawa J μ ε
      (actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε) := by
  intro s hs φ k h
  let l : (compactLevel S.borel P S.iwasawa (sourceSign ε) J →ₗ[ℂ]
      compactLevel S.borel P S.iwasawa (targetSign ε) J) →ₗ[ℂ] ℂ :=
    { toFun := fun M => (M φ).val.val k |>.val h
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hc := actualLevelNumerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k h
  have he := congrArg (fun p : ℤ →₀ ℂ => p.sum
    (fun n c => (evaluationUnit (LocalField F q) ε s : ℂ) ^ n * c)) hc
  rw [Finsupp.sum_mapRange_index (by intros; simp)] at he
  have hm : l (evaluate (LocalField F q) S.borel P S.iwasawa J ε
      (actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε)
      (evaluationUnit (LocalField F q) ε s)) =
      (actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε).sum
        (fun n M => (evaluationUnit (LocalField F q) ε s : ℂ) ^ n * l M) := by
    simp [evaluate, Finsupp.sum, map_sum, map_smul, smul_eq_mul]
  change l (evaluate (LocalField F q) S.borel P S.iwasawa J ε
    (actualLevelNumerator F ζ hζ q S P J hJ μ hμ π hπ ε)
    (evaluationUnit (LocalField F q) ε s)) = _
  rw [hm]
  exact he.trans (Classical.choose_spec
    (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k h) s hs).symm

end DedekindZetaZeroFree.KPRankOneShellRepair

end
