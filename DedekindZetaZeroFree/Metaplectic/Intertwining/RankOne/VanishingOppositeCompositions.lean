module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.RegularPointValues
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OppositeCompositionVanishing

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

private theorem exists_cube_root (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F)) :
    ∃ η : (valuation (LocalField F q)).integer, IsPrimitiveRoot η 3 := by
  have hinj : Function.Injective (algebraMap F (LocalField F q)) :=
    (algebraMap F (LocalField F q)).injective
  let η : LocalField F q := (algebraMap F (LocalField F q) ζ) ^ 4
  have hη : IsPrimitiveRoot η 3 := by
    simpa [η] using (hζ.map_of_injective hinj).pow_of_dvd (p := 4) (by norm_num) (by norm_num)
  have hv : valuation (LocalField F q) η = 1 := by
    have hp : (valuation (LocalField F q) η) ^ 3 = 1 := by
      rw [← map_pow, hη.pow_eq_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le (by decide)).mp hp
  exact ⟨⟨η, hv.le⟩, hη.of_map_of_injective
    (f := (valuation (LocalField F q)).integer.subtype) Subtype.val_injective⟩

 def sourceRaw : KPActualScalarBinding.ActualKPBinding F ζ hζ q where
  D := S.D
  groupD := S.groupD
  finiteD := S.finiteD
  cubeClassEquiv := S.cubeClassEquiv
  heisenberg := S.heisenberg
  borel := S.borel
  borel_eq := S.borel_eq
  torus_full := S.torus_full
  coordinate_lift := S.coordinate_lift
  cube_class := S.cube_class
  center_exact := S.center_exact
  cube_actual := S.cube_actual
  central := S.central
  central_actual := S.central_actual
  central_character := S.central_character
  center_parameterization := S.center_parameterization
  prescribed_center := S.prescribed_center
  split_scalars := S.split_scalars
  polarization := S.polarization
  iwasawa := S.iwasawa
  openCell := S.openCell
  openCell_ordinary := S.openCell_ordinary

set_option backward.isDefEq.respectTransparency false in
private theorem actual_compact_reverse_forward_zero
    (φ : compactPicture S.borel P S.iwasawa .plus) :
    actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0
      (actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0 φ) = 0 := by
  obtain ⟨η, hη⟩ := exists_cube_root F ζ hζ q
  have hR := KPActualScalarBinding.actual_regular_point_output F ζ hζ q
    (sourceRaw F ζ hζ q S) P μ hμ η hη
  obtain ⟨J, hJ, hφ⟩ := actual_common_level F ζ hζ q S P .plus φ
  have hp := actualCanonicalLevelNumerator_spec F ζ hζ q S P J hJ μ hμ .plus
  have hpRev := actualCanonicalLevelNumerator_spec F ζ hζ q S P J hJ μ hμ .minus
  rw [actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .plus 0 J hJ ⟨φ, hφ⟩]
  rw [actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .minus 0 J hJ
    (continuedLevel (LocalField F q) S.borel P S.iwasawa J .plus
      (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .plus) 0 ⟨φ, hφ⟩)]
  have hz := (both_level_compositions_zero (K := LocalField F q) S.borel P S.iwasawa J hJ
    μ hμ η hη hR (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .plus)
    (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .minus) hp hpRev).1
  have hv := LinearMap.congr_fun hz ⟨φ, hφ⟩
  have hv' : (continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus
      (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .minus) 0)
      ((continuedLevel (LocalField F q) S.borel P S.iwasawa J .plus
        (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .plus) 0) ⟨φ, hφ⟩) = 0 := hv
  rw [hv']
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem actual_compact_forward_reverse_zero
    (φ : compactPicture S.borel P S.iwasawa .minus) :
    actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0
      (actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0 φ) = 0 := by
  obtain ⟨η, hη⟩ := exists_cube_root F ζ hζ q
  have hR := KPActualScalarBinding.actual_regular_point_output F ζ hζ q
    (sourceRaw F ζ hζ q S) P μ hμ η hη
  obtain ⟨J, hJ, hφ⟩ := actual_common_level F ζ hζ q S P .minus φ
  have hp := actualCanonicalLevelNumerator_spec F ζ hζ q S P J hJ μ hμ .plus
  have hpRev := actualCanonicalLevelNumerator_spec F ζ hζ q S P J hJ μ hμ .minus
  rw [actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .minus 0 J hJ ⟨φ, hφ⟩]
  rw [actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .plus 0 J hJ
    (continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus
      (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .minus) 0 ⟨φ, hφ⟩)]
  have hz := (both_level_compositions_zero (K := LocalField F q) S.borel P S.iwasawa J hJ
    μ hμ η hη hR (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .plus)
    (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .minus) hp hpRev).2
  have hv := LinearMap.congr_fun hz ⟨φ, hφ⟩
  have hv' : (continuedLevel (LocalField F q) S.borel P S.iwasawa J .plus
      (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .plus) 0)
      ((continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus
        (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .minus) 0) ⟨φ, hφ⟩) = 0 := hv
  rw [hv']
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem actual_zero_opposite_compositions :
    (actualCanonicalForwardMap F ζ hζ q S P μ hμ).toLinearMap.comp
      (actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap = 0 ∧
    (actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap.comp
      (actualCanonicalForwardMap F ζ hζ q S P μ hμ).toLinearMap = 0 := by
  have hforward : (actualCanonicalForwardMap F ζ hζ q S P μ hμ).toLinearMap =
      forwardIntegralContinuationLinearWitness F ζ hζ q S P μ hμ := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext h
    exact (forwardIntegralContinuationLinearWitness_eq_integral F ζ hζ q S P μ hμ
      f g h).symm
  rw [hforward]
  constructor
  · apply LinearMap.ext
    intro f
    change (compactTrivialization S.borel P S.iwasawa .minus 0)
      (actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0
        ((compactTrivialization S.borel P S.iwasawa .plus 0).symm
          ((compactTrivialization S.borel P S.iwasawa .plus 0)
            (actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0
              ((compactTrivialization S.borel P S.iwasawa .minus 0).symm f))))) = 0
    rw [LinearEquiv.symm_apply_apply,
      actual_compact_forward_reverse_zero F ζ hζ q S P μ hμ]
    exact (compactTrivialization S.borel P S.iwasawa .minus 0).map_zero
  · apply LinearMap.ext
    intro f
    change (compactTrivialization S.borel P S.iwasawa .plus 0)
      (actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0
        ((compactTrivialization S.borel P S.iwasawa .minus 0).symm
          ((compactTrivialization S.borel P S.iwasawa .minus 0)
            (actualCanonicalContinued F q ζ hζ S P μ hμ .plus 0
              ((compactTrivialization S.borel P S.iwasawa .plus 0).symm f))))) = 0
    rw [LinearEquiv.symm_apply_apply,
      actual_compact_reverse_forward_zero F ζ hζ q S P μ hμ]
    exact (compactTrivialization S.borel P S.iwasawa .plus 0).map_zero

end DedekindZetaZeroFree.KPRankOneShellRepair

end
