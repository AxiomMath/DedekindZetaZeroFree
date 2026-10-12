module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Adeles.PositiveArchimedeanDilation

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.PositiveArchCharacter
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
open KPContinuation.ChamberOutgoingSource

theorem archDiagonalIdele_ideleAbs (u : NumberField.InfinitePlace F → ℝ) :
    (((KPGlobalTorusFunctionData.ideleAbs F (archDiagonalIdele F ζ hζ u) : ℝ≥0) : ℝ)) =
      Real.exp (2 * ∑ w, u w) := by
  let a := archDiagonalIdele F ζ hζ u
  have hf : ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a).2 = 1 := by
    apply (IdeleGroup.finiteEquivFiniteAdeleUnits (K := F)).injective
    apply Units.ext
    have he := congrArg (fun u : KPAdelicCoverRestrictedProduct.Ideles F => u.val.2)
      ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).apply_symm_apply a)
    exact he
  have hw (w : NumberField.InfinitePlace F) :
      ((InfiniteIdeleGroup.component w
        ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a).1 : w.Completionˣ) : w.Completion) =
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (u w) : ℂ) := by
    have he := congrArg (fun u : KPAdelicCoverRestrictedProduct.Ideles F => u.val.1 w)
      ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).apply_symm_apply a)
    exact he
  change (((IdeleGroup.absoluteNorm
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a))⁻¹ : ℝ≥0ˣ) : ℝ) = _
  rw [IdeleGroup.absoluteNorm_apply, hf, map_one, one_mul, inv_inv,
    InfiniteIdeleGroup.archimedeanNorm_apply]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val, nnnormUnitHom_val,
    NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  have hn (w : NumberField.InfinitePlace F) :
      ‖(NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (u w) : ℂ)‖ = Real.exp (u w) := by
    let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have h := e.symm.isometry.dist_eq (Real.exp (u w) : ℂ) 0
    change dist ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (u w) : ℂ))
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm 0) = _ at h
    simpa [Complex.norm_real, abs_of_pos (Real.exp_pos _)] using h
  simp_rw [hw, hn, (KPHilbert.infinite_isComplex F ζ hζ _).mult_eq_two, ← Real.exp_nat_mul]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  simp

end DedekindZetaZeroFree.KPGlobalResidualConstruction.PositiveArchCharacter

end
