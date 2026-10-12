module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.GaussianKernelMoments
public import DedekindZetaZeroFree.Theta.Periods.UpperPeriodDigitReindexing
public import DedekindZetaZeroFree.Theta.Digits.WeightedQuotientIntegrability
public import DedekindZetaZeroFree.Theta.Periods.WeightedUpperQuotientIntegrability
public import DedekindZetaZeroFree.Theta.Periods.OddUpperAverageVanishing

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources ThetaProfileHaarSheets ThetaSheetExactUnfolding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

namespace QuotientDescent
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem mask_frequency (m : ThetaReflectionData.Row R.A) (a : Fˣ)
    (ha : ∀ p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property,
      p.valuation F (a : F) ≤ 1) :
    (∑ d : Digits R m, digitWeight R m d * (adelicTraceCharacter F
      (algebraMap F (KPAdeles F) (a : F) * digitParameter R m d) : ℂ)) =
    ∏ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
      let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
      sexticUnitPower (ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩)
        (ThetaDigitAverage.rowExponent R.A m.val p.val) (ThetaBranch.unitResidue p.val a) := by
  let P := ThetaDigitAverage.rowPrimes R.A m.val m.property
  let f (p : P) (d : ThetaDigitAverage.Residue p.val) : ℂ :=
    let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
    sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩)
      (Characters.psi R ⟨p.val, hp⟩) (ThetaDigitAverage.rowExponent R.A m.val p.val) d *
      Characters.psi R ⟨p.val, hp⟩ (ThetaBranch.unitResidue p.val a * d)
  have hterm (d : Digits R m) : digitWeight R m d * (adelicTraceCharacter F
      (algebraMap F (KPAdeles F) (a : F) * digitParameter R m d) : ℂ) = ∏ p : P, f p (d p) := by
    rw [selected_digit_phase R m a ha]
    unfold digitWeight
    dsimp only [f]
    rw [← Finset.prod_mul_distrib]
  simp_rw [hterm]
  calc
    _ = ∏ p : P, ∑ d : ThetaDigitAverage.Residue p.val, f p d := (Fintype.prod_sum f).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
      exact sextic_fourier_mask_inversion R ⟨p.val, hp⟩ (ThetaDigitAverage.rowExponent R.A m.val p.val)
        (ThetaBranch.unitResidue p.val a)

theorem theta_descent (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (γ : R.A.Gamma) (y : R.A.G) :
    signedDigits R C.sources C.realization v m b (γ.val * y) =
      signedDigits R C.sources C.realization v m b y := by
  obtain ⟨q, ⟨u, hu, rfl⟩, hq⟩ := γ.property
  let u' : R.A.U := ⟨u, hu⟩
  have hγ : γ.val = R.A.diagonal (u'.val ^ 6) := hq.symm
  rw [hγ]
  unfold signedDigits
  rw [← (digitReindex R m u').sum_comp]
  apply Finset.sum_congr rfl
  intro d _
  rw [digitWeight_reindex, selected_theta_digit_reindex R C]

theorem upper_descent (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (γ : R.A.Gamma) (y : R.A.G) :
    upperDigits R C.sources C.realization v m b (γ.val * y) =
      upperDigits R C.sources C.realization v m b y := by
  obtain ⟨q, ⟨u, hu, rfl⟩, hq⟩ := γ.property
  let u' : R.A.U := ⟨u, hu⟩
  have hγ : γ.val = R.A.diagonal (u'.val ^ 6) := hq.symm
  rw [hγ]
  unfold upperDigits
  rw [← (digitReindex R m u').sum_comp]
  apply Finset.sum_congr rfl
  intro d _
  rw [digitWeight_reindex, (selected_upper_digit_reindex R C v m u' b y d).2]

theorem gamma_class (γ : R.A.Gamma) : QuotientGroup.mk' R.A.sixthPowers γ.val = 1 := by
  obtain ⟨q, ⟨u, hu, rfl⟩, hq⟩ := γ.property
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨R.A.diagonal u, by simpa only [powMonoidHom_apply, map_pow] using hq⟩

theorem branch_gamma (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient) (γ : R.A.Gamma) :
    C.packet.branch v γ.val = 1 := by
  rw [C.packet.branch_global]
  obtain ⟨q, ⟨u, hu, rfl⟩, hq⟩ := γ.property
  have ht : R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id
      (R.A.diagonal (u ^ 6)) = 1 :=
    R.probe.correction.theta_unit ⟨u ^ 6, R.A.U.pow_mem hu 6⟩
  have hp : R.A.H_S (R.A.diagonal (R.probe.unitReps.representative v).val) γ.val = 1 := by
    rw [← R.A.H_S6_on_representatives, gamma_class, map_one]
  have ht' : R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id γ.val = 1 := by
    have he : R.A.diagonal (u ^ 6) = γ.val := hq
    rw [he] at ht
    exact ht
  have hc : (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id γ.val : ℂ) = 1 :=
    congrArg (fun z : Circle => (z : ℂ)) ht'
  rw [hc, hp]
  rw [one_mul]
  change R.σ (1 : F) = 1
  exact map_one R.σ

theorem weighted_theta_descent (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (γ : R.A.Gamma) (y : R.A.G) :
    weightedDigits R C.sources C.realization C.packet v m b (γ.val * y) =
      weightedDigits R C.sources C.realization C.packet v m b y := by
  unfold weightedDigits
  simp only [map_mul, gamma_class, branch_gamma, one_mul, theta_descent]
  rw [one_mul (QuotientGroup.mk' R.A.sixthPowers y)]

theorem weighted_upper_descent (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (γ : R.A.Gamma) (y : R.A.G) :
    weightedUpper R C.sources C.realization C.packet v m b (γ.val * y) =
      weightedUpper R C.sources C.realization C.packet v m b y := by
  unfold weightedUpper
  simp only [map_mul, gamma_class, branch_gamma, one_mul, upper_descent]
  rw [one_mul (QuotientGroup.mk' R.A.sixthPowers y)]

open _root_.DedekindZetaZeroFree.KPLiteralPeriod renaming raw_rationalLift_mk → raw_rationalLift_mk

theorem theta_weyl (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient) (g : Group R) :
    C.realization.theta v (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g) =
      C.realization.theta v g := by
  have h := (C.realization.automorphic v).2.1
    (Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap F)) g
  rw [raw_rationalLift_mk] at h
  change C.realization.theta v (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (KPAdelicCoverRestrictedProduct.rationalSection F R.A.zeta12 R.A.primitive_zeta12
      (KPStandardLocalRootLifts.weylSwap F)) * g) = C.realization.theta v g at h
  simpa only [KPRationalAdelicSplitting.pglW, KPRationalAdelicSplitting.W_rational] using h

theorem weyl (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (y : R.A.G) :
    signedDigits R C.sources C.realization v m true y =
      signedDigits R C.sources C.realization v m false y := by
  simp only [signedDigits, signedArgument, Bool.false_eq_true, if_false, if_true, one_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [mul_assoc, theta_weyl]

theorem quotientUpper_projection (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (l : PositiveAxis) (y : Sheet R.A l) :
    quotientUpper R C.sources C.realization C.packet v m b l (sheetProjection R.A l y) =
      weightedUpper R C.sources C.realization C.packet v m b y.val := by
  unfold quotientUpper
  have h := Quotient.exact (Quotient.out_eq (sheetProjection R.A l y))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  have hv := congrArg Subtype.val hγ
  change γ.val.val * y.val = (Quotient.out (sheetProjection R.A l y)).val at hv
  rw [← hv]
  exact weighted_upper_descent C v m b ⟨γ.val.val, γ.property⟩ _

theorem upperAverage_zero_for_smoothing (C : JointMellinGaussianSources R N) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (l : PositiveAxis)
    (hi : letI := C.transport.groupHaar_isHaar;
      Integrable (quotientUpper R C.sources C.realization C.packet v m b l)
        (sheetQuotientHaar R.A C.packet.v₀ C.transport.groupHaar l)) :
    upperAverage R C.transport C.sources C.realization C.packet v m b l = 0 := by
  letI := C.transport.groupHaar_isHaar
  let t : R.A.G1 := ⟨DedekindZetaZeroFree.IdeleInsertion.infiniteInsertion R.A C.packet.v₀ (-1),
    DedekindZetaZeroFree.IdeleInsertion.norm_insertion_one R C.packet.v₀ (-1) (by simp)⟩
  apply DedekindZetaZeroFree.IdeleInsertion.quotient_integral_zero_of_odd R.A C.packet.v₀
    C.transport.groupHaar l t (quotientUpper R C.sources C.realization C.packet v m b l) hi
  intro y y' hy'
  rw [quotientUpper_projection, quotientUpper_projection, hy']
  exact DedekindZetaZeroFree.IdeleInsertion.weightedUpper_neg_one R C.packet C.constantTerm v m b C.packet.v₀ y.val

def descent_of_jointMellinGaussianSources (C : JointMellinGaussianSources R N) :
    DigitsDescent R C.transport C.sources C.realization C.packet where
  mask_frequency := mask_frequency
  theta_descent := theta_descent C
  upper_descent := upper_descent C
  weighted_theta_descent := weighted_theta_descent C
  weighted_upper_descent := weighted_upper_descent C
  weyl := weyl C
  theta_integrable := selected_theta_quotient_integrable R C (weighted_theta_descent C)
  upper_integrable := selected_upper_quotient_integrable R C (weighted_upper_descent C)
  smoothing_integrable := by
    intro v m b Z hZ
    have hi := selected_upper_quotient_integrable R C (weighted_upper_descent C)
    have hz : (fun t : PositiveAxis => C.packet.kernel t.val *
        upperAverage R C.transport C.sources C.realization C.packet v m b
          ⟨t.val / Z, div_pos t.property hZ⟩) = 0 := by
      funext t
      rw [upperAverage_zero_for_smoothing C v m b _ (hi v m b _), mul_zero]
      rfl
    rw [hz]
    exact integrable_zero _ _ _
end QuotientDescent

theorem weighted_digits_descent (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) (N : TraceHaarTransport R)
    (prior : Nonempty (JointMellinGaussianSources R N)) : Nonempty (JointDigitDescentSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨{ toJointMellinGaussianSources := C, descent := QuotientDescent.descent_of_jointMellinGaussianSources C }⟩

end DedekindZetaZeroFree.ThetaExpansion

end
