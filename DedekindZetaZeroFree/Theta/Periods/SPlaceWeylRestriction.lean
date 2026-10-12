module

public import DedekindZetaZeroFree.Theta.Digits.AdelicPlaceDecomposition

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_rationalUnit → eval_rationalUnit
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

abbrev sDiagonalTuple (y : R.A.G) :=
  KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R y)

theorem sRestriction_diagonal (y : R.A.G) :
    sRestriction R (sDiagonalTuple R y) = sDiagonalTuple R y := by
  apply RestrictedProduct.ext
  intro w
  simp only [sRestriction, restrictTuple_eval, Set.mem_compl_iff]
  by_cases hw : w ∈ exteriorPlaces R
  · rw [if_neg (not_not.mpr hw)]
    obtain ⟨p, rfl⟩ := hw
    exact (sDiagonal_exterior R y p.val p.property).symm
  · rw [if_pos hw]

theorem sRestriction_rational (x : Fˣ) :
    sRestriction R (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom x)) = sDiagonalTuple R (R.A.diagonal x) := by
  apply RestrictedProduct.ext
  intro w
  cases w with
  | inl w =>
    simp only [sRestriction, restrictTuple_eval, Set.mem_compl_iff, exteriorPlaces_arch, if_true]
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _
    have hr := eval_rationalUnit F (Sum.inl w) x
    have hs := DigitMasks.localIdele_arch R (R.A.diagonal x) w
    exact congrArg (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)) (hr.trans hs.symm)
  | inr p =>
    by_cases hp : p ∈ R.A.Sf
    · simp only [sRestriction, restrictTuple_eval, Set.mem_compl_iff, exteriorPlaces_finite, not_not, hp, if_true]
      change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) _ =
        KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) _
      have hr := eval_rationalUnit F (Sum.inr p) x
      have hs := DigitMasks.localIdele_finite R (R.A.diagonal x) p hp
      exact congrArg (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) (hr.trans hs.symm)
    · simp only [sRestriction, restrictTuple_eval, Set.mem_compl_iff, exteriorPlaces_finite, not_not, hp, if_false]
      exact (sDiagonal_exterior R (R.A.diagonal x) p hp).symm

theorem sRestriction_weyl :
    sRestriction R (KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12) = sWeylTuple R := by
  apply RestrictedProduct.ext
  intro w
  cases w with
  | inl w => simp [sRestriction, sWeylTuple]
  | inr p => simp [sRestriction, sWeylTuple]

theorem sRestriction_digit (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    sRestriction R (KPRationalAdelicSplitting.NTuple F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d)) = 1 := by
  apply RestrictedProduct.ext
  intro w
  cases w with
  | inl w =>
    simp only [sRestriction, restrictTuple_eval, Set.mem_compl_iff, exteriorPlaces_arch, if_true]
    change KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ = 1
    rw [DigitMasks.digitParameter_arch, KPStandardLocalRootLifts.N_zero]
  | inr p =>
    by_cases hp : p ∈ R.A.Sf
    · simp only [sRestriction, restrictTuple_eval, Set.mem_compl_iff, exteriorPlaces_finite, not_not, hp, if_true]
      change KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) _ = 1
      rw [DigitMasks.digitParameter_S R m d p hp, KPStandardLocalRootLifts.N_zero]
    · simp [sRestriction, hp]

theorem sReverseTuple_eq (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    sRestriction R (reverseTuple R x y m d) =
      sDiagonalTuple R (R.A.diagonal x) * sWeylTuple R * sDiagonalTuple R y := by
  simp only [reverseTuple, map_mul, sRestriction_rational, sRestriction_weyl,
    sRestriction_diagonal, sRestriction_digit, mul_one, mul_assoc]

theorem tuples_commute_of_disjoint
    (a b : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (h : ∀ w, a w = 1 ∨ b w = 1) : Commute a b := by
  change a * b = b * a
  apply RestrictedProduct.ext
  intro w
  rw [RestrictedProduct.mul_apply, RestrictedProduct.mul_apply]
  rcases h w with h | h <;> simp [h]

theorem exteriorWeyl_commute_diagonal (y : R.A.G) :
    Commute (exteriorWeylTuple R) (sDiagonalTuple R y) := by
  apply tuples_commute_of_disjoint
  intro w
  cases w with
  | inl w => left; simp [exteriorWeylTuple, sWeylTuple]
  | inr p =>
    by_cases hp : p ∈ R.A.Sf
    · left; simp [exteriorWeylTuple, sWeylTuple, hp]
    · right; exact sDiagonal_exterior R y p hp

theorem sReverseTuple_period {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    fourier R Q.dq (T.theta v) (restrictedLift R (sRestriction R (reverseTuple R x y m d))) =
      fourier R Q.dq (T.theta v)
        (diagonal R (R.A.diagonal x) * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y) := by
  rw [sReverseTuple_eq, map_mul, map_mul]
  have hW : KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12 =
      sWeylTuple R * exteriorWeylTuple R := by simp [exteriorWeylTuple]
  have hc := (exteriorWeyl_commute_diagonal R y).map (restrictedLift R)
  have he : diagonal R (R.A.diagonal x) * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y =
      (restrictedLift R (sDiagonalTuple R (R.A.diagonal x)) * restrictedLift R (sWeylTuple R) *
        restrictedLift R (sDiagonalTuple R y)) * restrictedLift R (exteriorWeylTuple R) := by
    change restrictedLift R (sDiagonalTuple R (R.A.diagonal x)) *
      restrictedLift R (KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12) *
      restrictedLift R (sDiagonalTuple R y) = _
    rw [hW, map_mul, mul_assoc, mul_assoc, hc.eq, ← mul_assoc, ← mul_assoc]
  rw [he]
  symm
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← mul_assoc]
  have h := DigitMasks.theta_full_exterior R T v (exteriorWeylTuple R) (exteriorWeylTuple_mem R)
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
      (restrictedLift R (sDiagonalTuple R (R.A.diagonal x)) * restrictedLift R (sWeylTuple R) * restrictedLift R (sDiagonalTuple R y)))
  exact congrArg (fun z : ℂ => z * star (adelicTraceQuotientCharacter F q : ℂ)) h

end DedekindZetaZeroFree.OrbitExpansion

end
