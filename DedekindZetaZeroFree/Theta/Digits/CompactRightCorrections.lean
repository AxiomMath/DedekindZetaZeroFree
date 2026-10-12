module

public import DedekindZetaZeroFree.Theta.Digits.ExteriorCongruences

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField IsDedekindDomain
open scoped Classical BigOperators
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def diagonalTuple (y : R.A.G) :=
  KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (MomentSources.localIdele R y)

def digitRightTuple (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :=
  (diagonalTuple R (R.A.diagonal (u.val ^ 6) * y) *
    KPRationalAdelicSplitting.NTuple F R.A.zeta12 R.A.primitive_zeta12
      (digitParameter R m (digitReindex R m u d)))⁻¹ *
    KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u.val ^ 6)) *
    (diagonalTuple R y * KPRationalAdelicSplitting.NTuple F R.A.zeta12 R.A.primitive_zeta12
      (digitParameter R m d))

private theorem diagonalTuple_arch (y : R.A.G) (w : InfinitePlace F) :
    diagonalTuple R y (Sum.inl w) =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) (y.1 w) := by
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ = _
  rw [localIdele_arch]
private theorem diagonalTuple_S (y : R.A.G) (p : KPFinitePlace F) (hp : p ∈ R.A.Sf) :
    diagonalTuple R y (Sum.inr p) =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) (y.2 ⟨p, hp⟩) := by
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) _ = _
  rw [localIdele_finite R y p hp]
private theorem diagonalTuple_exterior (y : R.A.G) (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    diagonalTuple R y (Sum.inr p) = 1 := by
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) _ = _
  have he := localIdele_exterior R y p hp
  have he' := congrArg (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) he
  exact he'.trans (KPStandardLocalRootLifts.A_one F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))

private theorem nt_eval (x : KPAdeles F) (w : KPHilbert.Place F) :
    KPRationalAdelicSplitting.NTuple F R.A.zeta12 R.A.primitive_zeta12 x w =
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 w
        (KPAdelicCoverRestrictedProduct.adeleEval F w x) := rfl
private theorem at_eval (x : KPAdelicCoverRestrictedProduct.Ideles F) (w : KPHilbert.Place F) :
    KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 x w =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w
        (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F w) x) := rfl

private theorem rational_eval_pow (u : Fˣ) (w : KPHilbert.Place F) :
    Units.map (KPAdelicCoverRestrictedProduct.adeleEval F w)
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u ^ 6)) =
      (Units.map (algebraMap F (KPHilbert.Completion F w)).toMonoidHom u) ^ 6 := by
  apply Units.ext
  cases w <;> change algebraMap F _ ((u : F) ^ 6) = _ <;> exact map_pow _ _ _

theorem digitRightTuple_arch (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) (w : InfinitePlace F) :
    digitRightTuple R m u y d (Sum.inl w) = 1 := by
  unfold digitRightTuple
  simp only [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, nt_eval, at_eval]
  rw [diagonalTuple_arch, diagonalTuple_arch, digitParameter_arch, digitParameter_arch,
    KPStandardLocalRootLifts.N_zero, mul_one, mul_one, rational_eval_pow]
  have hd : (R.A.diagonal (u.val ^ 6) * y).1 w =
      (Units.map (algebraMap F w.Completion).toMonoidHom u.val) ^ 6 * y.1 w := by
    exact congrArg (fun z => z * y.1 w) (map_pow _ _ _)
  rw [hd, local_A_pow_six_mul]
  group

theorem digitRightTuple_S (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : KPFinitePlace F) (hp : p ∈ R.A.Sf) :
    digitRightTuple R m u y d (Sum.inr p) = 1 := by
  unfold digitRightTuple
  simp only [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, nt_eval, at_eval]
  rw [diagonalTuple_S R _ p hp, diagonalTuple_S R _ p hp,
    digitParameter_S R _ _ p hp, digitParameter_S R _ _ p hp,
    KPStandardLocalRootLifts.N_zero, mul_one, mul_one, rational_eval_pow]
  have hd : (R.A.diagonal (u.val ^ 6) * y).2 ⟨p, hp⟩ =
      (Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom u.val) ^ 6 * y.2 ⟨p, hp⟩ := by
    exact congrArg (fun z => z * y.2 ⟨p, hp⟩) (map_pow _ _ _)
  rw [hd, local_A_pow_six_mul]
  group

theorem digitRightTuple_exterior (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    digitRightTuple R m u y d (Sum.inr p) ∈ exteriorFactor R (Sum.inr p) := by
  unfold digitRightTuple
  simp only [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, nt_eval, at_eval]
  rw [diagonalTuple_exterior R _ p hp, diagonalTuple_exterior R _ p hp, one_mul, one_mul,
    rational_eval_pow]
  simp only [exteriorFactor, dif_pos hp]
  have hu := exteriorUnit_inclusion R p hp u
  have hu' : KPTameCompact.unitInclusion F p (exteriorUnit R p hp u) =
      Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom u.val := hu
  rw [← hu']
  apply ThetaForwardQuotientMeasurability.MatrixConstruction.root_torus_sixth_mem_kStar
  rw [hu']
  exact digitParameter_congruence R m u d p

theorem digitRightTuple_mem (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    ∀ w, digitRightTuple R m u y d w ∈ exteriorFactor R w := by
  intro w
  cases w with
  | inl w => exact (Subgroup.mem_bot).mpr (digitRightTuple_arch R m u y d w)
  | inr p =>
    by_cases hp : p ∉ R.A.Sf
    · exact digitRightTuple_exterior R m u y d p hp
    · simp only [exteriorFactor, dif_neg hp, Subgroup.mem_bot]
      exact digitRightTuple_S R m u y d p (not_not.mp hp)

def digitRight (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) : Group R :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12
      (digitRightTuple R m u y d))

theorem signedArgument_reindex_true (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    signedArgument R m true (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d) =
      KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u.val ^ 6)) *
        signedArgument R m true y d * (digitRight R m u y d)⁻¹ := by
  have ht : digitRight R m u y d =
      (signedArgument R m true (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d))⁻¹ *
        KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
          (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u.val ^ 6)) *
        signedArgument R m true y d := by
    unfold digitRight digitRightTuple
    simp only [map_mul, map_inv]
    simp only [signedArgument, if_true, one_mul, diagonal, diagonalTuple,
      KPRationalAdelicSplitting.pglA, KPRationalAdelicSplitting.A,
      KPRationalAdelicSplitting.pglN, KPRationalAdelicSplitting.N]
  rw [ht]
  group

theorem signedArgument_reindex_false (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    signedArgument R m false (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d) =
      KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u.val ^ 6)⁻¹) *
        signedArgument R m false y d * (digitRight R m u y d)⁻¹ := by
  have he (z : R.A.G) (e : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
      signedArgument R m false z e =
        KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * signedArgument R m true z e := by
    simp only [signedArgument, Bool.false_eq_true, if_false, if_true, one_mul, mul_assoc]
  rw [he, signedArgument_reindex_true, ← mul_assoc, ← mul_assoc,
    KPRationalAdelicSplitting.quotient_weyl_diagonal, he, map_inv]
  simp only [mul_assoc]

end DedekindZetaZeroFree.DigitMasks

end
