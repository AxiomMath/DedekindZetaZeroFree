module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.CompactWordInvariance
public import DedekindZetaZeroFree.Theta.Digits.ExteriorCongruences

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localAdele → eval_localAdele
open _root_.DedekindZetaZeroFree.ThetaBranch renaming order_finite_support → order_finite_support
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)

 theorem parameter_offrow (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : KPFinitePlace F) (hp : p ∉ ThetaDigitAverage.rowPrimes R.A m.val m.property) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p) (digitParameter R m d) = 0 := by
  simp only [digitParameter, map_sum, eval_localAdele]
  apply Finset.sum_eq_zero
  intro q _
  apply Pi.single_eq_of_ne
  intro he
  exact hp (he ▸ q.property)

 theorem offrow_value (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A)
    (hp : p.val ∉ ThetaDigitAverage.rowPrimes R.A m.val m.property) :
    ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d p =
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x := by
  rw [digit_word, parameter_offrow R m d p.val hp]
  have hn : KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) 0 = 1 := by
    simp [KPPGLLocalCover.N]
  simp only [hn, mul_one, map_mul, Module.End.mul_apply, weyl_fixed R C p]
  rw [← exterior_diagonal_eq_standard_lift R p]
  exact C.exterior.rational_exact p x

 theorem finite_support (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    Function.HasFiniteMulSupport (ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d) := by
  have hs := (((ThetaDigitAverage.rowPrimes R.A m.val m.property).finite_toSet).union
    (order_finite_support x)).preimage
      (f := fun p : ThetaBranch.ExteriorPrime R.A => p.val) Subtype.val_injective.injOn
  apply hs.subset
  intro p hp
  by_contra h
  have hh : p.val ∉ ThetaDigitAverage.rowPrimes R.A m.val m.property ∧ ThetaBranch.order p.val x = 0 := by
    simpa only [Set.mem_preimage, Set.mem_union, Finset.mem_coe,
      Set.mem_setOf_eq, not_or, not_not] using h
  apply hp
  rw [offrow_value R C m x d p hh.1]
  simp [ThetaBranch.sphericalFactor, hh.2, sexticSphericalCoefficient]

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
