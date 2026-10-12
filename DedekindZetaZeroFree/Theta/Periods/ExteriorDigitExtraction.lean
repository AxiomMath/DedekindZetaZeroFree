module

public import DedekindZetaZeroFree.Theta.Digits.WeylPeriodExtraction
public import DedekindZetaZeroFree.Theta.Whittaker.RationalFrequencyDilation

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}

def exteriorDigitValue (D : SourceFactorization R Q T)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A) : ℂ :=
  OrbitExpansion.exteriorSlotValue R D p.val
    (OrbitExpansion.reverseTuple R x 1 m d (Sum.inr p.val))

theorem reverseTuple_period (D : SourceFactorization R Q T)
    (v : R.A.UnitQuotient) (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    Function.HasFiniteMulSupport (exteriorDigitValue R D m x d) ∧
    fourier R Q.dq (T.theta v) (OrbitExpansion.restrictedLift R (OrbitExpansion.reverseTuple R x y m d)) =
      (∏ᶠ p, exteriorDigitValue R D m x d p) *
      fourier R Q.dq (T.theta v)
        (diagonal R (R.A.diagonal x) *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y) := by
  let b := OrbitExpansion.reverseTuple R x y m d
  let a := OrbitExpansion.exteriorRestriction R b
  let g := OrbitExpansion.sRestriction R b
  obtain ⟨P, hP⟩ := OrbitExpansion.exterior_tuple_finite_exceptional R a
  have h := OrbitExpansion.fourier_exterior_tuple R D v a g
    (by intro p; simp [g, OrbitExpansion.sRestriction, p.property])
    (by intro w hw; exact ite_eq_right hw) P hP
  have he (p : ThetaBranch.ExteriorPrime R.A) :
      OrbitExpansion.exteriorSlotValue R D p.val (a (Sum.inr p.val)) = exteriorDigitValue R D m x d p := by
    have ha : a (Sum.inr p.val) = b (Sum.inr p.val) := by simp [a, p.property]
    rw [ha]
    dsimp only [b, exteriorDigitValue]
    rw [OrbitExpansion.reverseTuple_exterior, OrbitExpansion.reverseTuple_exterior]
  simp_rw [he] at h
  refine ⟨h.1, ?_⟩
  have hb := congrArg (OrbitExpansion.restrictedLift R) (OrbitExpansion.splitTuple R b)
  rw [map_mul] at hb
  rw [hb, h.2]
  congr 1
  exact OrbitExpansion.sReverseTuple_period R T v x y m d

theorem fourier_diagonal_mul_norm (v : R.A.UnitQuotient) (x y : R.A.G) (g : Group R) :
    ‖fourier R Q.dq (T.theta v) (diagonal R x * diagonal R y * g)‖ =
      ‖fourier R Q.dq (T.theta v) (diagonal R (x * y) * g)‖ := by
  have he := congrArg (OrbitExpansion.restrictedLift R) (OrbitExpansion.sDiagonalTuple_mul R x y)
  simp only [map_mul, OrbitExpansion.restrictedLift_centralTuple] at he
  change diagonal R x * diagonal R y =
    KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.centralProduct F (OrbitExpansion.sDiagonalDefect R x y)) *
        diagonal R (x * y) at he
  rw [he, mul_assoc, OrbitExpansion.fourier_left_central, norm_mul]
  have hc : ‖(KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.centralProduct F (OrbitExpansion.sDiagonalDefect R x y)) : ℂ)‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one (n := 3) _ (by decide)
    let ε := KPAdelicCoverRestrictedProduct.centralProduct F (OrbitExpansion.sDiagonalDefect R x y)
    have h : ε ^ 3 = 1 := Subtype.ext ε.property
    have hp : KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 ε ^ 3 = 1 := by
      rw [← map_pow, h, map_one]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) hp
  rw [hc, one_mul]

theorem orbit_reverse_norm (D : SourceFactorization R Q T)
    (v : R.A.UnitQuotient)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    ‖orbitFrequencyValue R Q T v i (signedArgument R m false y d)‖ =
      ‖∏ᶠ p, exteriorDigitValue R D m (Quotient.out i.1 * i.2.val) d p‖ *
      ‖fourier R Q.dq (T.theta v)
        (diagonal R (R.A.diagonal (Quotient.out i.1 * i.2.val) / y) *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)‖ := by
  rw [orbitFrequencyValue_eq_fourier]
  change ‖fourier R Q.dq (T.theta v)
    (OrbitExpansion.restrictedLift R (OrbitExpansion.reverseTuple R (Quotient.out i.1 * i.2.val) y m d))‖ = _
  rw [(reverseTuple_period R D v _ y m d).2, norm_mul,
    mul_assoc, OrbitExpansion.globalWeyl_diagonal, ← mul_assoc, fourier_diagonal_mul_norm]
  rfl

end DedekindZetaZeroFree.OrbitFrequencies
end
