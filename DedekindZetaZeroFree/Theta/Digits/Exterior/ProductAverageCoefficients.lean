module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.FiniteRowProducts

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming exteriorLocalFactor_finite → exteriorLocalFactor_finite
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)

theorem actual_product_average (m : ThetaReflectionData.Row R.A) (x : Fˣ) :
    ThetaExpansion.SignedExpansion.exteriorDigitCoefficient R C m x =
    (∏ p : RowPrime R m, ∑ v : ThetaDigitAverage.Residue p.val,
      sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ (exteriorRowPrime R m p))
        (Characters.psi R (exteriorRowPrime R m p)) (ThetaDigitAverage.rowExponent R.A m.val p.val) v *
      localDigitValue R C (exteriorRowPrime R m p) x ((ThetaDigitAverage.residueLifts _).lift p v)) *
    ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, if p ∈ exteriorRows R m then 1 else
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x := by
  let off := ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, if p ∈ exteriorRows R m then 1 else
    ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x
  have hs (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
      (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d p) =
      (∏ p : RowPrime R m, localDigitValue R C (exteriorRowPrime R m p) x
        ((ThetaDigitAverage.residueLifts _).lift p (d p))) * off := by
    rw [split_product (exteriorRows R m) _ (finite_support R C m x d), prod_exteriorRows]
    congr 1
    · apply Finset.prod_congr rfl
      intro p _
      exact factor_at_row R C m x d p
    · apply finprod_congr
      intro p
      by_cases hp : p ∈ exteriorRows R m
      · simp [hp]
      · rw [if_neg hp, if_neg hp]
        exact offrow_value R C m x d p (fun h => hp ((mem_exteriorRows R m p).mpr h))
  unfold ThetaExpansion.SignedExpansion.exteriorDigitCoefficient
  simp_rw [hs, ← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simp only [digitWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (p : RowPrime R m) (v : ThetaDigitAverage.Residue p.val) =>
    sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ (exteriorRowPrime R m p))
      (Characters.psi R (exteriorRowPrime R m p)) (ThetaDigitAverage.rowExponent R.A m.val p.val) v *
      localDigitValue R C (exteriorRowPrime R m p) x ((ThetaDigitAverage.residueLifts _).lift p v))]

theorem coefficient_exact (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (x : Fˣ) :
    ThetaExpansion.SignedExpansion.exteriorDigitCoefficient R C m x =
      ThetaBranch.exteriorCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D x := by
  rw [actual_product_average]
  simp_rw [local_average R C m x]
  unfold ThetaBranch.exteriorCoefficient
  rw [split_product (exteriorRows R m) _
    (exteriorLocalFactor_finite R.A R.probe.allowed R.σ (Characters.psi R) m D x), prod_exteriorRows]
  congr 1
  · apply Finset.prod_congr rfl
    intro p _
    unfold ThetaBranch.exteriorLocalFactor
    rw [← row_support R m D, if_pos p.property]
  · apply finprod_congr
    intro p
    by_cases hp : p ∈ exteriorRows R m
    · simp [hp]
    · rw [if_neg hp, if_neg hp]
      unfold ThetaBranch.exteriorLocalFactor
      rw [← row_support R m D, if_neg (fun h => hp ((mem_exteriorRows R m p).mpr h))]

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
