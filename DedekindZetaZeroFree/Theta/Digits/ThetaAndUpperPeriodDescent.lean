module

public import DedekindZetaZeroFree.Theta.Digits.CompactRightCorrections

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField
open scoped Classical BigOperators
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem digitRight_inverse_fixed {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (u : R.A.U) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) (g : Group R) :
    T.theta v (g * (digitRight R m u y d)⁻¹) = T.theta v g ∧
      upper R Q.dq (T.theta v) (g * (digitRight R m u y d)⁻¹) = upper R Q.dq (T.theta v) g := by
  have hk : ∀ w, (digitRightTuple R m u y d)⁻¹ w ∈ exteriorFactor R w := by
    intro w
    rw [RestrictedProduct.inv_apply]
    exact (exteriorFactor R w).inv_mem (digitRightTuple_mem R m u y d w)
  have he : (digitRight R m u y d)⁻¹ =
      KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12
          (digitRightTuple R m u y d)⁻¹) := by simp only [digitRight, map_inv]
  rw [he]
  exact ⟨theta_full_exterior R T v _ hk g, upper_full_exterior R T v _ hk g⟩

theorem signed_term_reindex {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (u : R.A.U) (b : Bool) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    T.theta v (signedArgument R m b (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d)) =
      T.theta v (signedArgument R m b y d) ∧
    upper R Q.dq (T.theta v)
      (signedArgument R m b (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d)) =
      upper R Q.dq (T.theta v) (signedArgument R m b y d) := by
  cases b
  · rw [signedArgument_reindex_false]
    have hh := digitRight_inverse_fixed R T v m u y d
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u.val ^ 6)⁻¹) * signedArgument R m false y d)
    rw [hh.1, hh.2]
    have ht := theta_rational_diagonal R T v ((u.val ^ 6)⁻¹) (signedArgument R m false y d)
    have hu := upper_rational_diagonal R T v ((u.val ^ 6)⁻¹) (signedArgument R m false y d)
    simpa only [map_inv] using And.intro ht hu
  · rw [signedArgument_reindex_true]
    have hh := digitRight_inverse_fixed R T v m u y d
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u.val ^ 6)) * signedArgument R m true y d)
    rw [hh.1, hh.2]
    exact ⟨theta_rational_diagonal R T v (u.val ^ 6) _, upper_rational_diagonal R T v (u.val ^ 6) _⟩

end DedekindZetaZeroFree.DigitMasks

end
