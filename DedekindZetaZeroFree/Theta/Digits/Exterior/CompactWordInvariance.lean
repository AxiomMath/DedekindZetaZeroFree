module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.CoefficientDefinitions
public import DedekindZetaZeroFree.Theta.Whittaker.SphericalNegativeSupport
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SexticUnitPhasesAndValuations

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)

 theorem weyl_compact (p : ThetaBranch.ExteriorPrime R.A) :
    KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) ∈
      KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) := by
  have hg := exterior_prime_not_bad R p
  change _ ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 p.val
  rw [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hg]
  exact ⟨KPStandardLocalRootLifts.integralW F p.val,
    (KPStandardLocalRootLifts.W_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p.val
      (fun h => hg (Or.inr h))).symm⟩

 theorem lower_compact (p : ThetaBranch.ExteriorPrime R.A) (o : KPTameCompact.O F p.val) :
    KPStandardLocalRootLifts.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) o.val ∈
      KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) := by
  have hg := exterior_prime_not_bad R p
  change _ ∈ KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 p.val
  rw [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hg]
  exact ⟨KPStandardLocalRootLifts.integralLowerN F p.val o,
    (KPStandardLocalRootLifts.LowerN_eq_compact F R.A.zeta12 R.A.primitive_zeta12 p.val
      (fun h => hg (Or.inr h)) o).symm⟩

 theorem weyl_fixed (p : ThetaBranch.ExteriorPrime R.A) :
    exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
      (C.factorization.references (Sum.inr p.val)) = C.factorization.references (Sum.inr p.val) :=
  (C.factorization.spherical_reference p.val p.property).2 _ (weyl_compact R p)

 theorem lower_fixed (p : ThetaBranch.ExteriorPrime R.A) (o : KPTameCompact.O F p.val) :
    exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) o.val)
      (C.factorization.references (Sum.inr p.val)) = C.factorization.references (Sum.inr p.val) :=
  (C.factorization.spherical_reference p.val p.property).2 _ (lower_compact R p o)

 theorem digit_word (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A) :
    ThetaExpansion.SignedExpansion.exteriorDigitFactor R C m x d p =
      C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
        (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
          KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
          KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
            (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val) (digitParameter R m d)))
        (C.factorization.references (Sum.inr p.val))) := by
  unfold ThetaExpansion.SignedExpansion.exteriorDigitFactor
  simp only [map_mul]
  rw [show KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (KPRationalAdelicSplitting.ACoordinates F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
          (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) (Sum.inr p.val)) =
      KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) from
      exterior_diagonal_eq_standard_lift R p _]
  rfl

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
