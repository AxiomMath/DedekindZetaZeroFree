module

public import DedekindZetaZeroFree.Theta.Unfolding.AdditiveFourierExtraction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def exteriorDigitFactor {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A) : ℂ :=
  C.factorization.ell (Sum.inr p.val)
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      p.val (C.factorization.finiteData p.val).inducing
      (C.factorization.finiteData p.val).inducing.polarization
      (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (KPRationalAdelicSplitting.ACoordinates F R.A.zeta12 R.A.primitive_zeta12
          (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
            (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) (Sum.inr p.val) *
          KPRationalAdelicSplitting.WCoordinates F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
          KPRationalAdelicSplitting.NCoordinates F R.A.zeta12 R.A.primitive_zeta12
            (digitParameter R m d) (Sum.inr p.val)))
      (C.factorization.references (Sum.inr p.val)))

def exteriorDigitCoefficient {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ) : ℂ :=
  ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
    digitWeight R m d * ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, exteriorDigitFactor R C m x d p

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
