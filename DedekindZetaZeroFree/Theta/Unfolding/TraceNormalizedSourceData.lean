module

public import DedekindZetaZeroFree.Moments.Probes.SignedUnfoldingAndAngularCancellation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
structure JointRootAlignedSources where
  aligned : RootAligned R
  transport : TraceHaarTransport R
  transport_exact : transport = N
  sources : AdmissibleFlatSources R
structure JointRealizedFlatSources extends JointRootAlignedSources R N where
  realization : Realization R sources
structure JointHaarFactorizedSources extends JointRealizedFlatSources R N where
  factorization : SourceFactorization R sources realization

  localHaarTransport : ∀ q, transport.finiteHaar q =
    ENNReal.ofReal (PoissonS.integerVolume F q) • (factorization.finiteData q).haar
structure JointExteriorCoefficientSources extends JointHaarFactorizedSources R N where
  exterior : ExteriorCoefficients R sources realization factorization
structure JointForwardIdentitySources extends JointExteriorCoefficientSources R N where
  packet : Packet R sources
  forward : ForwardIdentity R sources realization packet
structure JointResidualConstantTermSources extends JointForwardIdentitySources R N where
  constantTerm : ResidualConstantTerm R sources realization
structure JointMellinGaussianSources extends JointResidualConstantTermSources R N where
  mellin : MellinGaussian R transport sources packet
structure JointDigitDescentSources extends JointMellinGaussianSources R N where
  descent : DigitsDescent R transport sources realization packet
structure JointSameResidueProfileSources extends JointDigitDescentSources R N where
  profiles : SameResidueProfiles R sources realization packet
structure JointReverseAbsoluteSources extends JointSameResidueProfileSources R N where
  absolute : ReverseAbsolute R transport sources realization packet
structure JointUpperVanishingSources extends JointReverseAbsoluteSources R N where
  upperZero : BothUpperZero R transport sources realization packet
structure JointSignedUnfoldingSources extends JointUpperVanishingSources R N where
  unfolding : SignedUnfolding R transport sources realization packet

def JointSignedUnfoldingSources.certified (C : JointSignedUnfoldingSources R N) : CertifiedPacket R where
  aligned := C.aligned
  transport := C.transport
  sources := C.sources
  realization := C.realization
  factorization := C.factorization
  localHaarTransport := C.localHaarTransport
  exterior := C.exterior
  packet := C.packet
  forward := C.forward
  constantTerm := C.constantTerm
  mellin := C.mellin
  descent := C.descent
  profiles := C.profiles
  absolute := C.absolute
  upperZero := C.upperZero
  unfolding := C.unfolding
end DedekindZetaZeroFree.MomentSources

end
