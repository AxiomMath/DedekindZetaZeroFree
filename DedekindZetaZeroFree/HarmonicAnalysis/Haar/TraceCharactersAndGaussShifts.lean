module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ComplexTraceMeasureParameters
public import DedekindZetaZeroFree.Arithmetic.Ideals.RootAlignedPrincipalization

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem trace_haar_transport_exists (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) : Nonempty (TraceHaarTransport R) := by
  exact TraceHaarTransport.traceHaarTransport_exists R

end DedekindZetaZeroFree.ThetaExpansion
