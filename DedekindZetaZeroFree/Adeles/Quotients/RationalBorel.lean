module

public import DedekindZetaZeroFree.Eisenstein.Residues.AdelicChamberContinuationData

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPGlobalResidualKernel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalBorel : Subgroup (KPRationalAdelicSplitting.RationalPGL2 F) :=
  (KPGlobalTorusFunctionData.borel F ζ hζ).comap
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ)

abbrev RationalQuotient := Quotient (QuotientGroup.rightRel (rationalBorel F ζ hζ))

end DedekindZetaZeroFree.KPGlobalResidualKernel

end
