module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaActualArithmeticBinding
open NumberField IsDedekindDomain
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

def actualPlace {F : Type} [Field F] [NumberField F] : KPPlace F → KPHilbert.Place F
  | Sum.inl p => Sum.inr p
  | Sum.inr v => Sum.inl v

def completionEquiv {F : Type} [Field F] [NumberField F] (v : KPPlace F) :
    KPCompletion F v ≃+* KPHilbert.Completion F (actualPlace v) := by
  cases v <;> exact RingEquiv.refl _

end DedekindZetaZeroFree.ThetaActualArithmeticBinding

end
