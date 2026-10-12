module

public import DedekindZetaZeroFree.Eisenstein.Residues.QuotientRealizations.RankOneProbeMap

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation.NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detected_dictionary_exists
    (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
    (prior : Nonempty (PeriodSource R N)) :
    ∃ D : Dictionary R N, D.coreMap (D.selected D.probe) ≠ 0 := by
  exact FourierContinuation.DetectedDictionary.detected_dictionary_exists prior

end DedekindZetaZeroFree.ThetaExpansion

end
