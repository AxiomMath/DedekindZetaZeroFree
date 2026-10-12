module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAnalyticity
public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.EisensteinFourierContinuation
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem flat_entire (R : PrincipalMellin.ActualRecipe S η)
    (Q : AdmissibleFlatSources R) (v : R.A.UnitQuotient) (g : Group R) :
    Differentiable ℂ (fun s => (Q.flat v).val s g) :=
  KPLiteralExceptionalResidue.LiteralChamberAnalytic.flat_entire
    F R.A.zeta12 R.A.primitive_zeta12 Q.K Q.iwasawa (Q.flat v) g

end DedekindZetaZeroFree.EisensteinFourierContinuation

end
