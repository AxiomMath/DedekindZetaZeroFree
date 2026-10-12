module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.RationalFiberSlices
public import DedekindZetaZeroFree.Theta.Periods.FiniteHaarTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLocalExceptionalConstruction KPRankOneShellRepair
open KPAdelicCoverRestrictedProduct MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

include P C in

theorem traceHaar_eq_smul_unit (q : KPFinitePlace F)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (q.adicCompletion F)).integer : Set _) = 1) :
    N.finiteHaar q = ENNReal.ofReal (PoissonS.integerVolume F q) • μ :=
  FourierContinuation.finiteHaar_transport N q ⟨C.canonical q, μ, hμ⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
