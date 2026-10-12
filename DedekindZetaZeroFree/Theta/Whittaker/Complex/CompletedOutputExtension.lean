module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.CompletedContinuity
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.CompactResidueBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)

def actualSlot : complexCore →ₗ[ℂ] (KPLiteralRaw.G F ζ hζ → ℂ) :=
  (LiteralSource.coreResidue R P C).comp (restrictedSlotTensor R.A P C s x w hw)

theorem actualSlot_continuous (v : complexCore) : Continuous (actualSlot R P C s x w hw v) :=
  (LiteralSource.coreResidue_raw_automorphic R P C _).1.1

end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
