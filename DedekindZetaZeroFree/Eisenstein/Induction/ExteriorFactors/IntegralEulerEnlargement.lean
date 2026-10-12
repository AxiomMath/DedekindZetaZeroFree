module

public import DedekindZetaZeroFree.Eisenstein.Induction.ExteriorFactors.EulerInsertion
public import DedekindZetaZeroFree.Eisenstein.Induction.ExteriorFactors.ArithmeticHaarIntegrals

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators
open NumberField MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPLocalPrincipalSeries KPLocalExceptionalConstruction
open KPRankOneShellContinuation KPRankOneShellRepair KPRankOneTameSphericalFactor
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem parameterOutput_exterior_one (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C) (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain) :
    parameterOutput R N P C (fullCompact R P C) (.inr q) 1 z
      (plusReference R N P C (.inr q)) =
    ((arithmeticRootScale R (.inr q) : ℂ) *
      forwardFactor (LocalField F q) (integerHaar R N q) z) • reference R P C (.inr q) := by
  apply (inducingCoordinates R P C (.inr q)).injective
  funext j
  rw [← parameterKernel_integral R N P C (fullCompact R P C) (.inr q) 1 z hz]
  have hi := (exterior_arithmetic_integral R N P C q hq z hz
    (Function.surjInv (QuotientGroup.mk'_surjective
      ((C.polarization q).L.comap (C.canonical q).heisenberg.π)) j)).2
  simpa only [parameterKernel, inducingCoordinates, map_one, map_smul,
    Pi.smul_apply, smul_eq_mul]

def exteriorFactor (z : ℂ) : KPHilbert.Place F → ℂ
  | .inl _ => 1
  | .inr q => (arithmeticRootScale R (.inr q) : ℂ) *
      forwardFactor (LocalField F q) (integerHaar R N q) z

theorem parameterOutput_exterior (p : KPHilbert.Place F)
    (hp : p ∉ bad R P C) (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain) :
    parameterOutput R N P C (fullCompact R P C) p 1 z (plusReference R N P C p) =
      exteriorFactor R N z p • reference R P C p := by
  cases p with
  | inl w => exact False.elim (hp (arch_bad R P C w))
  | inr q => exact parameterOutput_exterior_one R N P C q hp z hz

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
