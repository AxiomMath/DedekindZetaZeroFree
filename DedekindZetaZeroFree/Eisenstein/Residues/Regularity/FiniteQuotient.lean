module

public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteImageQuotients.DescentAndCovariance
public import DedekindZetaZeroFree.Eisenstein.Residues.Regularity.CoreResidue

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)

theorem finiteCoreResidue_regular (N : MomentSources.TraceHaarTransport R)
    (x : RestrictedTensorSimple.Core (FiniteQuotientFiber R P C μ hμ)
      (finiteQuotientReference R P C μ hμ) (bad R.A P C)) :
    finiteCoreResidue R P C μ hμ N x ∈ MomentSources.regularResidualFunctions R := by
  obtain ⟨y, rfl⟩ := finiteCoreQuotient_surjective R P C μ hμ x
  rw [finiteCoreResidue_quotient]
  exact coreResidue_regular R P C y

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
