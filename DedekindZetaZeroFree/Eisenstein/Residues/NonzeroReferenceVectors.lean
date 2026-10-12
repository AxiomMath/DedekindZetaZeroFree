module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.LocalFactorCovariance
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteImageQuotients.SphericalReferences
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.NonzeroResidueExistence

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw KPRankOneShellRepair
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "Q" => FiniteQuotientFiber R P C μ hμ
local notation "W" => MomentSources.actualLocal R (actualImageData R P C μ hμ)
local notation "e" => finiteQuotientReference R P C μ hμ
local notation "E" => bad R.A P C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem actualCoreResidue_exists_ne_zero (N : MomentSources.TraceHaarTransport R) :
    ∃ x : RestrictedTensorSimple.Core W (actualReference R P C μ hμ) E,
      actualCoreResidue R P C μ hμ N x ≠ 0 := by
  obtain ⟨x,hx⟩ := CofactorChamber.exists_coreResidue_ne_zero_unconditional R P C
  refine ⟨actualCoreEquiv R P C μ hμ (finiteCoreQuotient R P C μ hμ x), ?_⟩
  simpa only [actualCoreResidue, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, finiteCoreResidue_quotient] using hx

theorem actualReference_ne_zero (hC : C.exceptional = R.A.Sf)
    (v : KPHilbert.Place F) (hv : v ∉ bad R.A P C) :
    actualReference R P C μ hμ v ≠ 0 := by
  intro hz
  apply finiteQuotientReference_ne_zero R P C μ hμ hC v hv
  apply (actualFactorEquiv R P C μ hμ v).injective
  exact hz.trans (map_zero (actualFactorEquiv R P C μ hμ v)).symm

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
