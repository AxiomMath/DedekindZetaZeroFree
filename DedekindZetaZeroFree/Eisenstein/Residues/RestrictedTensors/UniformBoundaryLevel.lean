module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.UniformInvariantLevel
public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.CompatibleLevels

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open NumberField IsDedekindDomain MomentSources KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
open KPGlobalResidualConstruction LiteralSource TensorActionSource ThetaExpansion KPLiteralRaw
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming pureComponent → pureComponent
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming exists_pure_product_level → exists_pure_product_level
open _root_.DedekindZetaZeroFree.FourierContinuation.LiteralSource renaming pure_raw_fixed → pure_raw_fixed
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000

open _root_.DedekindZetaZeroFree.FourierContinuation.ComplexLines renaming source_slot_uniform_level → source_slot_uniform_level

theorem restrictedSlot_uniform_source_residue_level
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) :
    ∃J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      (∀(v : complexCore) g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
        quotientCoreEvaluator R.A P C (restrictedSlotTensor R.A P C s x w hw v) (g*u) =
          quotientCoreEvaluator R.A P C (restrictedSlotTensor R.A P C s x w hw v) g) ∧
      (∀(v : complexCore) g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
        coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) (g*u) =
          coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g) := by
  obtain ⟨Us,hs⟩ := source_slot_uniform_level R P C s x w hw
  obtain ⟨Ur,hr⟩ := restrictedSlot_uniform_residue_level R P C s x w hw
  refine ⟨ResidualBoundaryRelevel.meetLevel F ζ hζ Us Ur, ?_, ?_⟩
  · intro v g u hu
    exact hs v g u (Subgroup.map_mono inf_le_left hu)
  · intro v g u hu
    exact hr v g u (Subgroup.map_mono inf_le_right hu)
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
