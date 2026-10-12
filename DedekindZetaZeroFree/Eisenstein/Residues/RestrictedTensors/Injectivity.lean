module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.KernelStability
public import DedekindZetaZeroFree.Eisenstein.Residues.NonzeroReferenceVectors

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources HCGeneration
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ
local notation "A" => actualLocalAlgebra R H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem actualCoreResidue_injective (N : TraceHaarTransport R)
    (hC : C.exceptional = R.A.Sf) :
    Function.Injective (actualCoreResidue R P C μ hμ N) := by
  let L := actualCoreResidue R P C μ hμ N
  let K : Submodule (RestrictedTensorSimple.actionAlgebra W (fun v => ↥(A v)) e E)
      (RestrictedTensorSimple.Core W e E) := {
    carrier := LinearMap.ker L
    zero_mem' := map_zero L
    add_mem' := by intro x y hx hy; change L (x+y)=0; rw [map_add,hx,hy,add_zero]
    smul_mem' := fun a x hx => actualCoreResidue_kernel_stable R P C μ hμ N a x hx }
  let := RestrictedTensorSimple.core_simple W (fun v => ↥(A v)) e E
    (actualReference_ne_zero R P C μ hμ hC) (actualLocalAlgebra_scalar R H)
  have hk : K = ⊥ := by
    rcases eq_bot_or_eq_top K with h | h
    · exact h
    · obtain ⟨x,hx⟩ := actualCoreResidue_exists_ne_zero R P C μ hμ N
      have hxK : x ∈ K := by rw [h]; trivial
      exact False.elim (hx hxK)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    have hxK : x ∈ K := hx
    rw [hk] at hxK
    exact hxK
  · exact bot_le

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
