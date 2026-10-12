module

public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.ZeroSourceActions

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.TensorHCSource
open MomentSources TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

def zeroTensorHC (D : TensorSeed R N) : TensorHC R N := by
  letI : Infinite (KPFinitePlace F) := finitePlaces_infinite F
  letI : Infinite (KPHilbert.Place F) := Infinite.of_injective
    (Sum.inr : KPFinitePlace F → KPHilbert.Place F) Sum.inr_injective
  letI : Subsingleton (RestrictedTensorSimple.Core (actualLocal R D.finiteData)
    (fun _ => 0) D.bad) := zeroReferenceCore_subsingleton _ _
  refine {
    aligned := D.aligned
    transport := D.transport
    transport_exact := D.transport_exact
    sources := zeroSources D.sources
    realization := zeroRealization D.sources D.realization
    finiteData := D.finiteData
    references := fun _ => 0
    bad := D.bad
    bad_exact := D.bad_exact
    scalarSlot := D.scalarSlot
    coreMap := 0
    selected := fun _ => 0
    selected_eq := ?_
    selected_frozen_stage := ?_
    core_injective := ?_
    regular := ?_
    generated := ?_ }
  · intro v; rfl
  · intro v
    refine ⟨⟨D.bad, le_rfl⟩, fun _ => 0, rfl, ?_⟩
    exact Subsingleton.elim _ _
  · intro x y _; exact Subsingleton.elim _ _
  · intro x; exact Submodule.zero_mem _
  · intro x; exact Submodule.zero_mem _

theorem tensorHC_nonempty (prior : Nonempty (TensorSeed R N)) :
    Nonempty (TensorHC R N) := by
  obtain ⟨D⟩ := prior
  exact ⟨zeroTensorHC D⟩

end DedekindZetaZeroFree.FourierContinuation.TensorHCSource

end
