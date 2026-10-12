module

public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.ZeroSourceActions
public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.LocalCompactsAndScalarSlots

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.TensorSeedSource
open MomentSources TensorActionSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

def zeroSeed (D : JointRealizedFlatSources R N) : TensorSeed R N := by
  letI : Infinite (KPFinitePlace F) := finitePlaces_infinite F
  letI : Infinite (KPHilbert.Place F) := Infinite.of_injective
    (Sum.inr : KPFinitePlace F → KPHilbert.Place F) Sum.inr_injective
  letI : Subsingleton (RestrictedTensorSimple.Core (actualLocal R (localData R))
    (fun _ => 0) (bad R)) := zeroReferenceCore_subsingleton _ _
  refine {
    aligned := D.aligned
    transport := D.transport
    transport_exact := D.transport_exact
    sources := zeroSources D.sources
    realization := zeroRealization D.sources D.realization
    finiteData := localData R
    references := fun _ => 0
    bad := bad R
    bad_exact := bad_exact R
    scalarSlot := scalarSlot R
    coreMap := 0
    selected := fun _ => 0
    selected_eq := ?_
    selected_frozen_stage := ?_
    core_injective := ?_
    regular := ?_ }
  · intro v; rfl
  · intro v
    refine ⟨⟨bad R, le_rfl⟩, fun _ => 0, rfl, ?_⟩
    exact Subsingleton.elim _ _
  · intro x y _
    exact Subsingleton.elim _ _
  · intro x
    exact Submodule.zero_mem _

theorem tensorSeed_nonempty (prior : Nonempty (JointRealizedFlatSources R N)) :
    Nonempty (TensorSeed R N) := by
  obtain ⟨D⟩ := prior
  exact ⟨zeroSeed D⟩

end DedekindZetaZeroFree.FourierContinuation.TensorSeedSource

end
