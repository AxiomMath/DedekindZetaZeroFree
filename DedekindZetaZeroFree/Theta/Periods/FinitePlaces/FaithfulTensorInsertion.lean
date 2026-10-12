module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.WhittakerProfileRank

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation

section Algebra
variable {I : Type*} [Fintype I] [DecidableEq I]
  (V : I → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

end Algebra

open MomentSources
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

namespace TensorHC

def slotFunction (D : TensorHC R N) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) (i : s.val) :
    actualLocal R D.finiteData i →ₗ[ℂ] Functions R :=
  D.coreMap.comp ((RestrictedTensorSimple.stageInclusion _ D.references D.bad s).comp
    ((PiTensorProduct.tprod ℂ).toLinearMap x i))

@[simp] theorem slotFunction_apply (D : TensorHC R N)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) (i : s.val)
    (b : actualLocal R D.finiteData i) :
    D.slotFunction s x i b = D.coreMap (RestrictedTensorSimple.stageInclusion _
      D.references D.bad s (PiTensorProduct.tprod ℂ (Function.update x i b))) := rfl

end TensorHC

namespace TensorDetected

theorem reference_ne_zero (D : TensorDetected R N) (p : KPHilbert.Place F)
    (hp : p ∉ D.bad) : D.references p ≠ 0 := by
  obtain ⟨l, _, _, hl⟩ := D.exists_detected_slice p
  intro hz
  exact hl hp (by rw [hz, map_zero])

end TensorDetected
end DedekindZetaZeroFree.FourierContinuation

end
