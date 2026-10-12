module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorWords.CyclicSlotDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6400000
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources KPCplxCharacterHaar
open KPContActualSphericalRightFieldIdentification
 theorem map_tensorSlot
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (Q : ∀ i, V i →ₗ[ℂ] W i) (i : ι)
    (A : Module.End ℂ (V i)) (B : Module.End ℂ (W i))
    (h : ∀ x, Q i (A x) = B (Q i x)) :
    (PiTensorProduct.map Q).comp (tensorSlot i A) =
      (tensorSlot i B).comp (PiTensorProduct.map Q) := by
  rw [tensorSlot, tensorSlot, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
    exact LinearMap.ext h
  · simp only [Function.update_of_ne hj, LinearMap.comp_id, LinearMap.id_comp]

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
