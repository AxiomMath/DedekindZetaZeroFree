module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace DedekindZetaZeroFree.KPKirillovFiniteTensor.ShuffleHelpers
variable {ι : Type*} [Fintype ι] (S J : ι → Type*)
 [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
 [∀ i, AddCommGroup (J i)] [∀ i, Module ℂ (J i)]
def shuffle : ((⨂[ℂ] i, S i) ⊗[ℂ] (⨂[ℂ] i, J i)) ≃ₗ[ℂ] (⨂[ℂ] i, S i ⊗[ℂ] J i) :=
 ((Basis.piTensorProduct fun i => Module.Free.chooseBasis ℂ (S i)).tensorProduct
 (Basis.piTensorProduct fun i => Module.Free.chooseBasis ℂ (J i))).equiv
 (Basis.piTensorProduct fun i => (Module.Free.chooseBasis ℂ (S i)).tensorProduct (Module.Free.chooseBasis ℂ (J i)))
 { toFun := fun p i => (p.1 i, p.2 i)
   invFun := fun p => (fun i => (p i).1, fun i => (p i).2)
   left_inv := by intro p; rfl
   right_inv := by intro p; rfl }
lemma shuffle_eq : (shuffle S J).toLinearMap = TensorProduct.lift (PiTensorProduct.map₂ (fun i => TensorProduct.mk ℂ (S i) (J i))) := by
 apply ((Basis.piTensorProduct fun i => Module.Free.chooseBasis ℂ (S i)).tensorProduct
 (Basis.piTensorProduct fun i => Module.Free.chooseBasis ℂ (J i))).ext
 intro p
 change shuffle S J _ = _
 unfold shuffle
 rw [Module.Basis.equiv_apply]
 simp only [Module.Basis.tensorProduct_apply', Basis.piTensorProduct_apply, TensorProduct.lift.tmul, PiTensorProduct.map₂_tprod_tprod, TensorProduct.mk_apply]
 rfl
@[simp] lemma shuffle_tmul (f : ∀ i, S i) (e : ∀ i, J i) :
 shuffle S J ((PiTensorProduct.tprod ℂ f) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ e)) = PiTensorProduct.tprod ℂ (fun i => f i ⊗ₜ[ℂ] e i) := by
 change (shuffle S J).toLinearMap _ = _
 rw [shuffle_eq]
 simp only [TensorProduct.lift.tmul, PiTensorProduct.map₂_tprod_tprod, TensorProduct.mk_apply]
end DedekindZetaZeroFree.KPKirillovFiniteTensor.ShuffleHelpers

end
