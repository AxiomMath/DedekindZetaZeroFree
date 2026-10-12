module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.ProductCovariantSlices

@[expose] public section

noncomputable section
open scoped TensorProduct
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.ScalarFiniteSamplingGeneration

section Functions
variable {ι : Type} [Fintype ι] [DecidableEq ι] {C : ι → Type} [∀ i, Fintype (C i)]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

 def functionTensorEquiv :
    PiTensorProduct ℂ (fun i => C i → V i) ≃ₗ[ℂ]
      ((∀ i, C i) → PiTensorProduct ℂ V) :=
  (PiTensorProduct.congr (fun i =>
    (Finsupp.linearEquivFunOnFinite ℂ (V i) (C i)).symm)).trans
    (PiTensorProduct.ofFinsuppEquiv.trans
      (Finsupp.linearEquivFunOnFinite ℂ (PiTensorProduct ℂ V) (∀ i, C i)))

 theorem functionTensorEquiv_formula
    (x : PiTensorProduct ℂ (fun i => C i → V i)) (c : ∀ i, C i) :
    functionTensorEquiv x c =
      PiTensorProduct.map (fun i => LinearMap.proj (c i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul]
    change r • functionTensorEquiv (PiTensorProduct.tprod ℂ x) c = _
    simp only [functionTensorEquiv, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
      PiTensorProduct.map_tprod, PiTensorProduct.ofFinsuppEquiv_apply,
      Finsupp.linearEquivFunOnFinite_apply, Finsupp.linearEquivFunOnFinite_symm_apply,
      LinearMap.proj_apply]
  | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

end Functions

end DedekindZetaZeroFree.ScalarFiniteSamplingGeneration

end
