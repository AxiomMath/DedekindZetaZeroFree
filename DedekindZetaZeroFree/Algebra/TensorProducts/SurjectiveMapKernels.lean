module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.Projective

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPLiteralResidueKernelTests

 theorem tensor_kernel_le_span
    {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι]
    {V W : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module 𝕜 (W i)]
    (f : ∀ i, V i →ₗ[𝕜] W i) (hf : ∀ i, Function.Surjective (f i)) :
    LinearMap.ker (PiTensorProduct.map f) ≤
      Submodule.span 𝕜 {t | ∃ a : ∀ i, V i,
        (∃ i, f i (a i) = 0) ∧ PiTensorProduct.tprod 𝕜 a = t} := by
  classical
  let S := Submodule.span 𝕜 {t | ∃ a : ∀ i, V i,
    (∃ i, f i (a i) = 0) ∧ PiTensorProduct.tprod 𝕜 a = t}
  let T := S.mkQ.compMultilinearMap (PiTensorProduct.tprod 𝕜)
  have hzero (a : ∀ i, V i) (i : ι) (ha : f i (a i) = 0) : T a = 0 := by
    exact (Submodule.Quotient.mk_eq_zero S).mpr
      (Submodule.subset_span ⟨a, ⟨i, ha⟩, rfl⟩)
  have hupdate (a : ∀ i, V i) (i : ι) (b : V i) (hab : f i (a i) = f i b) :
      T (Function.update a i b) = T a := by
    have hz : T (Function.update a i (a i - b)) = 0 := by
      apply hzero _ i
      simp [map_sub, hab]
    rw [MultilinearMap.map_update, hz, sub_zero]
  have hfib (a b : ∀ i, V i) (hab : ∀ i, f i (a i) = f i (b i)) : T a = T b := by
    have haux (s : Finset ι) : T (s.piecewise b a) = T a := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.piecewise_insert]
        rw [hupdate, ih]
        simpa [Finset.piecewise_eq_of_notMem, hi] using hab i
    simpa using (haux Finset.univ).symm
  have hr : ∀ i, ∃ g : W i →ₗ[𝕜] V i, (f i).comp g = LinearMap.id := by
    intro i
    exact (f i).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (hf i))
  choose g hg using hr
  have hg' (i : ι) (w : W i) : f i (g i w) = w := by
    simpa using LinearMap.congr_fun (hg i) w
  have heq : S.mkQ = (S.mkQ.comp (PiTensorProduct.map g)).comp
      (PiTensorProduct.map f) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    change T a = S.mkQ (PiTensorProduct.map g
      (PiTensorProduct.map f (PiTensorProduct.tprod 𝕜 a)))
    simp only [PiTensorProduct.map_tprod]
    exact hfib a (fun i => g i (f i (a i))) (fun i => (hg' i _).symm)
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQ x = 0
  rw [heq, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

end DedekindZetaZeroFree.KPLiteralResidueKernelTests

end
