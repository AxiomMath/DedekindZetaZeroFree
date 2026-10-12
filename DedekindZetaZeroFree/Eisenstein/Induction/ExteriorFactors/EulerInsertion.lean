module

public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity

@[expose] public section

noncomputable section
open scoped Classical TensorProduct BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource
universe u v w
variable {I : Type u} (V : I → Type v) (W : I → Type w)
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (e : ∀ i, V i) (e' : ∀ i, W i)

theorem euler_insertion (s t : Finset I) (hst : s ⊆ t)
    (A : ∀ i, V i →ₗ[ℂ] W i) (b : I → ℂ)
    (hA : ∀ i ∈ t, i ∉ s → A i (e i) = b i • e' i) :
    (PiTensorProduct.map (fun i : t => A i)).comp
      (RestrictedTensorSimple.insert V e s t hst) =
    (∏ i ∈ t \ s, b i) •
      ((RestrictedTensorSimple.insert W e' s t hst).comp
        (PiTensorProduct.map (fun i : s => A i))) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, RestrictedTensorSimple.insert_pure, PiTensorProduct.map_tprod]
  have hp : (∏ i : t, if (i : I) ∈ s then (1 : ℂ) else b i) =
      ∏ i ∈ t \ s, b i := by
    change (∏ i : t, (fun j : I => if j ∈ s then (1 : ℂ) else b j) i) = _
    rw [← Finset.prod_subtype t (by simp) (fun j : I => if j ∈ s then (1 : ℂ) else b j)]
    simp only [Finset.sdiff_eq_filter, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp_all
  rw [← hp, ← MultilinearMap.map_smul_univ]
  congr 1
  funext i
  by_cases hi : (i : I) ∈ s
  · simp only [dite_eq_left hi, ite_eq_left hi, one_smul]
  · simp only [dite_eq_right hi, ite_eq_right hi]
    exact hA i i.property hi

theorem euler_core_insertion (E : Finset I)
    (s t : RestrictedTensorSimple.Level E) (hst : s ≤ t)
    (A : ∀ i, V i →ₗ[ℂ] W i) (b : I → ℂ)
    (hA : ∀ i ∈ t.val, i ∉ s.val → A i (e i) = b i • e' i)
    (y : RestrictedTensorSimple.Stage V s.val) :
    RestrictedTensorSimple.stageInclusion W e' E t
      (PiTensorProduct.map (fun i : t.val => A i)
        (RestrictedTensorSimple.transition V e E s t hst y)) =
    (∏ i ∈ t.val \ s.val, b i) •
      RestrictedTensorSimple.stageInclusion W e' E s
        (PiTensorProduct.map (fun i : s.val => A i) y) := by
  have hm := LinearMap.congr_fun (euler_insertion V W e e' s.val t.val hst A b hA) y
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hm
  change RestrictedTensorSimple.stageInclusion W e' E t
    (PiTensorProduct.map (fun i : t.val => A i)
      (RestrictedTensorSimple.insert V e s.val t.val hst y)) = _
  rw [hm, map_smul]
  congr 1
  exact Module.DirectLimit.of_f

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource

end
