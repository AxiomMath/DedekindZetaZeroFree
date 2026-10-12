module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors

@[expose] public section

noncomputable section
open scoped TensorProduct
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.ScalarFiniteProductCovariantSlices
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
 def contractionMultilinear [DecidableEq ι] (q : ι) (l : ∀ i, V i →ₗ[ℂ] ℂ) : MultilinearMap ℂ V (V q) :=
  .mk' (fun x => (∏ i ∈ Finset.univ.erase q, l i (x i)) • x q)
    (by
    intro x i a b
    by_cases hi : i = q
    · subst i
      have hh (z : V q) : (∏ j ∈ Finset.univ.erase q, l j (Function.update x q z j)) = ∏ j ∈ Finset.univ.erase q, l j (x j) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hh (a + b), hh a, hh b]
      simp only [Function.update_self, smul_add]
    · have hm : i ∈ Finset.univ.erase q := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
      have hh (z : V i) : (∏ j ∈ Finset.univ.erase q, l j (Function.update x i z j)) =
          l i z * ∏ j ∈ (Finset.univ.erase q).erase i, l j (x j) := by
        rw [← Finset.mul_prod_erase _ _ hm]
        simp only [Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hh (a + b), hh a, hh b]
      simp only [Function.update_of_ne (Ne.symm hi), map_add, add_mul, add_smul]
    )
    (by
    intro x i c a
    by_cases hi : i = q
    · subst i
      have hh (z : V q) : (∏ j ∈ Finset.univ.erase q, l j (Function.update x q z j)) = ∏ j ∈ Finset.univ.erase q, l j (x j) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hh (c • a), hh a]
      simp only [Function.update_self, smul_smul, mul_comm]
    · have hm : i ∈ Finset.univ.erase q := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
      have hh (z : V i) : (∏ j ∈ Finset.univ.erase q, l j (Function.update x i z j)) =
          l i z * ∏ j ∈ (Finset.univ.erase q).erase i, l j (x j) := by
        rw [← Finset.mul_prod_erase _ _ hm]
        simp only [Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hh (c • a), hh a]
      simp only [Function.update_of_ne (Ne.symm hi), map_smul, smul_eq_mul, mul_assoc, mul_smul]
    )
 def contraction [DecidableEq ι] (q : ι) (l : ∀ i, V i →ₗ[ℂ] ℂ) := PiTensorProduct.lift (contractionMultilinear q l)
 theorem contraction_mapSingle [DecidableEq ι] (q : ι) (l : ∀ i, V i →ₗ[ℂ] ℂ) (A : V q →ₗ[ℂ] V q) (x : PiTensorProduct ℂ V) :
  contraction q l (PiTensorProduct.map (Function.update (fun i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A) x) = A (contraction q l x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, PiTensorProduct.map_tprod, contraction, PiTensorProduct.lift.tprod, map_smul]
    change c • ((∏ i ∈ Finset.univ.erase q, l i (Function.update (fun i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A i (x i))) • (Function.update (fun i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A q (x q))) = _
    have hh : (∏ i ∈ Finset.univ.erase q, l i (Function.update (fun i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A i (x i))) = ∏ i ∈ Finset.univ.erase q, l i (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Function.update_of_ne (Finset.ne_of_mem_erase hi), LinearMap.id_apply]
    rw [hh, Function.update_self]
    change c • _ = c • A ((∏ i ∈ Finset.univ.erase q, l i (x i)) • x q)
    rw [map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end DedekindZetaZeroFree.ScalarFiniteProductCovariantSlices

end
