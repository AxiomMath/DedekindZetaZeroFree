module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import DedekindZetaZeroFree.Algebra.TensorProduct.SeparatingFunctionals

@[expose] public section

noncomputable section

open scoped Classical TensorProduct

namespace DedekindZetaZeroFree.ResidualTensorRecovery

universe u v w

set_option backward.isDefEq.respectTransparency.types false in
private theorem prod_split {I : Type u} [Fintype I] (i₀ : I) (f : I → ℂ) :
    (∏ i, f i) = (∏ j : ({i₀}ᶜ : Set I), f j) * f i₀ := by
  classical
  rw [Fintype.prod_eq_prod_compl_mul i₀ f]
  rw [Finset.prod_subtype (p := fun i => i ∈ ({i₀}ᶜ : Set I))
    ({i₀}ᶜ : Finset I) (fun i => by simp) f]

private theorem prod_update {I : Type u} [Fintype I] {X : I → Type w}
    (f : ∀ i, X i → ℂ) (x₀ : ∀ i, X i) (i : I) (y : X i) :
    (∏ j, f j (Function.update x₀ i y j)) =
      (∏ j : ({i}ᶜ : Set I), f j (x₀ j)) * f i y := by
  calc
    (∏ j, f j (Function.update x₀ i y j)) =
        (∏ j : ({i}ᶜ : Set I), f j (Function.update x₀ i y j)) *
          f i (Function.update x₀ i y i) := prod_split i _
    _ = (∏ j : ({i}ᶜ : Set I), f j (x₀ j)) * f i y := by
      apply congrArg₂ (fun a b : ℂ => a * b)
      · apply Finset.prod_congr rfl
        intro j _
        rw [Function.update_of_ne (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using j.property)]
      · simp

variable {I : Type u} [Fintype I] {V : I → Type v} {X : I → Type w}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable (E : ∀ i, V i →ₗ[ℂ] (X i → ℂ))

def localEvaluation (i : I) (x : X i) : V i →ₗ[ℂ] ℂ :=
  (LinearMap.proj x).comp (E i)

def productEvaluation : (⨂[ℂ] i, V i) →ₗ[ℂ] ((∀ i, X i) → ℂ) :=
  LinearMap.pi fun x =>
    PiTensorProduct.dualDistrib
      (PiTensorProduct.tprod ℂ (fun i => localEvaluation E i (x i)))

@[simp]
theorem productEvaluation_tprod (m : ∀ i, V i) (x : ∀ i, X i) :
    productEvaluation E (PiTensorProduct.tprod ℂ m) x =
      ∏ i, E i (m i) (x i) := by
  simp [productEvaluation, localEvaluation, PiTensorProduct.dualDistrib_apply]

set_option backward.isDefEq.respectTransparency.types false in
private theorem productEvaluation_split (i₀ : I)
    (x : ∀ j : ({i₀}ᶜ : Set I), X j) (y : X i₀) (z : ⨂[ℂ] i, V i) :
    productEvaluation E z (Function.subtypeNeLift i₀ x y) =
      TensorProduct.lid ℂ ℂ
        (TensorProduct.map
          ((LinearMap.proj x).comp
            (productEvaluation (fun j : ({i₀}ᶜ : Set I) => E j)))
          (localEvaluation E i₀ y)
          (PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V i₀ z)) := by
  let e := PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V i₀
  let f : (⨂[ℂ] (j : ({i₀}ᶜ : Set I)), V j) →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp
      (productEvaluation (fun j : ({i₀}ᶜ : Set I) => E j))
  let g := localEvaluation E i₀ y
  have h :
      (LinearMap.proj (Function.subtypeNeLift i₀ x y)).comp
          (productEvaluation E) =
        (TensorProduct.lid ℂ ℂ).toLinearMap.comp
          ((TensorProduct.map f g).comp e.toLinearMap) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    change productEvaluation E (PiTensorProduct.tprod ℂ m)
        (Function.subtypeNeLift i₀ x y) =
      TensorProduct.lid ℂ ℂ
        (TensorProduct.map f g (e (PiTensorProduct.tprod ℂ m)))
    rw [show e (PiTensorProduct.tprod ℂ m) =
        (PiTensorProduct.tprod ℂ (fun j : ({i₀}ᶜ : Set I) => m j)) ⊗ₜ[ℂ] m i₀
      from PiTensorProduct.equivPiTensorComplSingletonTensor_tprod ℂ V i₀ m]
    simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul]
    change productEvaluation E (PiTensorProduct.tprod ℂ m)
        (Function.subtypeNeLift i₀ x y) =
      productEvaluation (fun j : ({i₀}ᶜ : Set I) => E j)
          (PiTensorProduct.tprod ℂ (fun j : ({i₀}ᶜ : Set I) => m j)) x *
        E i₀ (m i₀) y
    rw [productEvaluation_tprod, productEvaluation_tprod, prod_split i₀]
    simp only [Function.subtypeNeLift_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [Function.subtypeNeLift_of_neq _ _ _ _ (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using j.property)]
    rfl
  exact DFunLike.congr_fun h z

theorem productEvaluation_eq_zero
    (hE : ∀ i, Function.Injective (E i)) (z : ⨂[ℂ] i, V i)
    (hz : ∀ x, productEvaluation E z x = 0) : z = 0 := by
  obtain ⟨n, hI⟩ : ∃ n : ℕ, Nat.card I = n := ⟨_, rfl⟩
  induction n generalizing I with
  | zero =>
    haveI : IsEmpty I :=
      (Nat.card_eq_zero.1 hI).resolve_right <| Finite.not_infinite (inferInstance : Finite I)
    let x : ∀ i, X i := fun i => isEmptyElim i
    let m : ∀ i, V i := fun i => isEmptyElim i
    let p : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ :=
      (LinearMap.proj x).comp (productEvaluation E)
    let q : ℂ →ₗ[ℂ] (⨂[ℂ] i, V i) :=
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (PiTensorProduct.tprod ℂ m)
    have hqp : q.comp p = LinearMap.id := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro v
      have hv : v = m := Subsingleton.elim _ _
      simp [p, q, hv, productEvaluation_tprod]
    have hp : p z = 0 := hz x
    have hz' : q (p z) = z := DFunLike.congr_fun hqp z
    rw [hp, map_zero] at hz'
    exact hz'.symm
  | succ n hn =>
    haveI : Nonempty I :=
      ((Nat.card_pos_iff (α := I)).1 (by rw [hI]; exact Nat.succ_pos _)).1
    let i₀ : I := Classical.arbitrary I
    let E' : ∀ j : ({i₀}ᶜ : Set I), V j →ₗ[ℂ] (X j → ℂ) := fun j => E j
    let e := PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V i₀
    let f : (∀ j : ({i₀}ᶜ : Set I), X j) →
        (⨂[ℂ] (j : ({i₀}ᶜ : Set I)), V j) →ₗ[ℂ] ℂ :=
      fun x => (LinearMap.proj x).comp (productEvaluation E')
    let g : X i₀ → V i₀ →ₗ[ℂ] ℂ := fun y => localEvaluation E i₀ y
    have hcard : Nat.card ({i₀}ᶜ : Set I) = n :=
      Set.ncard_compl_of_ncard_eq_add _ (by simpa using hI)
    apply e.injective
    rw [map_zero]
    refine TauCeti.tensor_eq_zero_of_forall_lid_map_eq_zero f g ?_ ?_ (e z) ?_
    · intro w hw
      apply hn (E := E') (hE := fun j => hE j) (z := w)
      · intro x
        exact hw x
      · exact hcard
    · intro w hw
      apply hE i₀
      funext y
      simpa [g, localEvaluation] using hw y
    · intro x y
      exact (productEvaluation_split E i₀ x y z).symm.trans (hz _)

theorem productEvaluation_injective (hE : ∀ i, Function.Injective (E i)) :
    Function.Injective (productEvaluation E) := by
  intro z w h
  apply sub_eq_zero.mp
  apply productEvaluation_eq_zero E hE (z - w)
  intro x
  rw [map_sub, Pi.sub_apply, congrFun h x, sub_self]

theorem exists_slice_vector (z : ⨂[ℂ] i, V i) (x₀ : ∀ i, X i) (i : I) :
    ∃ c : V i, ∀ y, E i c y =
      productEvaluation E z (Function.update x₀ i y) := by
  let S : (⨂[ℂ] j, V j) →ₗ[ℂ] (X i → ℂ) :=
    LinearMap.pi fun y =>
      (LinearMap.proj (Function.update x₀ i y)).comp (productEvaluation E)
  have hS : (E i).range.mkQ.comp S = 0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    change (E i).range.mkQ (S (PiTensorProduct.tprod ℂ m)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨(∏ j : ({i}ᶜ : Set I), E j (m j) (x₀ j)) • m i, ?_⟩
    funext y
    change E i ((∏ j : ({i}ᶜ : Set I), E j (m j) (x₀ j)) • m i) y =
      productEvaluation E (PiTensorProduct.tprod ℂ m) (Function.update x₀ i y)
    rw [map_smul, Pi.smul_apply, smul_eq_mul, productEvaluation_tprod]
    exact (prod_update (fun j => E j (m j)) x₀ i y).symm
  have hmem : S z ∈ (E i).range := by
    have h := DFunLike.congr_fun hS z
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, fun y => congrFun hc y⟩

theorem exists_normalized_factors
    (hE : ∀ i, Function.Injective (E i)) (z : ⨂[ℂ] i, V i)
    (x₀ : ∀ i, X i) (a : ℂ) (ha : a ≠ 0)
    (hbase : productEvaluation E z x₀ = a)
    (hfactor : ∀ x, productEvaluation E z x =
      a * ∏ i, productEvaluation E z (Function.update x₀ i (x i)) / a) :
    ∃ u : ∀ i, V i,
      (∀ i, E i (u i) (x₀ i) = 1) ∧
      (∀ i y, E i (u i) y = productEvaluation E z (Function.update x₀ i y) / a) ∧
      z = a • PiTensorProduct.tprod ℂ u := by
  choose c hc using fun i => exists_slice_vector E z x₀ i
  let u : ∀ i, V i := fun i => a⁻¹ • c i
  have hu (i : I) (y : X i) :
      E i (u i) y = productEvaluation E z (Function.update x₀ i y) / a := by
    change E i (a⁻¹ • c i) y = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hc i y]
    simp [div_eq_mul_inv, mul_comm]
  have hnorm (i : I) : E i (u i) (x₀ i) = 1 := by
    rw [hu i (x₀ i), Function.update_eq_self, hbase, div_self ha]
  refine ⟨u, hnorm, hu, ?_⟩
  apply productEvaluation_injective E hE
  funext x
  rw [map_smul, Pi.smul_apply, smul_eq_mul, productEvaluation_tprod]
  simpa only [hu] using hfactor x

theorem exists_pure_of_factorization
    (hE : ∀ i, Function.Injective (E i)) (z : ⨂[ℂ] i, V i)
    (x₀ : ∀ i, X i) (a : ℂ) (ha : a ≠ 0)
    (hbase : productEvaluation E z x₀ = a)
    (hfactor : ∀ x, productEvaluation E z x =
      a * ∏ i, productEvaluation E z (Function.update x₀ i (x i)) / a)
    (i₀ : I) : ∃ v : ∀ i, V i, z = PiTensorProduct.tprod ℂ v := by
  obtain ⟨u, _, _, hz⟩ := exists_normalized_factors E hE z x₀ a ha hbase hfactor
  refine ⟨Function.update u i₀ (a • u i₀), ?_⟩
  have hslot : PiTensorProduct.tprod ℂ (Function.update u i₀ (a • u i₀)) =
      a • PiTensorProduct.tprod ℂ u := by
    simpa only [MultilinearMap.toLinearMap_apply, Function.update_eq_self] using
      (((PiTensorProduct.tprod ℂ).toLinearMap u i₀).map_smul a (u i₀))
  exact hz.trans hslot.symm

theorem exists_pure_of_product
    (hE : ∀ i, Function.Injective (E i)) (z : ⨂[ℂ] i, V i)
    (x₀ : ∀ i, X i) (a : ℂ) (ha : a ≠ 0)
    (f : ∀ i, X i → ℂ) (hnorm : ∀ i, f i (x₀ i) = 1)
    (hfactor : ∀ x, productEvaluation E z x = a * ∏ i, f i (x i))
    (i₀ : I) : ∃ v : ∀ i, V i, z = PiTensorProduct.tprod ℂ v := by
  have hbase : productEvaluation E z x₀ = a := by
    simpa only [hnorm, Finset.prod_const_one, mul_one] using hfactor x₀
  have hslice (i : I) (y : X i) :
      productEvaluation E z (Function.update x₀ i y) / a = f i y := by
    rw [hfactor, prod_update f x₀ i y]
    simp [hnorm, ha]
  apply exists_pure_of_factorization E hE z x₀ a ha hbase ?_ i₀
  intro x
  simpa only [hslice] using hfactor x

end DedekindZetaZeroFree.ResidualTensorRecovery
