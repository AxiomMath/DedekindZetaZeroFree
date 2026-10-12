module

public import DedekindZetaZeroFree.Theta.Periods.RestrictedTensorProductFunctional

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation
universe u v
variable {J : Type u} [Fintype J] [DecidableEq J] {V : J → Type v}
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

theorem multilinear_factorization_of_normalized
    (m : MultilinearMap ℂ V ℂ) (W : ∀ j, Submodule ℂ (V j →ₗ[ℂ] ℂ))
    (hmem : ∀ x j, m.toLinearMap x j ∈ W j)
    (hdim : ∀ j, Module.finrank ℂ (W j) = 1)
    (ell : ∀ j, V j →ₗ[ℂ] ℂ) (hell : ∀ j, ell j ∈ W j)
    (x₀ : ∀ j, V j) (hnorm : ∀ j, ell j (x₀ j) = 1) :
    ∀ x, m x = m x₀ * ∏ j, ell j (x j) := by
  have slot (x : ∀ j, V j) (i : J) (y : V i) :
      m (Function.update x i y) = m (Function.update x i (x₀ i)) * ell i y := by
    have hn : (⟨ell i, hell i⟩ : W i) ≠ 0 := by
      intro h
      have hh := congrArg (fun f : W i => f.val (x₀ i)) h
      exact one_ne_zero (by simpa only [hnorm, ZeroMemClass.coe_zero, LinearMap.zero_apply] using hh)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (hdim i)
      (x := (⟨ell i, hell i⟩ : W i)) hn (⟨m.toLinearMap x i, hmem x i⟩ : W i)
    have hc' : c • ell i = m.toLinearMap x i := congrArg Subtype.val hc
    have hce : c = m (Function.update x i (x₀ i)) := by
      simpa only [LinearMap.smul_apply, hnorm, smul_eq_mul, mul_one,
        MultilinearMap.toLinearMap_apply] using congrArg (fun f : V i →ₗ[ℂ] ℂ => f (x₀ i)) hc'
    rw [← MultilinearMap.toLinearMap_apply, ← hc', LinearMap.smul_apply, smul_eq_mul, hce]
  have finite_product (s : Finset J) : ∀ x : ∀ j, V j,
      (∀ j, x j ≠ x₀ j → j ∈ s) → m x = m x₀ * ∏ j ∈ s, ell j (x j) := by
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      have he : x = x₀ := funext (fun j => by
        by_contra hn
        exact Finset.notMem_empty j (hx j hn))
      simp [he]
    | @insert i s hi ih =>
      intro x hx
      let y := Function.update x i (x₀ i)
      have hy : ∀ j, y j ≠ x₀ j → j ∈ s := by
        intro j hj
        have hji : j ≠ i := by
          intro h; subst j; exact hj (by simp [y])
        have hjx : x j ≠ x₀ j := by simpa only [y, Function.update_of_ne hji] using hj
        exact (Finset.mem_insert.mp (hx j hjx)).resolve_left hji
      have hp : (∏ j ∈ s, ell j (y j)) = ∏ j ∈ s, ell j (x j) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hi hj
        simp only [y, Function.update_of_ne hji]
      have hs := slot x i (x i)
      rw [Function.update_eq_self] at hs
      rw [hs, ih y hy, hp, Finset.prod_insert hi]
      ring
  intro x
  exact finite_product Finset.univ x (fun j _ => Finset.mem_univ j)

variable {i : J}

end DedekindZetaZeroFree.FourierContinuation

end
