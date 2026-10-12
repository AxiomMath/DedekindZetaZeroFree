module

public import DedekindZetaZeroFree.Theta.Periods.TensorStageFactorization

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation
universe u v
variable {J : Type u} (V : J → Type v)
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
variable (e : ∀ j, V j) (bad : Finset J)
variable (L : RestrictedTensorSimple.Core V e bad →ₗ[ℂ] ℂ)

def coreStageMultilinear (s : RestrictedTensorSimple.Level bad) : MultilinearMap ℂ (fun j : s.val => V j) ℂ :=
  (L.comp (RestrictedTensorSimple.stageInclusion V e bad s)).compMultilinearMap
    (PiTensorProduct.tprod ℂ)

theorem core_factorization_one_scalar
    (W : ∀ j, Submodule ℂ (V j →ₗ[ℂ] ℂ))
    (hmem : ∀ (s : RestrictedTensorSimple.Level bad) (x : ∀ j : s.val, V j) (i : s.val),
      (coreStageMultilinear V e bad L s).toLinearMap x i ∈ W i)
    (hdim : ∀ j, Module.finrank ℂ (W j) = 1)
    (ell : ∀ j, V j →ₗ[ℂ] ℂ) (hell : ∀ j, ell j ∈ W j)
    (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (x₀ : ∀ j : bad, V j) (hx₀ : ∀ j : bad, ell j (x₀ j) = 1) :
    ∀ (s : RestrictedTensorSimple.Level bad) (x : ∀ j : s.val, V j),
      L (RestrictedTensorSimple.stageInclusion V e bad s (PiTensorProduct.tprod ℂ x)) =
        L (RestrictedTensorSimple.stageInclusion V e bad ⟨bad, le_rfl⟩
          (PiTensorProduct.tprod ℂ x₀)) * ∏ j : s.val, ell j (x j) := by
  intro s x
  let b : RestrictedTensorSimple.Level bad := ⟨bad, le_rfl⟩
  let xs : ∀ j : s.val, V j := fun j => if h : (j : J) ∈ bad then x₀ ⟨j, h⟩ else e j
  have hxs (j : s.val) : ell j (xs j) = 1 := by
    dsimp only [xs]
    split_ifs with h
    · exact hx₀ ⟨j, h⟩
    · exact hnorm j h
  have hf := multilinear_factorization_of_normalized (coreStageMultilinear V e bad L s)
    (fun j : s.val => W j) (hmem s) (fun j => hdim j)
    (fun j : s.val => ell j) (fun j => hell j) xs hxs x
  have htrans : RestrictedTensorSimple.stageInclusion V e bad s (PiTensorProduct.tprod ℂ xs) =
      RestrictedTensorSimple.stageInclusion V e bad b (PiTensorProduct.tprod ℂ x₀) := by
    have hinsert : RestrictedTensorSimple.transition V e bad b s s.property
        (PiTensorProduct.tprod ℂ x₀) = PiTensorProduct.tprod ℂ xs :=
      RestrictedTensorSimple.insert_pure V e bad s.val s.property x₀
    rw [← hinsert]
    exact Module.DirectLimit.of_f
  change L (RestrictedTensorSimple.stageInclusion V e bad s (PiTensorProduct.tprod ℂ x)) =
    L (RestrictedTensorSimple.stageInclusion V e bad s (PiTensorProduct.tprod ℂ xs)) *
      ∏ j : s.val, ell j (x j) at hf
  rw [htrans] at hf
  exact hf

theorem core_factorization_absorbed
    (W : ∀ j, Submodule ℂ (V j →ₗ[ℂ] ℂ))
    (hmem : ∀ (s : RestrictedTensorSimple.Level bad) (x : ∀ j : s.val, V j) (i : s.val),
      (coreStageMultilinear V e bad L s).toLinearMap x i ∈ W i)
    (hdim : ∀ j, Module.finrank ℂ (W j) = 1)
    (ell : ∀ j, V j →ₗ[ℂ] ℂ) (hell : ∀ j, ell j ∈ W j)
    (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (x₀ : ∀ j : bad, V j) (hx₀ : ∀ j : bad, ell j (x₀ j) = 1)
    (slot : bad) :
    let c := L (RestrictedTensorSimple.stageInclusion V e bad ⟨bad, le_rfl⟩
      (PiTensorProduct.tprod ℂ x₀))
    L = productFunctional V e bad (Function.update ell slot.val (c • ell slot.val))
      (fun j hj => absorb_reference_value V e bad ell hnorm slot c j hj) := by
  apply absorb_global_coefficient V e bad ell hnorm slot _ L
  exact core_factorization_one_scalar V e bad L W hmem hdim ell hell hnorm x₀ hx₀

theorem core_reference_detected
    (W : ∀ j, Submodule ℂ (V j →ₗ[ℂ] ℂ))
    (hmem : ∀ (s : RestrictedTensorSimple.Level bad) (x : ∀ j : s.val, V j) (i : s.val),
      (coreStageMultilinear V e bad L s).toLinearMap x i ∈ W i)
    (hdim : ∀ j, Module.finrank ℂ (W j) = 1)
    (ell : ∀ j, V j →ₗ[ℂ] ℂ) (hell : ∀ j, ell j ∈ W j)
    (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (x₀ : ∀ j : bad, V j) (hx₀ : ∀ j : bad, ell j (x₀ j) = 1)
    (hne : L ≠ 0) :
    L (RestrictedTensorSimple.stageInclusion V e bad ⟨bad, le_rfl⟩
      (PiTensorProduct.tprod ℂ x₀)) ≠ 0 := by
  intro hz
  apply hne
  apply LinearMap.ext
  intro z
  letI : Nonempty (RestrictedTensorSimple.Level bad) := ⟨⟨bad, le_rfl⟩⟩
  obtain ⟨s, w, rfl⟩ := Module.DirectLimit.exists_of z
  have hp : ∀ x : ∀ j : s.val, V j,
      L (RestrictedTensorSimple.stageInclusion V e bad s (PiTensorProduct.tprod ℂ x)) = 0 := by
    intro x
    rw [core_factorization_one_scalar V e bad L W hmem hdim ell hell hnorm x₀ hx₀, hz, zero_mul]
  change L (RestrictedTensorSimple.stageInclusion V e bad s w) = 0
  induction w using PiTensorProduct.induction_on with
  | smul_tprod c x => simp only [map_smul, hp x, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end DedekindZetaZeroFree.FourierContinuation

end
