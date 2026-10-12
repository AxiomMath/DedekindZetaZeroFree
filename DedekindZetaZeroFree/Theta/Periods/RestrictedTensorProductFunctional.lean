module

public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation
universe u v
variable {J : Type u} (V : J → Type v)
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
variable (e : ∀ j, V j) (bad : Finset J) (ell : ∀ j, V j →ₗ[ℂ] ℂ)

def stageMultilinear (s : Finset J) : MultilinearMap ℂ (fun j : s => V j) ℂ :=
  (MultilinearMap.mkPiRing ℂ s (1 : ℂ)).compLinearMap (fun j => ell j)

@[simp] theorem stageMultilinear_apply (s : Finset J) (x : ∀ j : s, V j) :
    stageMultilinear V ell s x = ∏ j : s, ell j (x j) := by
  simp [stageMultilinear, MultilinearMap.mkPiRing_apply]

def stageFunctional (s : Finset J) : RestrictedTensorSimple.Stage V s →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift (stageMultilinear V ell s)

@[simp] theorem stageFunctional_pure (s : Finset J) (x : ∀ j : s, V j) :
    stageFunctional V ell s (PiTensorProduct.tprod ℂ x) = ∏ j : s, ell j (x j) := by
  simp [stageFunctional, PiTensorProduct.lift.tprod]

theorem stageFunctional_insert (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (s t : RestrictedTensorSimple.Level bad) (hst : s ≤ t) :
    (stageFunctional V ell t.val).comp (RestrictedTensorSimple.transition V e bad s t hst) =
      stageFunctional V ell s.val := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure, stageFunctional_pure]
  have he : ∀ j : t.val, (j : J) ∉ s.val → ell j (e j) = 1 := by
    intro j hj
    exact hnorm j (fun hb => hj (s.property hb))
  let f : J → ℂ := fun j => if h : j ∈ s.val then ell j (x ⟨j, h⟩) else 1
  have hleft : (∏ j : t.val, ell j
      (if h : (j : J) ∈ s.val then x ⟨j, h⟩ else e j)) = ∏ j : t.val, f j := by
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : (j : J) ∈ s.val
    · simp [f, hj]
    · simp [f, hj, he j hj]
  rw [hleft]
  change (∏ j : t.val, f j) = ∏ j : s.val, ell j (x j)
  rw [Finset.prod_coe_sort]
  have hprod : (∏ j ∈ t.val, f j) = ∏ j ∈ s.val, f j := by
    exact (Finset.prod_subset hst (fun j _ hj => by simp [f, hj])).symm
  rw [hprod, ← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro j _
  simp [f, j.property]

def productFunctional (hnorm : ∀ j ∉ bad, ell j (e j) = 1) :
    RestrictedTensorSimple.Core V e bad →ₗ[ℂ] ℂ :=
  Module.DirectLimit.lift ℂ _ _ _
    (fun s => stageFunctional V ell s.val)
    (fun s t hst x => LinearMap.congr_fun (stageFunctional_insert V e bad ell hnorm s t hst) x)

@[simp] theorem productFunctional_stage (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (s : RestrictedTensorSimple.Level bad) (x : ∀ j : s.val, V j) :
    productFunctional V e bad ell hnorm
      (RestrictedTensorSimple.stageInclusion V e bad s (PiTensorProduct.tprod ℂ x)) =
        ∏ j : s.val, ell j (x j) := by
  unfold productFunctional RestrictedTensorSimple.stageInclusion
  rw [Module.DirectLimit.lift_of]
  exact stageFunctional_pure V ell s.val x

theorem stageFunctional_absorb (slot : bad) (c : ℂ)
    (s : RestrictedTensorSimple.Level bad) (x : ∀ j : s.val, V j) :
    stageFunctional V (Function.update ell slot.val (c • ell slot.val)) s.val
      (PiTensorProduct.tprod ℂ x) =
        c * stageFunctional V ell s.val (PiTensorProduct.tprod ℂ x) := by
  rw [stageFunctional_pure, stageFunctional_pure]
  let i : s.val := ⟨slot.val, s.property slot.property⟩
  have hi : (fun j : s.val => Function.update ell slot.val (c • ell slot.val) j (x j)) =
      Function.update (fun j : s.val => ell j (x j)) i (c * ell i (x i)) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [i, LinearMap.smul_apply, smul_eq_mul]
    · have hj' : j.val ≠ slot.val := by
        intro hh
        exact hj (Subtype.ext hh)
      simp [Function.update_of_ne hj, Function.update_of_ne hj']
  rw [hi, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

theorem productFunctional_unique (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (L : RestrictedTensorSimple.Core V e bad →ₗ[ℂ] ℂ)
    (hL : ∀ (s : RestrictedTensorSimple.Level bad) (x : ∀ j : s.val, V j),
      L (RestrictedTensorSimple.stageInclusion V e bad s (PiTensorProduct.tprod ℂ x)) =
        ∏ j : s.val, ell j (x j)) :
    L = productFunctional V e bad ell hnorm := by
  apply LinearMap.ext
  intro z
  letI : Nonempty (RestrictedTensorSimple.Level bad) := ⟨⟨bad, le_rfl⟩⟩
  obtain ⟨s, w, rfl⟩ := Module.DirectLimit.exists_of z
  have heq : L.comp (RestrictedTensorSimple.stageInclusion V e bad s) =
      (productFunctional V e bad ell hnorm).comp
        (RestrictedTensorSimple.stageInclusion V e bad s) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hL,
      productFunctional_stage]
  exact LinearMap.congr_fun heq w

theorem absorb_reference_value (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (slot : bad) (c : ℂ) (j : J) (hj : j ∉ bad) :
    Function.update ell slot.val (c • ell slot.val) j (e j) = 1 := by
  have hjs : j ≠ slot.val := by
    intro h
    exact hj (h ▸ slot.property)
  rw [Function.update_of_ne hjs]
  exact hnorm j hj

theorem absorb_global_coefficient (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (slot : bad) (c : ℂ)
    (L : RestrictedTensorSimple.Core V e bad →ₗ[ℂ] ℂ)
    (hL : ∀ (s : RestrictedTensorSimple.Level bad) (x : ∀ j : s.val, V j),
      L (RestrictedTensorSimple.stageInclusion V e bad s (PiTensorProduct.tprod ℂ x)) =
        c * ∏ j : s.val, ell j (x j)) :
    L = productFunctional V e bad (Function.update ell slot.val (c • ell slot.val))
      (fun j hj => absorb_reference_value V e bad ell hnorm slot c j hj) := by
  apply productFunctional_unique
  intro s x
  rw [hL]
  have h := stageFunctional_absorb V bad ell slot c s x
  simpa only [stageFunctional_pure] using h.symm

end DedekindZetaZeroFree.FourierContinuation

end
