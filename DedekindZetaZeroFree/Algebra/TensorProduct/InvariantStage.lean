module

public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity

@[expose] public section

namespace DedekindZetaZeroFree.InvariantStage

open scoped TensorProduct Classical
open RestrictedTensorSimple

universe u v w a

section Coefficients

variable {K : Type*} [Field K] {I : Type u} [Fintype I]
variable (W : I → Type v) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

noncomputable def slotMap (i : I) (f : Module.End K (W i)) :
    Module.End K (⨂[K] k : I, W k) :=
  PiTensorProduct.map
    (Function.update (fun k : I => (LinearMap.id : Module.End K (W k))) i f)

theorem slotMap_pure (i : I) (f : Module.End K (W i)) (x : ∀ k, W k) :
    slotMap W i f (PiTensorProduct.tprod K x) =
      PiTensorProduct.tprod K (Function.update x i (f (x i))) := by
  classical
  rw [slotMap, PiTensorProduct.map_tprod]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k; simp
  · simp [Function.update_of_ne hk]

noncomputable def coefficientExcept (i : I) (φ : ∀ k, Module.Dual K (W k)) :
    (⨂[K] k : I, W k) →ₗ[K] W i := by
  classical
  let S : Finset I := Finset.univ.erase i
  let q (x : ∀ k, W k) (k : I) : K := φ k (x k)
  have hq : ∀ (d : DecidableEq I), letI := d; ∀ (x : ∀ k, W k) (j : I) (z : W j),
      q (Function.update x j z) = Function.update (q x) j (φ j z) := by
    intro d x j z
    funext k
    by_cases hk : k = j
    · subst k; simp [q]
    · simp [q, Function.update_of_ne hk]
  have hsame : ∀ (d : DecidableEq I), letI := d; ∀ (x : ∀ k, W k) (z : W i),
      (∏ k ∈ S, q (Function.update x i z) k) = ∏ k ∈ S, q x k := by
    intro d x z
    apply Finset.prod_congr rfl
    intro k hk
    have hki : k ≠ i := by
      intro h
      subst k
      simpa [S] using hk
    simp only [q, Function.update_of_ne hki]
  let m : MultilinearMap K W (W i) :=
    { toFun := fun x => (∏ k ∈ S, q x k) • x i
      map_update_add' := fun x j z w => by
        by_cases hj : j = i
        · subst j
          simp only [hsame, Function.update_self, smul_add]
        · have hjS : j ∈ S := by simpa [S] using hj
          simp only [hq, Finset.prod_update_of_mem hjS,
            Function.update_of_ne (Ne.symm hj), map_add, add_mul, add_smul]
      map_update_smul' := fun x j c z => by
        by_cases hj : j = i
        · subst j
          simp only [hsame, Function.update_self, smul_comm c]
        · have hjS : j ∈ S := by simpa [S] using hj
          simp only [hq, Finset.prod_update_of_mem hjS,
            Function.update_of_ne (Ne.symm hj), map_smul, smul_eq_mul,
            mul_assoc, mul_smul] }
  exact PiTensorProduct.lift m

theorem coefficientExcept_pure (i : I) (φ : ∀ k, Module.Dual K (W k))
    (x : ∀ k, W k) :
    coefficientExcept W i φ (PiTensorProduct.tprod K x) =
      (∏ k ∈ Finset.univ.erase i, φ k (x k)) • x i := by
  classical
  simp only [coefficientExcept, PiTensorProduct.lift.tprod]
  rfl

theorem coefficientExcept_slot (i : I) (φ : ∀ k, Module.Dual K (W k))
    (f : Module.End K (W i)) (z : ⨂[K] k : I, W k) :
    coefficientExcept W i φ (slotMap W i f z) =
      f (coefficientExcept W i φ z) := by
  classical
  have hmap : (coefficientExcept W i φ).comp (slotMap W i f) =
      f.comp (coefficientExcept W i φ) := by
    apply PiTensorProduct.ext
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      slotMap_pure, coefficientExcept_pure]
    have hprod :
        (∏ k ∈ Finset.univ.erase i, φ k (Function.update x i (f (x i)) k)) =
          ∏ k ∈ Finset.univ.erase i, φ k (x k) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    rw [hprod]
    simp
  exact LinearMap.congr_fun hmap z

theorem coefficientExcept_coordinate {ι : I → Type w}
    (b : ∀ k, Module.Basis (ι k) K (W k)) (i : I) (p : ∀ k, ι k)
    (z : ⨂[K] k : I, W k) :
    (Basis.piTensorProduct b).repr z p =
      (b i).coord (p i)
        (coefficientExcept W i (fun k => (b k).coord (p k)) z) := by
  classical
  have hmap : (Basis.piTensorProduct b).coord p =
      ((b i).coord (p i)).comp
        (coefficientExcept W i (fun k => (b k).coord (p k))) := by
    apply PiTensorProduct.ext
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      coefficientExcept_pure, map_smul, smul_eq_mul]
    change (Basis.piTensorProduct b).repr (PiTensorProduct.tprod K x) p =
      (∏ k ∈ Finset.univ.erase i, (b k).repr (x k) (p k)) *
        (b i).repr (x i) (p i)
    rw [Basis.piTensorProduct_repr_tprod_apply]
    simpa [mul_comm] using
      (Finset.mul_prod_erase Finset.univ
        (fun k => (b k).repr (x k) (p k)) (Finset.mem_univ i)).symm
  exact LinearMap.congr_fun hmap z

theorem slotMap_fixed_of_common_fixed {A : Type a} (i : I)
    (ρ : A → Module.End K (W i)) (P : Module.End K (W i))
    (hP : ∀ x, (∀ a, ρ a x = x) → P x = x)
    (z : ⨂[K] k : I, W k) (hz : ∀ a, slotMap W i (ρ a) z = z) :
    slotMap W i P z = z := by
  classical
  let b (k : I) := Module.Free.chooseBasis K (W k)
  apply (Basis.piTensorProduct b).repr.injective
  ext p
  have hc (a : A) :
      ρ a (coefficientExcept W i (fun k => (b k).coord (p k)) z) =
        coefficientExcept W i (fun k => (b k).coord (p k)) z := by
    rw [← coefficientExcept_slot W i (fun k => (b k).coord (p k)) (ρ a) z,
      hz a]
  rw [coefficientExcept_coordinate W b i p (slotMap W i P z),
    coefficientExcept_coordinate W b i p z, coefficientExcept_slot,
    hP _ hc]

theorem map_fixed_of_slot_fixed (f : ∀ i, Module.End K (W i))
    (z : ⨂[K] k : I, W k) (hz : ∀ i, slotMap W i (f i) z = z) :
    PiTensorProduct.map f z = z := by
  classical
  have h (q : Finset I) :
      PiTensorProduct.map (fun i => if i ∈ q then f i else LinearMap.id) z = z := by
    induction q using Finset.induction_on with
    | empty => simpa [PiTensorProduct.map_id] using (show z = z from rfl)
    | @insert i q hi ih =>
      have hmap :
          PiTensorProduct.map
            (fun k => if k ∈ Insert.insert i q then f k else LinearMap.id) =
          (PiTensorProduct.map (fun k => if k ∈ q then f k else LinearMap.id)).comp
            (slotMap W i (f i)) := by
        apply PiTensorProduct.ext
        ext x
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          PiTensorProduct.map_tprod, slotMap_pure]
        congr 1
        funext k
        by_cases hk : k = i
        · subst k; simp [hi]
        · simp [hk, Function.update_of_ne hk]
      rw [hmap, LinearMap.comp_apply, hz i]
      exact ih
  simpa using h Finset.univ

end Coefficients

section Stages

variable {J : Type u} (V : J → Type v)
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

theorem insert_contract_eq_map (e : ∀ j, V j) (s t : Finset J) (hst : s ⊆ t)
    (φ : ∀ j : t, Module.Dual ℂ (V j)) :
    (insert V e s t hst).comp (contract V s t hst φ) =
      PiTensorProduct.map (fun j : t =>
        if (j : J) ∈ s then LinearMap.id else (φ j).smulRight (e j)) := by
  classical
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    contract, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk, map_smul, insert_pure,
    PiTensorProduct.map_tprod]
  change (∏ j : t, if (j : J) ∈ s then (1 : ℂ) else φ j (x j)) •
      PiTensorProduct.tprod ℂ (fun j : t =>
        if h : (j : J) ∈ s then restrict V s t hst x ⟨j, h⟩ else e j) =
    PiTensorProduct.tprod ℂ (fun j : t =>
      (if (j : J) ∈ s then (LinearMap.id : Module.End ℂ (V j))
        else (φ j).smulRight (e j)) (x j))
  have hext :
      (fun j : t => if h : (j : J) ∈ s then restrict V s t hst x ⟨j, h⟩ else e j) =
        (fun j : t => if (j : J) ∈ s then x j else e j) := by
    funext j
    by_cases hj : (j : J) ∈ s
    · simp [hj, restrict]
    · simp [hj]
  rw [hext]
  have hfun :
      (fun j : t =>
        (if (j : J) ∈ s then (LinearMap.id : Module.End ℂ (V j))
          else (φ j).smulRight (e j)) (x j)) =
      (fun j : t =>
        (if (j : J) ∈ s then (1 : ℂ) else φ j (x j)) •
          (if (j : J) ∈ s then x j else e j)) := by
    funext j
    by_cases hj : (j : J) ∈ s <;> simp [hj, LinearMap.smulRight_apply]
  rw [hfun, (PiTensorProduct.tprod ℂ).map_smul_univ]

theorem exists_insert_of_slot_invariant (e : ∀ j, V j)
    (s t : Finset J) (hst : s ⊆ t)
    (A : t → Type a) (ρ : ∀ j : t, A j → Module.End ℂ (V j))
    (he : ∀ j : t, (j : J) ∉ s → e j ≠ 0)
    (hline : ∀ j : t, (j : J) ∉ s → ∀ x : V j,
      (∀ a, ρ j a x = x) → ∃ c : ℂ, x = c • e j)
    (z : Stage V t)
    (hz : ∀ j : t, (j : J) ∉ s → ∀ a,
      PiTensorProduct.map
        (Function.update (fun k : t => (LinearMap.id : Module.End ℂ (V k)))
          j (ρ j a)) z = z) :
    ∃ y : Stage V s, insert V e s t hst y = z := by
  classical
  let φ : ∀ j : t, Module.Dual ℂ (V j) := fun j =>
    if h : (j : J) ∈ s then 0
    else Classical.choose (Module.Projective.exists_dual_eq_one ℂ (he j h))
  have hφ (j : t) (hj : (j : J) ∉ s) : φ j (e j) = 1 := by
    simp only [φ, dif_neg hj]
    exact Classical.choose_spec (Module.Projective.exists_dual_eq_one ℂ (he j hj))
  let P (j : t) : Module.End ℂ (V j) :=
    if (j : J) ∈ s then LinearMap.id else (φ j).smulRight (e j)
  have hp (j : t) : slotMap (fun k : t => V k) j (P j) z = z := by
    by_cases hj : (j : J) ∈ s
    · simp [P, hj, slotMap, Function.update_eq_self, PiTensorProduct.map_id]
    · apply slotMap_fixed_of_common_fixed (fun k : t => V k) j (ρ j) (P j)
        (z := z) (hz := by
          intro a
          unfold slotMap
          convert hz j hj a using 1
          apply congrArg (fun f : ∀ k : t, Module.End ℂ (V k) =>
            PiTensorProduct.map f z)
          funext k
          by_cases hk : k = j
          · subst k
            simp
          · simp only [Function.update, dite_eq_right hk])
      intro x hx
      obtain ⟨c, rfl⟩ := hline j hj x hx
      simp [P, hj, LinearMap.smulRight_apply, hφ j hj]
  have hfixed := map_fixed_of_slot_fixed (fun k : t => V k) P z hp
  refine ⟨contract V s t hst φ z, ?_⟩
  change ((insert V e s t hst).comp (contract V s t hst φ)) z = z
  rw [insert_contract_eq_map V e s t hst φ]
  exact hfixed

end Stages

end DedekindZetaZeroFree.InvariantStage
