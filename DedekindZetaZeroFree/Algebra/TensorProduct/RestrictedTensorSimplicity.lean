module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree
namespace RestrictedTensorSimple

open scoped TensorProduct Classical

universe u v a
variable {J : Type u} (V : J → Type v)
  [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

abbrev Stage (s : Finset J) := ⨂[ℂ] j : s, V j

noncomputable def extend (e : ∀ j, V j) (s t : Finset J) (x : ∀ j : s, V j) :
    ∀ j : t, V j := fun j => if h : (j : J) ∈ s then x ⟨j, h⟩ else e j

private theorem extend_update (e : ∀ j, V j) (s t : Finset J) (hst : s ⊆ t)
    [DecidableEq s] [DecidableEq t] (x : ∀ j : s, V j) (i : s) (z : V i) :
    extend V e s t (Function.update x i z) =
      Function.update (extend V e s t x) ⟨i, hst i.property⟩ z := by
  classical
  funext j
  by_cases hji : (j : J) = i
  · have hj : j = (⟨i, hst i.property⟩ : t) := Subtype.ext hji
    subst j
    simp [extend]
  · have hj : j ≠ (⟨i, hst i.property⟩ : t) := by
      intro h
      exact hji (congrArg Subtype.val h)
    rw [Function.update_of_ne hj]
    simp only [extend]
    split_ifs with h
    · rw [Function.update_of_ne (by
        intro heq
        exact hji (congrArg Subtype.val heq))]
    · rfl

theorem exists_insert (e : ∀ j, V j) (s t : Finset J) (hst : s ⊆ t) :
    ∃ f : Stage V s →ₗ[ℂ] Stage V t,
      ∀ x : ∀ j : s, V j,
        f (PiTensorProduct.tprod ℂ x) =
          PiTensorProduct.tprod ℂ (fun j : t =>
            if h : (j : J) ∈ s then x ⟨j, h⟩ else e j) := by
  classical
  let m : MultilinearMap ℂ (fun j : s => V j) (Stage V t) :=
    { toFun := fun x => PiTensorProduct.tprod ℂ (extend V e s t x)
      map_update_add' := fun x i z w => by
        simp only [extend_update V e s t hst]
        exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun x i c z => by
        simp only [extend_update V e s t hst]
        exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }
  exact ⟨PiTensorProduct.lift m, fun x => PiTensorProduct.lift.tprod x⟩

noncomputable def insert (e : ∀ j, V j) (s t : Finset J) (hst : s ⊆ t) :
    Stage V s →ₗ[ℂ] Stage V t :=
  Classical.choose (exists_insert V e s t hst)

theorem insert_pure (e : ∀ j, V j) (s t : Finset J) (hst : s ⊆ t)
    (x : ∀ j : s, V j) :
    insert V e s t hst (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (fun j : t =>
        if h : (j : J) ∈ s then x ⟨j, h⟩ else e j) :=
  (Classical.choose_spec (exists_insert V e s t hst)) x

theorem insert_refl (e : ∀ j, V j) (s : Finset J) :
    insert V e s s le_rfl = LinearMap.id := by
  classical
  apply PiTensorProduct.ext
  ext y
  simp only [LinearMap.compMultilinearMap_apply, insert_pure, LinearMap.id_apply]
  congr 1
  funext j
  simp [j.property]

theorem insert_comp (e : ∀ j, V j) (s t u : Finset J)
    (hst : s ⊆ t) (htu : t ⊆ u) :
    (insert V e t u htu).comp (insert V e s t hst) =
      insert V e s u (hst.trans htu) := by
  classical
  apply PiTensorProduct.ext
  ext y
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, insert_pure]
  congr 1
  funext j
  by_cases hs : (j : J) ∈ s
  · simp [hs, hst hs]
  · by_cases ht : (j : J) ∈ t <;> simp [hs, ht]

noncomputable def restrict (s t : Finset J) (hst : s ⊆ t)
    (x : ∀ j : t, V j) : ∀ j : s, V j := fun j => x ⟨j, hst j.property⟩

theorem restrict_update_mem (s t : Finset J) (hst : s ⊆ t)
    [DecidableEq s] [DecidableEq t] (x : ∀ j : t, V j) (i : t) (hi : (i : J) ∈ s)
    (z : V i) : restrict V s t hst (Function.update x i z) =
      Function.update (restrict V s t hst x) ⟨i, hi⟩ z := by
  funext j
  by_cases hji : (j : J) = i
  · have hj : j = (⟨i, hi⟩ : s) := Subtype.ext hji
    subst j
    simp [restrict]
  · simp only [restrict]
    rw [Function.update_of_ne (by intro h; exact hji (congrArg Subtype.val h)),
      Function.update_of_ne (by intro h; exact hji (congrArg Subtype.val h))]
    rfl

theorem restrict_update_notMem (s t : Finset J) (hst : s ⊆ t)
    [DecidableEq t] (x : ∀ j : t, V j) (i : t) (hi : (i : J) ∉ s)
    (z : V i) : restrict V s t hst (Function.update x i z) = restrict V s t hst x := by
  funext j
  simp only [restrict]
  rw [Function.update_of_ne (by
    intro h
    exact hi ((congrArg Subtype.val h) ▸ j.property))]

noncomputable def contract (s t : Finset J) (hst : s ⊆ t)
    (φ : ∀ j : t, Module.Dual ℂ (V j)) : Stage V t →ₗ[ℂ] Stage V s := by
  classical
  let p (x : ∀ j : t, V j) (j : t) : ℂ := if (j : J) ∈ s then 1 else φ j (x j)
  have hp : ∀ (d : DecidableEq t), letI := d; ∀ (x : ∀ j : t, V j) (i : t) (z : V i),
      p (Function.update x i z) = Function.update (p x) i
        (if (i : J) ∈ s then 1 else φ i z) := by
    intro d x i z
    funext j
    by_cases hj : j = i
    · subst j; simp [p]
    · simp [p, Function.update_of_ne hj]
  let m : MultilinearMap ℂ (fun j : t => V j) (Stage V s) :=
    { toFun := fun x => (∏ j, p x j) • PiTensorProduct.tprod ℂ (restrict V s t hst x)
      map_update_add' := fun x i z w => by
        by_cases hi : (i : J) ∈ s
        · have hp' (q : V i) : p (Function.update x i q) = p x := by
            rw [hp]
            simp [hi, p, Function.update_eq_self]
          simp only [hp', restrict_update_mem V s t hst _ _ hi,
            MultilinearMap.map_update_add, smul_add]
        · simp only [hp, Finset.prod_update_of_mem (Finset.mem_univ i), if_neg hi,
            restrict_update_notMem V s t hst _ _ hi, map_add, add_mul, add_smul]
      map_update_smul' := fun x i c z => by
        by_cases hi : (i : J) ∈ s
        · have hp' (q : V i) : p (Function.update x i q) = p x := by
            rw [hp]
            simp [hi, p, Function.update_eq_self]
          simp only [hp', restrict_update_mem V s t hst _ _ hi,
            MultilinearMap.map_update_smul, smul_comm c]
        · simp only [hp, Finset.prod_update_of_mem (Finset.mem_univ i), if_neg hi,
            restrict_update_notMem V s t hst _ _ hi, map_smul, smul_eq_mul,
            mul_assoc, mul_smul] }
  exact PiTensorProduct.lift m

private theorem contract_insert (e : ∀ j, V j) (s t : Finset J) (hst : s ⊆ t)
    (φ : ∀ j : t, Module.Dual ℂ (V j))
    (hφ : ∀ j : t, (j : J) ∉ s → φ j (e j) = 1) :
    (contract V s t hst φ).comp (insert V e s t hst) = LinearMap.id := by
  classical
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    insert_pure, LinearMap.id_apply, contract, PiTensorProduct.lift.tprod]
  have hprod : (∏ j : t,
      if (j : J) ∈ s then (1 : ℂ) else φ j
        (if h : (j : J) ∈ s then x ⟨j, h⟩ else e j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    split_ifs with h
    · rfl
    · exact hφ j h
  change (∏ j : t, if (j : J) ∈ s then (1 : ℂ) else φ j
    (if h : (j : J) ∈ s then x ⟨j, h⟩ else e j)) •
      PiTensorProduct.tprod ℂ (restrict V s t hst
        (fun j : t => if h : (j : J) ∈ s then x ⟨j, h⟩ else e j)) = _
  rw [hprod, one_smul]
  congr 1
  funext j
  simp [restrict, j.property]

def Level (E : Finset J) := {s : Finset J // E ⊆ s}

instance (E : Finset J) : PartialOrder (Level E) :=
  PartialOrder.lift (fun s : Level E => s.1) (fun _ _ h => Subtype.ext h)

instance (E : Finset J) : IsDirectedOrder (Level E) where
  directed s t := ⟨⟨s.1 ∪ t.1, s.property.trans Finset.subset_union_left⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩

noncomputable def transition (e : ∀ j, V j) (E : Finset J)
    (s t : Level E) (hst : s ≤ t) : Stage V s.1 →ₗ[ℂ] Stage V t.1 :=
  insert V e s.1 t.1 hst

noncomputable abbrev Core (e : ∀ j, V j) (E : Finset J) : Type _ :=
  Module.DirectLimit (R := ℂ) (ι := Level E) (G := fun s : Level E => Stage V s.1)
    (transition V e E)

noncomputable def stageInclusion (e : ∀ j, V j) (E : Finset J) (s : Level E) :
    Stage V s.1 →ₗ[ℂ] Core V e E :=
  Module.DirectLimit.of ℂ (Level E) (fun t : Level E => Stage V t.1)
    (transition V e E) s

theorem insert_injective (e : ∀ j, V j) (E : Finset J)
    (he : ∀ j ∉ E, e j ≠ 0) (s t : Level E) (hst : s ≤ t) :
    Function.Injective (transition V e E s t hst) := by
  classical
  have hnonzero (j : t.1) (hj : (j : J) ∉ s.1) : e j ≠ 0 :=
    he j (fun h => hj (s.property h))
  let φ : ∀ j : t.1, Module.Dual ℂ (V j) := fun j =>
    if h : (j : J) ∈ s.1 then 0
    else Classical.choose (Module.Projective.exists_dual_eq_one ℂ (hnonzero j h))
  have hφ (j : t.1) (hj : (j : J) ∉ s.1) : φ j (e j) = 1 := by
    simp only [φ, dif_neg hj]
    exact Classical.choose_spec (Module.Projective.exists_dual_eq_one ℂ (hnonzero j hj))
  have hleft := contract_insert V e s.1 t.1 hst φ hφ
  intro x y hxy
  have h := congrArg (contract V s.1 t.1 hst φ) hxy
  have hx := congrArg (fun f : Stage V s.1 →ₗ[ℂ] Stage V s.1 => f x) hleft
  have hy := congrArg (fun f : Stage V s.1 →ₗ[ℂ] Stage V s.1 => f y) hleft
  exact hx.symm.trans (h.trans hy)

noncomputable instance directedSystem (e : ∀ j, V j) (E : Finset J) :
    DirectedSystem (fun s : Level E => Stage V s.1)
      (fun {i j} h => transition V e E i j h) := by
  constructor
  · intro s x
    exact congrArg (fun f : Stage V s.1 →ₗ[ℂ] Stage V s.1 => f x)
      (insert_refl V e s.1)
  · intro u t s hst htu x
    exact congrArg (fun f : Stage V s.1 →ₗ[ℂ] Stage V u.1 => f x)
      (insert_comp V e s.1 t.1 u.1 hst htu)

theorem stageInclusion_injective (e : ∀ j, V j) (E : Finset J)
    (he : ∀ j ∉ E, e j ≠ 0) (s : Level E) :
    Function.Injective (stageInclusion V e E s) := by
  intro x y hxy
  obtain ⟨t, hst, ht⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
  exact insert_injective V e E he s t hst ht

section Actions

variable (A : J → Type a) [∀ j, Ring (A j)] [∀ j, Algebra ℂ (A j)]
  [∀ j, Module (A j) (V j)] [∀ j, IsScalarTower ℂ (A j) (V j)]
  [∀ j, SMulCommClass (A j) ℂ (V j)]

noncomputable def localOperator (j : J) (a : A j) : V j →ₗ[ℂ] V j where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' c x := smul_comm a c x

noncomputable def stageOperator (s : Finset J) (j : J) (hj : j ∈ s)
    (a : A j) : Module.End ℂ (Stage V s) :=
  PiTensorProduct.map (Function.update (fun k : s => (LinearMap.id : V k →ₗ[ℂ] V k))
    ⟨j, hj⟩ (localOperator V A j a))

private theorem stageOperator_pure (s : Finset J) (j : J) (hj : j ∈ s)
    (a : A j) (x : ∀ k : s, V k) :
    stageOperator V A s j hj a (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x ⟨j, hj⟩ (a • x ⟨j, hj⟩)) := by
  classical
  rw [stageOperator, PiTensorProduct.map_tprod]
  congr 1
  funext k
  by_cases h : k = ⟨j, hj⟩
  · subst k; simp [localOperator]
  · simp [Function.update_of_ne h]

private theorem stageOperator_insert (e : ∀ j, V j) (s t : Finset J)
    (hst : s ⊆ t) (j : J) (hj : j ∈ s) (a : A j) :
    (stageOperator V A t j (hst hj) a).comp (insert V e s t hst) =
      (insert V e s t hst).comp (stageOperator V A s j hj a) := by
  classical
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, insert_pure,
    stageOperator_pure]
  change PiTensorProduct.tprod ℂ (Function.update (extend V e s t x)
    ⟨j, hst hj⟩ (a • (extend V e s t x) ⟨j, hst hj⟩)) =
    PiTensorProduct.tprod ℂ (extend V e s t (Function.update x ⟨j, hj⟩ (a • x ⟨j, hj⟩)))
  rw [extend_update V e s t hst]
  simp [extend, hj]

theorem inclusion_insert (e : ∀ j, V j) (E : Finset J)
    (s t : Level E) (hst : s ≤ t) :
    (stageInclusion V e E t).comp (insert V e s.1 t.1 hst) =
      stageInclusion V e E s := by
  ext x
  exact Module.DirectLimit.of_f

theorem exists_slotAction (e : ∀ j, V j) (E : Finset J) (j : J) (a : A j) :
    ∃ f : Module.End ℂ (Core V e E),
      ∀ (s : Level E) (hj : j ∈ s.1) (x : ∀ k : s.1, V k),
        f (stageInclusion V e E s (PiTensorProduct.tprod ℂ x)) =
          stageInclusion V e E s (PiTensorProduct.tprod ℂ
            (Function.update x ⟨j, hj⟩ (a • x ⟨j, hj⟩))) := by
  classical
  let enlarge : Level E → Level E := fun s =>
    ⟨Insert.insert j s.1, s.property.trans (Finset.subset_insert j s.1)⟩
  let g (s : Level E) : Stage V s.1 →ₗ[ℂ] Core V e E :=
    (stageInclusion V e E (enlarge s)).comp
      ((stageOperator V A (enlarge s).1 j (Finset.mem_insert_self _ _) a).comp
        (insert V e s.1 (enlarge s).1 (Finset.subset_insert _ _)))
  have hg (s t : Level E) (hst : s ≤ t) :
      (g t).comp (transition V e E s t hst) = g s := by
    have hlarge : enlarge s ≤ enlarge t := Finset.insert_subset_insert j hst
    have h1 := stageOperator_insert V A e (enlarge s).1 (enlarge t).1 hlarge j
      (Finset.mem_insert_self _ _) a
    have h2 := inclusion_insert V e E (enlarge s) (enlarge t) hlarge
    dsimp [g, transition]
    simp only [LinearMap.comp_assoc]
    rw [insert_comp V e s.1 t.1 (enlarge t).1 hst]
    rw [← insert_comp V e s.1 (enlarge s).1 (enlarge t).1
      (Finset.subset_insert _ _) hlarge]
    rw [← LinearMap.comp_assoc _ _ (stageOperator V A (enlarge t).1 j _ a), h1]
    simp only [← LinearMap.comp_assoc]
    rw [h2]
  refine ⟨Module.DirectLimit.lift ℂ (Level E) (fun s : Level E => Stage V s.1)
    (transition V e E) g (fun s t hst x => LinearMap.congr_fun (hg s t hst) x), ?_⟩
  intro s hj x
  simp only [stageInclusion, Module.DirectLimit.lift_of]
  have hs : g s = (stageInclusion V e E s).comp (stageOperator V A s.1 j hj a) := by
    dsimp [g]
    rw [stageOperator_insert V A e s.1 (enlarge s).1
      (Finset.subset_insert _ _) j hj a, ← LinearMap.comp_assoc,
      inclusion_insert V e E s (enlarge s) (Finset.subset_insert _ _)]
  rw [hs, LinearMap.comp_apply, stageOperator_pure]
  rfl

noncomputable def slotAction (e : ∀ j, V j) (E : Finset J) (j : J) (a : A j) :
    Module.End ℂ (Core V e E) :=
  Classical.choose (exists_slotAction V A e E j a)

noncomputable abbrev actionAlgebra (e : ∀ j, V j) (E : Finset J) :
    Subalgebra ℂ (Module.End ℂ (Core V e E)) :=
  Algebra.adjoin ℂ {f | ∃ j a, f = slotAction V A e E j a}

noncomputable instance actionModule (e : ∀ j, V j) (E : Finset J) :
    Module (actionAlgebra V A e E) (Core V e E) :=
  Module.compHom (Core V e E) (actionAlgebra V A e E).val.toRingHom

end Actions

end RestrictedTensorSimple
end DedekindZetaZeroFree

section

namespace DedekindZetaZeroFree
namespace RestrictedTensorSimple

open scoped TensorProduct Classical

universe u v a
variable {J : Type u} (V : J → Type v)
  [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

theorem core_nontrivial (e : ∀ j, V j) (E : Finset J)
    (he : ∀ j ∉ E, e j ≠ 0) [∀ j, Nontrivial (V j)] :
    Nontrivial (Core V e E) := by
  classical
  let x : ∀ j : E, V j := fun j => Classical.choose (exists_ne (0 : V j))
  have hx (j : E) : x j ≠ 0 := Classical.choose_spec (exists_ne (0 : V j))
  let φ : ∀ j : E, Module.Dual ℂ (V j) := fun j =>
    Classical.choose (Module.Projective.exists_dual_eq_one ℂ (hx j))
  have hφ (j : E) : φ j (x j) = 1 :=
    Classical.choose_spec (Module.Projective.exists_dual_eq_one ℂ (hx j))
  let f : Module.Dual ℂ (Stage V E) :=
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ φ)
  have hfx : f (PiTensorProduct.tprod ℂ x) = 1 := by
    simp [f, PiTensorProduct.dualDistrib_apply, hφ]
  have hne : PiTensorProduct.tprod ℂ x ≠ 0 := by
    intro h
    rw [h, map_zero] at hfx
    exact zero_ne_one hfx
  let s : Level E := ⟨E, le_rfl⟩
  refine ⟨⟨stageInclusion V e E s (PiTensorProduct.tprod ℂ x), 0, ?_⟩⟩
  intro h
  apply hne
  exact stageInclusion_injective V e E he s (h.trans (map_zero _).symm)

section Actions

variable (A : J → Type a) [∀ j, Ring (A j)] [∀ j, Algebra ℂ (A j)]
  [∀ j, Module (A j) (V j)] [∀ j, IsScalarTower ℂ (A j) (V j)]
  [∀ j, SMulCommClass (A j) ℂ (V j)]

def ScalarCommutant : Prop :=
  ∀ j, ∀ f : Module.End (A j) (V j), ∃ c : ℂ, ∀ x, f x = c • x

theorem slotAction_pure (e : ∀ j, V j) (E : Finset J) (j : J) (a : A j)
    (s : Level E) (hj : j ∈ s.1) (x : ∀ k : s.1, V k) :
    slotAction V A e E j a (stageInclusion V e E s (PiTensorProduct.tprod ℂ x)) =
      stageInclusion V e E s (PiTensorProduct.tprod ℂ
        (Function.update x ⟨j, hj⟩ (a • x ⟨j, hj⟩))) :=
  Classical.choose_spec (exists_slotAction V A e E j a) s hj x

private theorem density_complex [∀ j, IsSimpleModule (A j) (V j)]
    (hcommutant : ScalarCommutant V A) (j : J) (f : Module.End ℂ (V j))
    (s : Finset (V j)) : ∃ a : A j, ∀ x ∈ s, f x = a • x := by
  let g : Module.End (Module.End (A j) (V j)) (V j) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun d x => by
        obtain ⟨c, hc⟩ := hcommutant j d
        change f (d x) = d (f x)
        rw [hc, hc, f.map_smul] }
  exact jacobson_density g s

private noncomputable def linearSlot (s : Finset J) (i : s) (f : Module.End ℂ (V i)) :
    Module.End ℂ (Stage V s) :=
  PiTensorProduct.map (Function.update (fun k : s => (LinearMap.id : V k →ₗ[ℂ] V k)) i f)

private theorem linearSlot_pure (s : Finset J) (i : s) (f : Module.End ℂ (V i))
    (x : ∀ k : s, V k) : linearSlot V s i f (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x i (f (x i))) := by
  classical
  rw [linearSlot, PiTensorProduct.map_tprod]
  congr 1
  funext k
  by_cases h : k = i
  · subst k; simp
  · simp [Function.update_of_ne h]

private theorem slot_finite_test (s : Finset J) (i : s) (x : Stage V s) :
    ∃ t : Finset (V i), ∀ f g : Module.End ℂ (V i),
      (∀ z ∈ t, f z = g z) → linearSlot V s i f x = linearSlot V s i g x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    refine ⟨{x i}, fun f g h => ?_⟩
    simp only [map_smul, linearSlot_pure, h _ (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨t, ht⟩ := hx
    obtain ⟨u, hu⟩ := hy
    refine ⟨t ∪ u, fun f g h => ?_⟩
    simp only [map_add, ht f g (fun z hz => h z (Finset.mem_union_left _ hz)),
      hu f g (fun z hz => h z (Finset.mem_union_right _ hz))]

private theorem slotAction_stage (e : ∀ j, V j) (E : Finset J) (s : Level E)
    (i : s.1) (a : A i) (x : Stage V s.1) :
    slotAction V A e E i a (stageInclusion V e E s x) =
      stageInclusion V e E s (linearSlot V s.1 i (localOperator V A i a) x) := by
  have h : (slotAction V A e E i a).comp (stageInclusion V e E s) =
      (stageInclusion V e E s).comp (linearSlot V s.1 i (localOperator V A i a)) := by
    apply PiTensorProduct.ext
    ext y
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      linearSlot_pure]
    exact slotAction_pure V A e E i a s i.property y
  exact LinearMap.congr_fun h x

private theorem linearSlot_mem [∀ j, IsSimpleModule (A j) (V j)]
    (hcommutant : ScalarCommutant V A) (e : ∀ j, V j) (E : Finset J)
    (N : Submodule (actionAlgebra V A e E) (Core V e E)) (s : Level E)
    (i : s.1) (f : Module.End ℂ (V i)) (x : Stage V s.1)
    (hx : stageInclusion V e E s x ∈ N) :
    stageInclusion V e E s (linearSlot V s.1 i f x) ∈ N := by
  obtain ⟨t, ht⟩ := slot_finite_test V s.1 i x
  obtain ⟨a, ha⟩ := density_complex V A hcommutant i f t
  rw [ht f (localOperator V A i a) ha, ← slotAction_stage V A e E s i a x]
  let b : actionAlgebra V A e E := ⟨slotAction V A e E i a,
    Algebra.subset_adjoin ⟨i, a, rfl⟩⟩
  exact N.smul_mem b hx

private theorem tensorMap_mem [∀ j, IsSimpleModule (A j) (V j)]
    (hcommutant : ScalarCommutant V A) (e : ∀ j, V j) (E : Finset J)
    (N : Submodule (actionAlgebra V A e E) (Core V e E)) (s : Level E)
    (f : ∀ i : s.1, Module.End ℂ (V i)) (x : Stage V s.1)
    (hx : stageInclusion V e E s x ∈ N) :
    stageInclusion V e E s (PiTensorProduct.map f x) ∈ N := by
  classical
  have h (t : Finset s.1) : stageInclusion V e E s
      (PiTensorProduct.map (fun i => if i ∈ t then f i else LinearMap.id) x) ∈ N := by
    induction t using Finset.induction_on with
    | empty => simpa [PiTensorProduct.map_id] using hx
    | @insert i t hi ih =>
      have hmap : PiTensorProduct.map (fun k => if k ∈ Insert.insert i t then f k else LinearMap.id) =
          (linearSlot V s.1 i (f i)).comp
            (PiTensorProduct.map (fun k => if k ∈ t then f k else LinearMap.id)) := by
        apply PiTensorProduct.ext
        ext y
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          PiTensorProduct.map_tprod, linearSlot_pure]
        congr 1
        funext k
        by_cases hk : k = i
        · subst k; simp [hi]
        · simp [hk, Function.update_of_ne hk]
      rw [hmap, LinearMap.comp_apply]
      exact linearSlot_mem V A hcommutant e E N s i (f i) _ ih
  simpa using h Finset.univ

private theorem stage_cyclic [∀ j, IsSimpleModule (A j) (V j)]
    (hcommutant : ScalarCommutant V A) (e : ∀ j, V j) (E : Finset J)
    (N : Submodule (actionAlgebra V A e E) (Core V e E)) (s : Level E)
    (x : Stage V s.1) (hzero : x ≠ 0) (hx : stageInclusion V e E s x ∈ N) :
    ∀ z : Stage V s.1, stageInclusion V e E s z ∈ N := by
  classical
  have scalar_mem (c : ℂ) (z : Core V e E) (hz : z ∈ N) : c • z ∈ N := by
    exact N.smul_mem (algebraMap ℂ (actionAlgebra V A e E) c) hz
  let b (i : s.1) := Module.Free.chooseBasis ℂ (V i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr x p ≠ 0 := by
    by_contra h
    apply hzero
    apply B.repr.injective
    ext p
    simp only [map_zero, Finsupp.zero_apply]
    exact not_ne_iff.mp (not_exists.mp h p)
  have hpure (y : ∀ i : s.1, V i) : stageInclusion V e E s (PiTensorProduct.tprod ℂ y) ∈ N := by
    let f (i : s.1) : Module.End ℂ (V i) := (b i).coord (p i) |>.smulRight (y i)
    have hmap : PiTensorProduct.map f = (B.coord p).smulRight (PiTensorProduct.tprod ℂ y) := by
      apply PiTensorProduct.ext
      ext z
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.smulRight_apply]
      change PiTensorProduct.tprod ℂ (fun i => (b i).repr (z i) (p i) • y i) =
        B.repr (PiTensorProduct.tprod ℂ z) p • PiTensorProduct.tprod ℂ y
      rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
      rw [Basis.piTensorProduct_repr_tprod_apply]
    have hm := tensorMap_mem V A hcommutant e E N s f x hx
    rw [hmap, LinearMap.smulRight_apply, map_smul] at hm
    have hm' := scalar_mem ((B.repr x p)⁻¹) _ hm
    simpa [smul_smul, hp] using hm'
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    rw [map_smul]
    exact scalar_mem c _ (hpure y)
  | add z w hz hw => simpa using N.add_mem hz hw

theorem core_simple (e : ∀ j, V j) (E : Finset J)
    (he : ∀ j ∉ E, e j ≠ 0) [∀ j, Nontrivial (V j)]
    [∀ j, IsSimpleModule (A j) (V j)] (hcommutant : ScalarCommutant V A) :
    IsSimpleOrder (Submodule (actionAlgebra V A e E) (Core V e E)) := by
  classical
  letI : Nonempty (Level E) := ⟨⟨E, le_rfl⟩⟩
  letI : Nontrivial (Core V e E) := core_nontrivial V e E he
  apply (isSimpleOrder_iff _).mpr
  refine ⟨(Submodule.nontrivial_iff _).mpr inferInstance, fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨z, hz, hzero⟩ := (Submodule.ne_bot_iff N).mp hN
  obtain ⟨s, x, hx⟩ := Module.DirectLimit.exists_of z
  change stageInclusion V e E s x = z at hx
  have hxn : x ≠ 0 := by
    intro h; apply hzero; rw [← hx, h, map_zero]
  apply Submodule.eq_top_iff'.mpr
  intro w
  obtain ⟨t, y, hy⟩ := Module.DirectLimit.exists_of w
  change stageInclusion V e E t y = w at hy
  obtain ⟨r, hsr, htr⟩ := exists_ge_ge s t
  let xr := transition V e E s r hsr x
  have hxr : stageInclusion V e E r xr = z := by
    exact (LinearMap.congr_fun (inclusion_insert V e E s r hsr) x).trans hx
  have hxrn : xr ≠ 0 := by
    intro h; apply hzero; rw [← hxr, h, map_zero]
  have hm := stage_cyclic V A hcommutant e E N r xr hxrn (hxr.symm ▸ hz)
    (transition V e E t r htr y)
  have hyr := (LinearMap.congr_fun (inclusion_insert V e E t r htr) y).trans hy
  exact hyr ▸ hm

end Actions

theorem scalarCommutant_of_finiteLevel
    (A : Type a) [Ring A] [Algebra ℂ A]
    (W : Type v) [AddCommGroup W] [Module ℂ W] [Module A W]
    [IsScalarTower ℂ A W] [SMulCommClass A ℂ W] [IsSimpleModule A W]
    (L : Submodule ℂ W) [Module.Finite ℂ L] (hL : L ≠ ⊥)
    (hpreserve : ∀ f : Module.End A W, ∀ x ∈ L, f x ∈ L) :
    ∀ f : Module.End A W, ∃ c : ℂ, ∀ x, f x = c • x := by
  classical
  intro f
  haveI : Nontrivial L := (Submodule.nontrivial_iff_ne_bot).mpr hL
  let g : Module.End ℂ L :=
    { toFun := fun x => ⟨f x, hpreserve f x x.property⟩
      map_add' := fun x y => Subtype.ext (f.map_add x y)
      map_smul' := fun c x => Subtype.ext (by
        change f (c • (x : W)) = c • f (x : W)
        exact f.map_smul_of_tower c x) }
  obtain ⟨c, hc⟩ := g.exists_eigenvalue
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  let d : Module.End A W := f - c • LinearMap.id
  have hdx : d (x : W) = 0 := by
    have h := congrArg Subtype.val hx.apply_eq_smul
    change f (x : W) = c • (x : W) at h
    change f (x : W) - c • (x : W) = 0
    exact sub_eq_zero.mpr h
  have hd : d = 0 := by
    rcases d.injective_or_eq_zero with hinj | hz
    · have : (x : W) = 0 := hinj (hdx.trans d.map_zero.symm)
      exact False.elim (hx.2 (Subtype.ext this))
    · exact hz
  refine ⟨c, fun y => ?_⟩
  have h := congrArg (fun q : Module.End A W => q y) hd
  exact sub_eq_zero.mp h

end RestrictedTensorSimple
end DedekindZetaZeroFree

end
