module

public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ScalarAbsorption
universe u v
variable {A : Type u} {Q : Type v} (V : Q → Type)
  [∀ q, AddCommGroup (V q)] [∀ q, Module ℂ (V q)]

abbrev FullV : A ⊕ Q → Type
  | .inl _ => ℂ
  | .inr q => V q
instance (j : A ⊕ Q) : AddCommGroup (FullV V j) := by cases j <;> dsimp [FullV] <;> infer_instance
instance (j : A ⊕ Q) : Module ℂ (FullV V j) := by cases j <;> dsimp [FullV] <;> infer_instance

 def scalarEquiv (J : Type*) [Fintype J] : PiTensorProduct ℂ (fun _ : J => ℂ) ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofLinearMap (PiTensorProduct.lift (MultilinearMap.mkPiRing ℂ J (1 : ℂ)))
    (LinearMap.toSpanSingleton ℂ _ (PiTensorProduct.tprod ℂ (fun _ => (1 : ℂ))))
    (by
      apply LinearMap.ext
      intro c
      simp [PiTensorProduct.lift.tprod])
    (by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearMap.id_apply, PiTensorProduct.lift.tprod, MultilinearMap.mkPiRing_apply,
        smul_eq_mul, mul_one, LinearMap.toSpanSingleton_apply]
      have h := (PiTensorProduct.tprod ℂ (s := fun _ : J => ℂ)).map_smul_univ x (fun _ => 1)
      simpa only [smul_eq_mul, mul_one] using h.symm)

 def split (s : Finset (A ⊕ Q)) : s ≃ s.toLeft ⊕ s.toRight where
  toFun j := match j with
    | ⟨.inl a, ha⟩ => .inl ⟨a, Finset.mem_toLeft.mpr ha⟩
    | ⟨.inr q, hq⟩ => .inr ⟨q, Finset.mem_toRight.mpr hq⟩
  invFun j := match j with
    | .inl a => ⟨.inl a.val, Finset.mem_toLeft.mp a.property⟩
    | .inr q => ⟨.inr q.val, Finset.mem_toRight.mp q.property⟩
  left_inv j := by rcases j with ⟨a | q, h⟩ <;> rfl
  right_inv j := by cases j <;> rfl

 def slotEquiv (s : Finset (A ⊕ Q)) (j : s.toLeft ⊕ s.toRight) :
    FullV V ((split s).symm j).val ≃ₗ[ℂ]
      FullV (fun q : s.toRight => V q.val) j := by
  cases j with
  | inl a => exact LinearEquiv.refl ℂ ℂ
  | inr q => exact LinearEquiv.refl ℂ (V q.val)

def stageEquiv (s : Finset (A ⊕ Q)) :
    RestrictedTensorSimple.Stage (FullV V) s ≃ₗ[ℂ] RestrictedTensorSimple.Stage V s.toRight :=
  (PiTensorProduct.reindex ℂ (fun j : s => FullV V j.val) (split s)).trans
    ((PiTensorProduct.congr (slotEquiv V s)).trans ((PiTensorProduct.tmulEquivDep ℂ
      (FullV (fun q : s.toRight => V q.val) : s.toLeft ⊕ s.toRight → Type)).symm.trans
      ((TensorProduct.congr (scalarEquiv s.toLeft) (LinearEquiv.refl ℂ _)).trans
        (TensorProduct.lid ℂ _))))

theorem stageEquiv_pure (s : Finset (A ⊕ Q))
    (x : ∀ j : s, FullV V j.val) :
    stageEquiv V s (PiTensorProduct.tprod ℂ x) =
      (∏ a : s.toLeft, x ⟨.inl a.val, Finset.mem_toLeft.mp a.property⟩) •
        PiTensorProduct.tprod ℂ (fun q : s.toRight =>
          x ⟨.inr q.val, Finset.mem_toRight.mp q.property⟩) := by
  simp only [stageEquiv, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    PiTensorProduct.congr_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.lid_tmul]
  change (scalarEquiv s.toLeft (PiTensorProduct.tprod ℂ (fun a =>
    x ⟨.inl a.val, Finset.mem_toLeft.mp a.property⟩))) •
      PiTensorProduct.tprod ℂ (fun q : s.toRight => x ⟨.inr q.val, Finset.mem_toRight.mp q.property⟩) = _
  simp [scalarEquiv, PiTensorProduct.lift.tprod, MultilinearMap.mkPiRing_apply]

 instance level_nonempty {J : Type*} (E : Finset J) :
    Nonempty (RestrictedTensorSimple.Level E) := ⟨⟨E, le_rfl⟩⟩

variable [Fintype A]

abbrev fullReference (e : ∀ q, V q) : ∀ j : A ⊕ Q, FullV V j
  | .inl _ => 1
  | .inr q => e q

def fullBad (E : Finset Q) : Finset (A ⊕ Q) := Finset.univ.disjSum E

def rightLevel (E : Finset Q) (s : RestrictedTensorSimple.Level (fullBad (A := A) E)) :
    RestrictedTensorSimple.Level E :=
  ⟨s.val.toRight, by intro q hq; exact Finset.mem_toRight.mpr (s.property (by simp [fullBad, hq]))⟩

private theorem left_eq_univ (E : Finset Q)
    (s : RestrictedTensorSimple.Level (fullBad (A := A) E)) : s.val.toLeft = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro a
  exact Finset.mem_toLeft.mpr (s.property (by simp [fullBad]))

 theorem stageEquiv_insert (e : ∀ q, V q) (E : Finset Q)
    (s t : RestrictedTensorSimple.Level (fullBad (A := A) E)) (hst : s ≤ t) :
    (stageEquiv V t.val).toLinearMap.comp
      (RestrictedTensorSimple.transition (FullV V) (fullReference V e) (fullBad E) s t hst) =
    (RestrictedTensorSimple.transition V e E (rightLevel E s) (rightLevel E t)
      (Finset.toRight_subset_toRight hst)).comp (stageEquiv V s.val).toLinearMap := by
  classical
  letI : DecidableEq (A ⊕ Q) := fun a b => Classical.propDecidable (a = b)
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change stageEquiv V t.val
    (RestrictedTensorSimple.insert (FullV V) (fullReference V e) s.val t.val hst
      (PiTensorProduct.tprod ℂ x)) =
    RestrictedTensorSimple.insert V e s.val.toRight t.val.toRight _
      (stageEquiv V s.val (PiTensorProduct.tprod ℂ x))
  rw [RestrictedTensorSimple.insert_pure, stageEquiv_pure, stageEquiv_pure,
    map_smul, RestrictedTensorSimple.insert_pure]
  have hl : t.val.toLeft = s.val.toLeft := (left_eq_univ E t).trans (left_eq_univ E s).symm
  have hp : (∏ a : t.val.toLeft,
      (if h : (.inl a.val : A ⊕ Q) ∈ s.val then x ⟨.inl a.val, h⟩
       else fullReference V e (.inl a.val))) =
      ∏ a : s.val.toLeft, x ⟨.inl a.val, Finset.mem_toLeft.mp a.property⟩ := by
    have hm (a : A) : (.inl a : A ⊕ Q) ∈ s.val := s.property (by simp [fullBad])
    simp only [dif_pos (hm _)]
    exact Fintype.prod_equiv (Set.equivOfEq (congrArg (fun r : Finset A => (r : Set A)) hl))
      _ _ (by intro a; rfl)
  change ((∏ a : t.val.toLeft,
      (if h : (.inl a.val : A ⊕ Q) ∈ s.val then x ⟨.inl a.val, h⟩
       else fullReference V e (.inl a.val))) •
      PiTensorProduct.tprod ℂ (fun q : t.val.toRight =>
        if h : (.inr q.val : A ⊕ Q) ∈ s.val then x ⟨.inr q.val, h⟩
        else fullReference V e (.inr q.val))) =
      (∏ a : s.val.toLeft, x ⟨.inl a.val, Finset.mem_toLeft.mp a.property⟩) •
      PiTensorProduct.tprod ℂ (fun q : t.val.toRight =>
        if h : q.val ∈ s.val.toRight then x ⟨.inr q.val, Finset.mem_toRight.mp h⟩ else e q.val)
  rw [hp]
  congr 2
  funext q
  by_cases hq : q.val ∈ s.val.toRight
  · simp [Finset.mem_toRight.mp hq, hq]
  · simp [show (.inr q.val : A ⊕ Q) ∉ s.val from fun h => hq (Finset.mem_toRight.mpr h), hq,
      fullReference]

def absorb (e : ∀ q, V q) (E : Finset Q) :
    RestrictedTensorSimple.Core (FullV V) (fullReference V e) (fullBad (A := A) E) →ₗ[ℂ]
      RestrictedTensorSimple.Core V e E :=
  Module.DirectLimit.lift ℂ _ _ _
    (fun s => (RestrictedTensorSimple.stageInclusion V e E (rightLevel E s)).comp
      (stageEquiv V s.val).toLinearMap)
    (by
      intro s t hst x
      change ((RestrictedTensorSimple.stageInclusion V e E (rightLevel E t)).comp
        ((stageEquiv V t.val).toLinearMap.comp
          (RestrictedTensorSimple.transition (FullV V) (fullReference V e) (fullBad E) s t hst))) x = _
      rw [stageEquiv_insert V e E s t hst]
      exact Module.DirectLimit.of_f)

theorem absorb_stage (e : ∀ q, V q) (E : Finset Q)
    (s : RestrictedTensorSimple.Level (fullBad (A := A) E))
    (x : RestrictedTensorSimple.Stage (FullV V) s.val) :
    absorb V e E (RestrictedTensorSimple.stageInclusion (FullV V) (fullReference V e)
      (fullBad E) s x) =
    RestrictedTensorSimple.stageInclusion V e E (rightLevel E s) (stageEquiv V s.val x) := by
  unfold absorb RestrictedTensorSimple.stageInclusion
  rw [Module.DirectLimit.lift_of]
  rfl

theorem absorb_injective (e : ∀ q, V q) (E : Finset Q)
    (he : ∀ q ∉ E, e q ≠ 0) : Function.Injective (absorb (A := A) V e E) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨s, x, rfl⟩ := Module.DirectLimit.exists_of z
  change absorb V e E (RestrictedTensorSimple.stageInclusion (FullV V) (fullReference V e)
    (fullBad E) s x) = 0 at hz
  rw [absorb_stage] at hz
  have hx : stageEquiv V s.val x = 0 :=
    RestrictedTensorSimple.stageInclusion_injective V e E he (rightLevel E s)
      (hz.trans (map_zero _).symm)
  have hx0 : x = 0 := (stageEquiv V s.val).injective (hx.trans (map_zero _).symm)
  rw [hx0, map_zero]
  exact Submodule.zero_mem _

theorem absorb_surjective (e : ∀ q, V q) (E : Finset Q) :
    Function.Surjective (absorb (A := A) V e E) := by
  intro z
  obtain ⟨s, x, rfl⟩ := Module.DirectLimit.exists_of z
  let t : RestrictedTensorSimple.Level (fullBad (A := A) E) :=
    ⟨Finset.univ.disjSum s.val, Finset.disjSum_mono le_rfl s.property⟩
  have ht : t.val.toRight = s.val := Finset.toRight_disjSum
  let y : RestrictedTensorSimple.Stage V t.val.toRight :=
    Eq.mp (congrArg (RestrictedTensorSimple.Stage V) ht.symm) x
  refine ⟨RestrictedTensorSimple.stageInclusion (FullV V) (fullReference V e) (fullBad E) t
    ((stageEquiv V t.val).symm y), ?_⟩
  rw [absorb_stage, LinearEquiv.apply_symm_apply]
  have general (T S : Finset Q) (hTS : T = S) (hE : E ⊆ T) (hES : E ⊆ S)
      (x : RestrictedTensorSimple.Stage V S) :
      RestrictedTensorSimple.stageInclusion V e E ⟨T, hE⟩
        (Eq.mp (congrArg (RestrictedTensorSimple.Stage V) hTS.symm) x) =
        RestrictedTensorSimple.stageInclusion V e E ⟨S, hES⟩ x := by
    subst T
    rfl
  exact general t.val.toRight s.val ht (rightLevel E t).property s.property x

def equivalence (e : ∀ q, V q) (E : Finset Q)
    (he : ∀ q ∉ E, e q ≠ 0) :
    RestrictedTensorSimple.Core (FullV V) (fullReference V e) (fullBad (A := A) E) ≃ₗ[ℂ]
      RestrictedTensorSimple.Core V e E :=
  LinearEquiv.ofBijective (absorb V e E)
    ⟨absorb_injective V e E he, absorb_surjective V e E⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ScalarAbsorption

end
