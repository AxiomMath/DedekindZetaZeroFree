module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

noncomputable section

open scoped BigOperators

namespace DedekindZetaZeroFree.RightFrame.PullbackWords

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {B : Type*}

def directionalWord (fields : B → E → E) : List B → (E → ℂ) → E → ℂ
  | [], u => u
  | b :: r, u => fun x => fderiv ℝ (directionalWord fields r u) x (fields b x)

def constantDirectionWord (w : List P) (u : P → ℂ) : P → ℂ :=
  directionalWord (fun (v : P) (_ : P) => v) w u

section TransportProof
open Topology
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [Fintype B]

private lemma inverse_coefficients (U : Set E) (O : Set P) (hU : IsOpen U) (hO : IsOpen O)
    (fields : B → E → E) (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (ψ : P → E) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ O) (hψU : Set.MapsTo ψ O U)
    (v : P) :
    ∃ a : B → P → ℝ, (∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (a b) O) ∧
      ∀ x ∈ O, fderiv ℝ ψ x v = ∑ b, a b x • fields b (ψ x) := by
  let A : E → (B → ℝ) →L[ℝ] E := fun x =>
    ∑ b, (ContinuousLinearMap.proj b).smulRight (fields b x)
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A U := by
    apply ContDiffOn.sum
    intro b _
    exact contDiffOn_const.smulRight (hfields b)
  have hAe (x : E) (hx : x ∈ U) : ∃ e : (B → ℝ) ≃L[ℝ] E, A x = e := by
    obtain ⟨e, he⟩ := hframe x hx
    refine ⟨e.equivFunL.symm, ?_⟩
    ext y
    simp only [A, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, ← he]
    change ∑ i, y i • e i = e.equivFunL.symm y
    have hrepr : ∀ i, e.repr (e.equivFunL.symm y) i = y i := by
      intro i
      change e.equivFunL (e.equivFunL.symm y) i = y i
      rw [ContinuousLinearEquiv.apply_symm_apply]
    simpa only [hrepr] using e.sum_repr (e.equivFunL.symm y)
  have hi : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ContinuousLinearMap.inverse (A x)) U := by
    intro x hx
    obtain ⟨e, he⟩ := hAe x hx
    have hInv : ContDiffAt ℝ (⊤ : ℕ∞) ContinuousLinearMap.inverse (A x) := by
      rw [he]
      exact contDiffAt_map_inverse e
    exact hInv.comp_contDiffWithinAt x (hA x hx)
  let a : B → P → ℝ := fun b x => ContinuousLinearMap.inverse (A (ψ x)) (fderiv ℝ ψ x v) b
  refine ⟨a, ?_, ?_⟩
  · intro b
    exact (contDiff_apply ℝ ℝ b).comp_contDiffOn
      ((hi.comp hψ hψU).clm_apply ((hψ.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const))
  · intro x hx
    obtain ⟨e, he⟩ := hAe (ψ x) (hψU hx)
    have hh : A (ψ x) (ContinuousLinearMap.inverse (A (ψ x)) (fderiv ℝ ψ x v)) = fderiv ℝ ψ x v := by
      exact (show (A (ψ x)).IsInvertible from ⟨e, he.symm⟩).self_apply_inverse _
    simpa only [A, a, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply] using hh.symm
 lemma word_smooth (U : Set E) (hU : IsOpen U)
    (fields : B → E → E) (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (r : List B) (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWord fields r u) U := by
  induction r with
  | nil => exact hu
  | cons b r ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply (hfields b)

private lemma term_derivative (U : Set E) (O : Set P) (hU : IsOpen U) (hO : IsOpen O)
    (fields : B → E → E) (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (ψ : P → E) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ O) (hψU : Set.MapsTo ψ O U)
    (v : P) (a : B → P → ℝ)
    (ha : ∀ x ∈ O, fderiv ℝ ψ x v = ∑ b, a b x • fields b (ψ x))
    (c : P → ℝ) (hc : ContDiffOn ℝ (⊤ : ℕ∞) c O) (r : List B)
    (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (x : P) (hx : x ∈ O) :
    fderiv ℝ (fun y => c y • directionalWord fields r u (ψ y)) x v =
      fderiv ℝ c x v • directionalWord fields r u (ψ x) +
        ∑ b, (c x * a b x) • directionalWord fields (b :: r) u (ψ x) := by
  have hdq := ((word_smooth U hU fields hfields r u hu).contDiffAt (hU.mem_nhds (hψU hx))).differentiableAt (by simp)
  have hdψ := (hψ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdc := (hc.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hh := hdc.hasFDerivAt.smul (hdq.hasFDerivAt.comp x hdψ.hasFDerivAt)
  change (fderiv ℝ (c • (directionalWord fields r u ∘ ψ)) x) v = _
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [ha x hx, map_sum]
  simp only [map_smul, Finset.smul_sum, smul_smul, directionalWord, Function.comp_apply]
  exact add_comm _ _

private lemma list_derivative {α : Type*} (ts : List α) (f : α → P → ℂ) (x : P)
    (hf : ∀ t ∈ ts, DifferentiableAt ℝ (f t) x) :
    HasFDerivAt (fun y => (ts.map (fun t => f t y)).sum)
      (ts.map (fun t => fderiv ℝ (f t) x)).sum x := by
  induction ts with
  | nil => simpa using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x
  | cons t ts ih =>
    exact (hf t (by simp)).hasFDerivAt.fun_add (ih (fun r hr => hf r (by simp [hr])))
private lemma list_transport (U : Set E) (O : Set P) (hU : IsOpen U) (hO : IsOpen O)
    (fields : B → E → E) (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (ψ : P → E) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ O) (hψU : Set.MapsTo ψ O U) (w : List P) :
    ∃ ts : List ((P → ℝ) × List B),
      (∀ t ∈ ts, ContDiffOn ℝ (⊤ : ℕ∞) t.1 O ∧ t.2.length ≤ w.length) ∧
      ∀ u : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u U → ∀ x ∈ O,
        constantDirectionWord w (u ∘ ψ) x =
          (ts.map (fun t => t.1 x • directionalWord fields t.2 u (ψ x))).sum := by
  classical
  induction w with
  | nil =>
    refine ⟨[(fun _ => 1, [])], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst t
      exact ⟨contDiffOn_const, by simp⟩
    · intro u hu x hx
      simp [constantDirectionWord, directionalWord]
  | cons v w ih =>
    obtain ⟨ts,hts,heq⟩ := ih
    obtain ⟨a,has,ha⟩ := inverse_coefficients U O hU hO fields hfields hframe ψ hψ hψU v
    let expand : ((P → ℝ) × List B) → List ((P → ℝ) × List B) := fun t =>
      (fun x => fderiv ℝ t.1 x v, t.2) ::
        (Finset.univ.toList.map (fun b => (fun x => t.1 x * a b x, b :: t.2)))
    refine ⟨ts.flatMap expand, ?_, ?_⟩
    · intro t ht
      obtain ⟨q,hq,ht⟩ := List.mem_flatMap.mp ht
      have hq' := hts q hq
      simp only [expand, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨b,hb,rfl⟩
      · exact ⟨(hq'.1.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const,
          hq'.2.trans (Nat.le_succ _)⟩
      · exact ⟨hq'.1.mul (has b), Nat.succ_le_succ hq'.2⟩
    · intro u hu x hx
      have he : constantDirectionWord w (u ∘ ψ) =ᶠ[𝓝 x]
          (fun y => (ts.map (fun t => t.1 y • directionalWord fields t.2 u (ψ y))).sum) :=
        Filter.Eventually.mono (hO.mem_nhds hx) (fun y hy => heq u hu y hy)
      change fderiv ℝ (constantDirectionWord w (u ∘ ψ)) x v = _
      rw [he.fderiv_eq]
      have ht (t : (P → ℝ) × List B) (hm : t ∈ ts) :
          DifferentiableAt ℝ (fun y => t.1 y • directionalWord fields t.2 u (ψ y)) x :=
        (((hts t hm).1.smul ((word_smooth U hU fields hfields t.2 u hu).comp hψ hψU)).contDiffAt
          (hO.mem_nhds hx)).differentiableAt (by simp)
      rw [(list_derivative ts (fun t y => t.1 y • directionalWord fields t.2 u (ψ y)) x ht).fderiv]
      rw [show (ts.flatMap expand).map (fun t => t.1 x • directionalWord fields t.2 u (ψ x)) =
          (ts.map (fun t => (expand t).map (fun q => q.1 x • directionalWord fields q.2 u (ψ x)))).flatten by
        simp [List.flatMap, List.map_flatten, List.map_map, Function.comp_def]]
      rw [List.sum_flatten, List.map_map]
      rw [show ((ts.map (fun t => fderiv ℝ
          (fun y => t.1 y • directionalWord fields t.2 u (ψ y)) x)).sum) v =
          (ts.map (fun t => fderiv ℝ (fun y => t.1 y • directionalWord fields t.2 u (ψ y)) x v)).sum by
        simpa only [List.map_map, Function.comp_def, ContinuousLinearMap.apply_apply] using
          map_list_sum (ContinuousLinearMap.apply ℝ ℂ v)
            (ts.map (fun t => fderiv ℝ (fun y => t.1 y • directionalWord fields t.2 u (ψ y)) x))]
      congr 1
      apply List.map_congr_left
      intro t htmem
      rw [term_derivative U O hU hO fields hfields ψ hψ hψU v a ha t.1 (hts t htmem).1 t.2 u hu x hx]
      simp only [expand, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        Finset.sum_toList]
      congr 1
      exact (Finset.sum_map_toList _ _).symm

end TransportProof

theorem transport [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [Fintype B]
    (U : Set E) (O : Set P) (hU : IsOpen U) (hO : IsOpen O)
    (fields : B → E → E)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (ψ : P → E) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ O)
    (hψU : Set.MapsTo ψ O U) (w : List P) :
    ∃ N : ℕ, ∃ c : Fin N → P → ℝ, ∃ r : Fin N → List B,
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (c i) O) ∧
      (∀ i, (r i).length ≤ w.length) ∧
      ∀ u : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u U → ∀ x ∈ O,
        constantDirectionWord w (u ∘ ψ) x =
          ∑ i : Fin N, c i x • directionalWord fields (r i) u (ψ x) := by
  obtain ⟨ts, hts, heq⟩ := list_transport U O hU hO fields hfields hframe ψ hψ hψU w
  refine ⟨ts.length, (fun i => (ts.get i).1), (fun i => (ts.get i).2), ?_, ?_, ?_⟩
  · intro i
    exact (hts _ (List.get_mem _ _)).1
  · intro i
    exact (hts _ (List.get_mem _ _)).2
  · intro u hu x hx
    rw [heq u hu x hx]
    conv_lhs => rw [← List.ofFn_get ts, List.map_ofFn, List.sum_ofFn]
    rfl

end DedekindZetaZeroFree.RightFrame.PullbackWords

end
