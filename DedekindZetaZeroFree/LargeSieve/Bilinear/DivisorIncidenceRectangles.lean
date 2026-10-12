module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteDisjointSupportInequality

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve.Vendor.DivisorBlocks

noncomputable section
open scoped NumberField Classical BigOperators

theorem divisor_block_bound
    {R L T P D E : Type*}
    [Fintype R] [Fintype L] [Fintype T] [Fintype P] [DecidableEq P]
    [Fintype D] [Fintype E]
    (s : L → Finset P) (t : T → Finset P)
    (IL : D → L → Prop) (IR : E → T → Prop)
    (A : D → R → L → ℂ) (B : E → R → T → ℂ)
    (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hA : ∀ d (z : L → ℂ),
      (∑ r, ‖∑ l, A d r l * z l‖ ^ 2) ≤ UA * ∑ l, ‖z l‖ ^ 2)
    (hB : ∀ e (v : T → ℂ),
      (∑ r, ‖∑ k, B e r k * v k‖ ^ 2) ≤ UB * ∑ k, ‖v k‖ ^ 2)
    (x : L → ℂ) (y : T → ℂ) :
    (∑ d, ∑ e, ∑ r, ‖∑ l, ∑ k, if Disjoint (s l) (t k) then
      (A d r l * (if IL d l then x l else 0)) *
        star (B e r k * (if IR e k then y k else 0)) else 0‖) ^ 2 ≤
      (Fintype.card D : ℝ) * (Fintype.card E : ℝ) * UA * UB *
        (∑ l, (2 : ℝ) ^ (s l).card *
          ((Finset.univ.filter (fun d => IL d l)).card : ℝ) * ‖x l‖ ^ 2) *
        (∑ k, (2 : ℝ) ^ (t k).card *
          ((Finset.univ.filter (fun e => IR e k)).card : ℝ) * ‖y k‖ ^ 2) := by
  classical
  set V : D → E → ℝ := fun d e => ∑ r, ‖∑ l, ∑ k, if Disjoint (s l) (t k) then
      (A d r l * (if IL d l then x l else 0)) *
        star (B e r k * (if IR e k then y k else 0)) else 0‖ with hV

  have hcell : ∀ d e, V d e ^ 2 ≤ UA * UB *
      (∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) *
      (∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0)) := by
    intro d e
    have h := DedekindZetaZeroFree.LargeSieve.Vendor.CoprimeBilinear.coprime_bilinear_operator_bound
      s t (A d) (B e) UA UB hUA hUB (hA d) (hB e)
      (fun l => if IL d l then x l else 0) (fun k => if IR e k then y k else 0)
    have h2 : (∑ l, (2 : ℝ) ^ (s l).card * ‖(if IL d l then x l else 0 : ℂ)‖ ^ 2) =
        ∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      split <;> simp
    have h3 : (∑ k, (2 : ℝ) ^ (t k).card * ‖(if IR e k then y k else 0 : ℂ)‖ ^ 2) =
        ∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      split <;> simp
    rw [h2, h3] at h
    simpa only [hV] using h

  have hcs : (∑ d, ∑ e, V d e) ^ 2 ≤
      ((Fintype.card D : ℝ) * (Fintype.card E : ℝ)) * (∑ d, ∑ e, V d e ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (D × E)))
      (f := fun p : D × E => V p.1 p.2)
    simp only [Finset.card_univ, Fintype.card_prod, Nat.cast_mul] at h
    rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type] at h
    exact h

  have hsumsq : (∑ d, ∑ e, V d e ^ 2) ≤ UA * UB *
      (∑ d, ∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) *
      (∑ e, ∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0)) := by
    have hstep : (∑ d, ∑ e, UA * UB *
            (∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) *
            (∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0))) =
        UA * UB *
            (∑ d, ∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) *
            (∑ e, ∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0)) := by
      rw [← Fintype.sum_mul_sum (fun d => UA * UB *
            (∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)))
            (fun e => ∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0))]
      rw [← Finset.mul_sum Finset.univ
        (fun d => ∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) (UA * UB)]
    calc (∑ d, ∑ e, V d e ^ 2)
        ≤ ∑ d, ∑ e, UA * UB *
            (∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) *
            (∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0)) :=
          Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun e _ => hcell d e
      _ = _ := hstep

  have hLd : (∑ d, ∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) =
      ∑ l, (2 : ℝ) ^ (s l).card *
        ((Finset.univ.filter (fun d => IL d l)).card : ℝ) * ‖x l‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hinner : (∑ d, (if IL d l then ‖x l‖ ^ 2 else 0)) =
        ((Finset.univ.filter (fun d => IL d l)).card : ℝ) * ‖x l‖ ^ 2 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum Finset.univ
      (fun d => if IL d l then ‖x l‖ ^ 2 else 0) ((2 : ℝ) ^ (s l).card), hinner]
    ring
  have hRe : (∑ e, ∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0)) =
      ∑ k, (2 : ℝ) ^ (t k).card *
        ((Finset.univ.filter (fun e => IR e k)).card : ℝ) * ‖y k‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hinner : (∑ e, (if IR e k then ‖y k‖ ^ 2 else 0)) =
        ((Finset.univ.filter (fun e => IR e k)).card : ℝ) * ‖y k‖ ^ 2 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum Finset.univ
      (fun e => if IR e k then ‖y k‖ ^ 2 else 0) ((2 : ℝ) ^ (t k).card), hinner]
    ring
  have hmain : (∑ d, ∑ e, V d e) ^ 2 ≤
      (Fintype.card D : ℝ) * (Fintype.card E : ℝ) * UA * UB *
        (∑ d, ∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) *
        (∑ e, ∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0)) := by
    calc (∑ d, ∑ e, V d e) ^ 2
        ≤ ((Fintype.card D : ℝ) * (Fintype.card E : ℝ)) * (∑ d, ∑ e, V d e ^ 2) := hcs
      _ ≤ ((Fintype.card D : ℝ) * (Fintype.card E : ℝ)) * (UA * UB *
            (∑ d, ∑ l, (2 : ℝ) ^ (s l).card * (if IL d l then ‖x l‖ ^ 2 else 0)) *
            (∑ e, ∑ k, (2 : ℝ) ^ (t k).card * (if IR e k then ‖y k‖ ^ 2 else 0))) :=
          mul_le_mul_of_nonneg_left hsumsq (by positivity)
      _ = _ := by ring
  simpa only [hV, hLd, hRe] using hmain

end
end DedekindZetaZeroFree.LargeSieve.Vendor.DivisorBlocks
