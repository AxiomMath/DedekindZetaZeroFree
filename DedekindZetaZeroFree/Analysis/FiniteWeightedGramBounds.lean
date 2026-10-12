module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean.
Source: github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve.Vendor

open scoped NumberField Classical

private lemma mul_sum_sum_eq {ι : Type*} (a : ℂ) (f g : ι → ℂ) (s : Finset ι) :
    a * (∑ i ∈ s, f i) * (∑ i ∈ s, g i) = ∑ i ∈ s, ∑ j ∈ s, a * f i * g j := by
  have h1 : a * (∑ i ∈ s, f i) = ∑ i ∈ s, a * f i := Finset.mul_sum ..
  rw [h1, Finset.sum_mul_sum]

private lemma energy_gram_identity {α β : Type*} (R : Finset α) (S : Finset β)
    (w : α → ℝ) (k : β → α → ℂ) (lam : β → ℂ) :
    ((∑ a ∈ R, w a * ‖∑ b ∈ S, lam b * k b a‖ ^ 2 : ℝ) : ℂ) =
      ∑ b ∈ S, ∑ d ∈ S, (starRingEnd ℂ) (lam b) * lam d *
        (∑ a ∈ R, (w a : ℂ) * k d a * (starRingEnd ℂ) (k b a)) := by
  rw [Complex.ofReal_sum]
  trans ∑ a ∈ R, (w a : ℂ) * ((‖∑ b ∈ S, lam b * k b a‖ : ℂ)) ^ 2
  · exact Finset.sum_congr rfl (fun a _ => by rw [Complex.ofReal_mul, Complex.ofReal_pow])
  trans ∑ a ∈ R, ∑ b ∈ S, ∑ d ∈ S,
      (w a : ℂ) * ((starRingEnd ℂ) (lam b) * (starRingEnd ℂ) (k b a)) * (lam d * k d a)
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    have hconj : (starRingEnd ℂ) (∑ b ∈ S, lam b * k b a) =
        ∑ b ∈ S, (starRingEnd ℂ) (lam b) * (starRingEnd ℂ) (k b a) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun b _ => map_mul _ _ _)
    calc (w a : ℂ) * ((‖∑ b ∈ S, lam b * k b a‖ : ℂ)) ^ 2
        = (w a : ℂ) * (starRingEnd ℂ) (∑ b ∈ S, lam b * k b a) * (∑ b ∈ S, lam b * k b a) := by
          rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
          ring
      _ = (w a : ℂ) * (∑ b ∈ S, (starRingEnd ℂ) (lam b) * (starRingEnd ℂ) (k b a)) *
            (∑ d ∈ S, lam d * k d a) := by rw [hconj]
      _ = ∑ b ∈ S, ∑ d ∈ S,
            (w a : ℂ) * ((starRingEnd ℂ) (lam b) * (starRingEnd ℂ) (k b a)) * (lam d * k d a) :=
          mul_sum_sum_eq _ _ _ _
  · trans ∑ b ∈ S, ∑ d ∈ S, ∑ a ∈ R,
        (w a : ℂ) * ((starRingEnd ℂ) (lam b) * (starRingEnd ℂ) (k b a)) * (lam d * k d a)
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_comm]
    · refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun d _ => ?_))
      trans ∑ a ∈ R, ((starRingEnd ℂ) (lam b) * lam d) *
            ((w a : ℂ) * k d a * (starRingEnd ℂ) (k b a))
      · exact Finset.sum_congr rfl (fun a _ => by ring)
      · rw [← Finset.mul_sum]

private lemma gram_form_bound {β : Type*} (S : Finset β) (M : β → β → ℂ) (v : β → ℂ)
    (D H : ℝ) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hdiag : ∀ b ∈ S, ‖M b b‖ ≤ D)
    (hoff : ∀ b ∈ S, ∀ d ∈ S, b ≠ d → ‖M b d‖ ≤ H) :
    ‖∑ b ∈ S, ∑ d ∈ S, (starRingEnd ℂ) (v b) * v d * M d b‖ ≤
      (D + H * (S.card : ℝ)) * ∑ b ∈ S, ‖v b‖ ^ 2 := by
  have h1 : ‖∑ b ∈ S, ∑ d ∈ S, (starRingEnd ℂ) (v b) * v d * M d b‖
      ≤ ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * ‖M d b‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b hb => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d hd => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have h2 : ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * ‖M d b‖
      ≤ ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * (if d = b then D else H) := by
    refine Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun d hd => ?_))
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases h : d = b
    · rw [h, if_pos rfl]; exact hdiag b hb
    · rw [if_neg h]; exact hoff d hd b hb h
  have hErase : ∑ b ∈ S, ∑ d ∈ S.erase b, ‖v b‖ * ‖v d‖ ≤ (∑ b ∈ S, ‖v b‖) ^ 2 := by
    have hsub : ∀ b ∈ S, ∑ d ∈ S.erase b, ‖v b‖ * ‖v d‖ ≤ ∑ d ∈ S, ‖v b‖ * ‖v d‖ := by
      intro b hb
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
      intro d hd _
      positivity
    calc ∑ b ∈ S, ∑ d ∈ S.erase b, ‖v b‖ * ‖v d‖
        ≤ ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ := Finset.sum_le_sum hsub
      _ = (∑ b ∈ S, ‖v b‖) ^ 2 := by rw [sq, ← Finset.sum_mul_sum]
  have hCS : (∑ b ∈ S, ‖v b‖) ^ 2 ≤ (S.card : ℝ) * ∑ b ∈ S, ‖v b‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun b => ‖v b‖) (fun _ => (1:ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
    linarith [h]
  have hsplit : ∀ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * (if d = b then D else H)
      = ‖v b‖ * ‖v b‖ * D + ∑ d ∈ S.erase b, ‖v b‖ * ‖v d‖ * H := by
    intro b hb
    rw [← Finset.sum_erase_add S (fun d => ‖v b‖ * ‖v d‖ * (if d = b then D else H)) hb]
    have hs : ∑ x ∈ S.erase b, ‖v b‖ * ‖v x‖ * (if x = b then D else H)
        = ∑ x ∈ S.erase b, ‖v b‖ * ‖v x‖ * H :=
      Finset.sum_congr rfl (fun d hd => by
        have hdb : d ≠ b := (Finset.mem_erase.mp hd).1
        simp [hdb])
    rw [hs, if_pos rfl]
    ring
  have hsum : ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * (if d = b then D else H)
      = D * ∑ b ∈ S, ‖v b‖ ^ 2 + H * ∑ b ∈ S, ∑ d ∈ S.erase b, ‖v b‖ * ‖v d‖ := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_mul]
      have : ∑ b ∈ S, ‖v b‖ * ‖v b‖ = ∑ b ∈ S, ‖v b‖ ^ 2 :=
        Finset.sum_congr rfl (fun b _ => by ring)
      rw [this]; ring
    · have h : ∀ b ∈ S, ∑ d ∈ S.erase b, ‖v b‖ * ‖v d‖ * H
          = (∑ d ∈ S.erase b, ‖v b‖ * ‖v d‖) * H :=
        fun b _ => (Finset.sum_mul (S.erase b) (fun d => ‖v b‖ * ‖v d‖) H).symm
      rw [Finset.sum_congr rfl h, ← Finset.sum_mul, mul_comm]
  have h3 : ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * (if d = b then D else H)
      ≤ (D + H * (S.card : ℝ)) * ∑ b ∈ S, ‖v b‖ ^ 2 := by
    calc ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * (if d = b then D else H)
        = D * ∑ b ∈ S, ‖v b‖ ^ 2 + H * ∑ b ∈ S, ∑ d ∈ S.erase b, ‖v b‖ * ‖v d‖ := hsum
      _ ≤ D * ∑ b ∈ S, ‖v b‖ ^ 2 + H * (∑ b ∈ S, ‖v b‖) ^ 2 :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hErase hH)
      _ ≤ D * ∑ b ∈ S, ‖v b‖ ^ 2 + H * ((S.card : ℝ) * ∑ b ∈ S, ‖v b‖ ^ 2) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hCS hH)
      _ = (D + H * (S.card : ℝ)) * ∑ b ∈ S, ‖v b‖ ^ 2 := by ring
  calc ‖∑ b ∈ S, ∑ d ∈ S, (starRingEnd ℂ) (v b) * v d * M d b‖
      ≤ ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * ‖M d b‖ := h1
    _ ≤ ∑ b ∈ S, ∑ d ∈ S, ‖v b‖ * ‖v d‖ * (if d = b then D else H) := h2
    _ ≤ (D + H * (S.card : ℝ)) * ∑ b ∈ S, ‖v b‖ ^ 2 := h3

theorem finite_weighted_gram_bound {α β : Type*}
    (R : Finset α) (S : Finset β) (w : α → ℝ) (k : β → α → ℂ) (lam : β → ℂ)
    (D H : ℝ) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hw : ∀ a ∈ R, 0 ≤ w a)
    (hdiag : ∀ b ∈ S,
      ‖∑ a ∈ R, (w a : ℂ) * k b a * (starRingEnd ℂ) (k b a)‖ ≤ D)
    (hoff : ∀ b ∈ S, ∀ d ∈ S, b ≠ d →
      ‖∑ a ∈ R, (w a : ℂ) * k b a * (starRingEnd ℂ) (k d a)‖ ≤ H) :
    ∑ a ∈ R, w a * ‖∑ b ∈ S, lam b * k b a‖ ^ 2 ≤
      (D + H * (S.card : ℝ)) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  have hE : ∑ a ∈ R, w a * ‖∑ b ∈ S, lam b * k b a‖ ^ 2 =
      (∑ b ∈ S, ∑ d ∈ S, (starRingEnd ℂ) (lam b) * lam d *
        (∑ a ∈ R, (w a : ℂ) * k d a * (starRingEnd ℂ) (k b a))).re := by
    rw [← energy_gram_identity R S w k lam, Complex.ofReal_re]
  have hb := gram_form_bound S
    (fun b d => ∑ a ∈ R, (w a : ℂ) * k b a * (starRingEnd ℂ) (k d a)) lam D H hD hH hdiag hoff
  calc ∑ a ∈ R, w a * ‖∑ b ∈ S, lam b * k b a‖ ^ 2
      = (∑ b ∈ S, ∑ d ∈ S, (starRingEnd ℂ) (lam b) * lam d *
          (∑ a ∈ R, (w a : ℂ) * k d a * (starRingEnd ℂ) (k b a))).re := hE
    _ ≤ ‖∑ b ∈ S, ∑ d ∈ S, (starRingEnd ℂ) (lam b) * lam d *
          (∑ a ∈ R, (w a : ℂ) * k d a * (starRingEnd ℂ) (k b a))‖ := Complex.re_le_norm _
    _ ≤ (D + H * (S.card : ℝ)) * ∑ b ∈ S, ‖lam b‖ ^ 2 := hb

theorem finite_weighted_gram_bound_subset {α β : Type*}
    (R0 R : Finset α) (S : Finset β) (w : α → ℝ) (k : β → α → ℂ) (lam : β → ℂ)
    (D H : ℝ) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hw : ∀ a ∈ R, 0 ≤ w a) (hsub : R0 ⊆ R) (hw0 : ∀ a ∈ R0, 1 ≤ w a)
    (hdiag : ∀ b ∈ S,
      ‖∑ a ∈ R, (w a : ℂ) * k b a * (starRingEnd ℂ) (k b a)‖ ≤ D)
    (hoff : ∀ b ∈ S, ∀ d ∈ S, b ≠ d →
      ‖∑ a ∈ R, (w a : ℂ) * k b a * (starRingEnd ℂ) (k d a)‖ ≤ H) :
    ∑ a ∈ R0, ‖∑ b ∈ S, lam b * k b a‖ ^ 2 ≤
      (D + H * (S.card : ℝ)) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  refine le_trans ?_ (finite_weighted_gram_bound R S w k lam D H hD hH hw hdiag hoff)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun a ha _ => mul_nonneg (hw a ha) (sq_nonneg _)))
  exact Finset.sum_le_sum (fun a ha => le_mul_of_one_le_left (sq_nonneg _) (hw0 a ha))

end DedekindZetaZeroFree.LargeSieve.Vendor
