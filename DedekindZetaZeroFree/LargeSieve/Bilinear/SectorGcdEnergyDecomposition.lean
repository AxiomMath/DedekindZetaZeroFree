module

public import Mathlib

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/GcdReduction.lean.
-/

namespace DedekindZetaZeroFree.LargeSieve.Vendor.GcdReduction

noncomputable section
open scoped Classical BigOperators

def gcdBlock {R L G D : Type*} [Fintype R] [Fintype L]
    (w : R → NNReal) (A : R → L → ℂ) (sector : L → G)
    (gcdLabel : L → L → D) (x : L → ℂ) (g : G) (d : D) : ℂ :=
  ∑ r, ∑ l, ∑ k, if sector l = g ∧ sector k = g ∧ gcdLabel l k = d then
    (w r : ℂ) * (A r l * x l) * star (A r k * x k) else 0

private lemma ofReal_normSq_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.ofReal_pow, Complex.star_def, ← Complex.mul_conj']

private lemma ofReal_mul_normSq_eq (w : NNReal) (z : ℂ) :
    (((w : ℝ) * ‖z‖ ^ 2 : ℝ) : ℂ) = (w : ℂ) * (z * star z) := by
  rw [Complex.ofReal_mul, ofReal_normSq_eq]

private lemma ofReal_sum_eq {R : Type*} [Fintype R] (X : R → ℝ) :
    ((∑ r, X r : ℝ) : ℂ) = ∑ r, (X r : ℂ) := by
  rw [Complex.ofReal_sum]

private lemma sum_mul_star_sum {L : Type*} [Fintype L] (f : L → ℂ) :
    (∑ l, f l) * star (∑ l, f l) = ∑ l, ∑ k, f l * star (f k) := by
  rw [star_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => Finset.mul_sum ..

private lemma ite_mul_star_ite (a b : ℂ) (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then a else 0) * star (if Q then b else 0) =
      if P ∧ Q then a * star b else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

private lemma sector_sum_eq {R L G : Type*} [Fintype L]
    (A : R → L → ℂ) (sector : L → G) (x : L → ℂ) (g : G) (r : R) :
    (∑ l, ∑ k,
        (if sector l = g then A r l * x l else 0) *
          star (if sector k = g then A r k * x k else 0)) =
      ∑ l, ∑ k,
        (if sector l = g ∧ sector k = g then
          (A r l * x l) * star (A r k * x k) else 0) := by
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  exact ite_mul_star_ite (A r l * x l) (A r k * x k) (sector l = g) (sector k = g)

private lemma sum_pool_ite {D : Type*} (pool : Finset D) (d0 : D)
    (hd : d0 ∈ pool) (P : Prop) [Decidable P] (Y : ℂ) :
    (∑ d ∈ pool, if P ∧ d0 = d then Y else 0) = if P then Y else 0 := by
  classical
  by_cases hP : P
  · rw [if_pos hP]
    refine (Finset.sum_eq_single_of_mem d0 hd ?_).trans ?_
    · intro d _ hne
      rw [if_neg (show ¬(P ∧ d0 = d) from fun hc => hne hc.2.symm)]
    · simp [hP]
  · rw [if_neg hP]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg (show ¬(P ∧ d0 = d) from fun hc => hP hc.1)]

private lemma sum_pool_sum_swap {L D : Type*} [Fintype L] (pool : Finset D)
    (F : L → L → D → ℂ) :
    (∑ d ∈ pool, ∑ l, ∑ k, F l k d) = ∑ l, ∑ k, ∑ d ∈ pool, F l k d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]

private lemma gcdBlock_eq {R L G D : Type*} [Fintype R] [Fintype L]
    (w : R → NNReal) (A : R → L → ℂ) (sector : L → G)
    (gcdLabel : L → L → D) (x : L → ℂ) (g : G) (d : D) :
    gcdBlock w A sector gcdLabel x g d =
      ∑ r, (w r : ℂ) * ∑ l, ∑ k,
        (if (sector l = g ∧ sector k = g) ∧ gcdLabel l k = d
          then (A r l * x l) * star (A r k * x k) else 0) := by
  simp only [gcdBlock]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (sector l = g ∧ sector k = g) ∧ gcdLabel l k = d
  · rw [if_pos h]
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [if_pos (show sector l = g ∧ sector k = g ∧ gcdLabel l k = d from ⟨h1, h2, h3⟩)]
    ring
  · rw [if_neg h, mul_zero]
    rw [if_neg (show ¬(sector l = g ∧ sector k = g ∧ gcdLabel l k = d) from
      fun hc => h ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩)]

private lemma sum_sector_eq_sum {L G : Type*} [Fintype L] [Fintype G]
    (f : L → ℂ) (sector : L → G) :
    (∑ g, ∑ l, if sector l = g then f l else 0) = ∑ l, f l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_ite_eq]
  simp

private lemma sum_mul_sum_swap {R G : Type*} [Fintype R] [Fintype G]
    (u : R → ℝ) (c : ℝ) (f : R → G → ℝ) :
    (∑ r, u r * (c * ∑ g, f r g)) = c * ∑ g, ∑ r, u r * f r g := by
  have h1 : (∑ r, u r * (c * ∑ g, f r g)) = ∑ r, ∑ g, u r * (c * f r g) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have h2 : (∑ r, ∑ g, u r * (c * f r g)) = ∑ g, ∑ r, u r * (c * f r g) :=
    Finset.sum_comm
  have h3 : (∑ g, ∑ r, u r * (c * f r g)) = ∑ g, ∑ r, c * (u r * f r g) := by
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  have h4 : (∑ g, ∑ r, c * (u r * f r g)) = c * ∑ g, ∑ r, u r * f r g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
  rw [h1, h2, h3, h4]

private lemma row_bound {R L G : Type*} [Fintype L] [Fintype G]
    (A : R → L → ℂ) (sector : L → G) (x : L → ℂ) (r : R) :
    ‖∑ l, A r l * x l‖ ^ 2 ≤
      (Fintype.card G : ℝ) *
        ∑ g, ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2 := by
  have hdecomp : (∑ l, A r l * x l) =
      ∑ g, ∑ l, if sector l = g then A r l * x l else 0 :=
    (sum_sector_eq_sum (fun l => A r l * x l) sector).symm
  rw [hdecomp]
  calc ‖∑ g, ∑ l, if sector l = g then A r l * x l else 0‖ ^ 2
      ≤ (∑ g, ‖∑ l, if sector l = g then A r l * x l else 0‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Fintype.card G : ℝ) *
          ∑ g, ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun g => ‖∑ l, if sector l = g then A r l * x l else 0‖)
        simpa using this

theorem sector_weighted_energy_bound
    {R L G : Type*} [Fintype R] [Fintype L] [Fintype G]
    (w : R → NNReal) (A : R → L → ℂ) (sector : L → G) (x : L → ℂ) :
    (∑ r, (w r : ℝ) * ‖∑ l, A r l * x l‖ ^ 2) ≤
      (Fintype.card G : ℝ) *
        ∑ g, ∑ r, (w r : ℝ) *
          ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2 := by
  calc ∑ r, (w r : ℝ) * ‖∑ l, A r l * x l‖ ^ 2
      ≤ ∑ r, (w r : ℝ) *
          ((Fintype.card G : ℝ) *
            ∑ g, ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2) :=
        Finset.sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_left (row_bound A sector x r) (by positivity)
    _ = (Fintype.card G : ℝ) *
          ∑ g, ∑ r, (w r : ℝ) *
            ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2 :=
        sum_mul_sum_swap (fun r => (w r : ℝ)) (Fintype.card G : ℝ)
          (fun r g => ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2)

theorem weighted_energy_eq_gcd_blocks
    {R L G D : Type*} [Fintype R] [Fintype L]
    (w : R → NNReal) (A : R → L → ℂ) (sector : L → G)
    (gcdLabel : L → L → D) (x : L → ℂ) (g : G)
    (pool : Finset D) (hpool : ∀ l k, gcdLabel l k ∈ pool) :
    ((∑ r, (w r : ℝ) * ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2 : ℝ) : ℂ) =
      ∑ d ∈ pool, gcdBlock w A sector gcdLabel x g d := by
  have hL : ((∑ r, (w r : ℝ) * ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2 : ℝ) : ℂ)
      = ∑ r, (w r : ℂ) * ∑ l, ∑ k,
          (if sector l = g ∧ sector k = g then
            (A r l * x l) * star (A r k * x k) else 0) := by
    rw [ofReal_sum_eq]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ofReal_mul_normSq_eq]
    congr 1
    rw [sum_mul_star_sum]
    exact sector_sum_eq A sector x g r
  have hR : (∑ d ∈ pool, gcdBlock w A sector gcdLabel x g d)
      = ∑ r, (w r : ℂ) * ∑ l, ∑ k,
          (if sector l = g ∧ sector k = g then
            (A r l * x l) * star (A r k * x k) else 0) := by
    simp only [gcdBlock_eq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [sum_pool_sum_swap]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    exact sum_pool_ite pool (gcdLabel l k) (hpool l k) (sector l = g ∧ sector k = g)
      ((A r l * x l) * star (A r k * x k))
  rw [hL, hR]

private lemma sum_weight_normSq_le {R L G D : Type*} [Fintype R] [Fintype L]
    (w : R → NNReal) (A : R → L → ℂ) (sector : L → G)
    (gcdLabel : L → L → D) (x : L → ℂ) (g : G)
    (pool : Finset D) (hpool : ∀ l k, gcdLabel l k ∈ pool) :
    (∑ r, (w r : ℝ) * ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2) ≤
      ∑ d ∈ pool, ‖gcdBlock w A sector gcdLabel x g d‖ := by
  have h := weighted_energy_eq_gcd_blocks w A sector gcdLabel x g pool hpool
  calc (∑ r, (w r : ℝ) * ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2)
      = (((∑ r, (w r : ℝ) * ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2 : ℝ) : ℂ)).re :=
        (Complex.ofReal_re _).symm
    _ = (∑ d ∈ pool, gcdBlock w A sector gcdLabel x g d).re := by rw [h]
    _ ≤ ‖∑ d ∈ pool, gcdBlock w A sector gcdLabel x g d‖ := Complex.re_le_norm _
    _ ≤ ∑ d ∈ pool, ‖gcdBlock w A sector gcdLabel x g d‖ := norm_sum_le _ _

theorem weighted_energy_le_sector_gcd_blocks
    {R L G D : Type*} [Fintype R] [Fintype L] [Fintype G]
    (w : R → NNReal)
    (A : R → L → ℂ) (sector : L → G)
    (gcdLabel : L → L → D) (x : L → ℂ)
    (pool : Finset D) (hpool : ∀ l k, gcdLabel l k ∈ pool) :
    (∑ r, (w r : ℝ) * ‖∑ l, A r l * x l‖ ^ 2) ≤
      (Fintype.card G : ℝ) *
        ∑ g, ∑ d ∈ pool, ‖gcdBlock w A sector gcdLabel x g d‖ := by
  calc (∑ r, (w r : ℝ) * ‖∑ l, A r l * x l‖ ^ 2)
      ≤ (Fintype.card G : ℝ) *
          ∑ g, ∑ r, (w r : ℝ) *
            ‖∑ l, if sector l = g then A r l * x l else 0‖ ^ 2 :=
        sector_weighted_energy_bound w A sector x
    _ ≤ (Fintype.card G : ℝ) *
          ∑ g, ∑ d ∈ pool, ‖gcdBlock w A sector gcdLabel x g d‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun g _ =>
          sum_weight_normSq_le w A sector gcdLabel x g pool hpool

end
end DedekindZetaZeroFree.LargeSieve.Vendor.GcdReduction
