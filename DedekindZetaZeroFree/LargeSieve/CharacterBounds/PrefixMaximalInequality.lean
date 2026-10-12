module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped BigOperators

def detector_prefixSum {m : ℕ} (a b : Fin m → ℂ) (l : Fin (m + 1)) : ℂ :=
  ∑ k : Fin m, if k.val < l.val then a k * b k else 0

def detector_prefixMaxSq {m : ℕ} (a b : Fin m → ℂ) : ℝ :=
  (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
    (fun l => ‖detector_prefixSum a b l‖ ^ 2)

private lemma weighted_norm (t : ℝ) (ht : 0 < t) (u v : ℂ) :
    t * ‖u + v‖ ^ 2 ≤ t * (t + 1) * ‖u‖ ^ 2 + (t + 1) * ‖v‖ ^ 2 := by
  have hn := norm_add_le u v
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have huv := norm_nonneg (u + v)
  have hs := sq_nonneg (t * ‖u‖ - ‖v‖)
  nlinarith [sq_le_sq₀ huv (add_nonneg hu hv) |>.mpr hn]

private lemma max_nonneg {m : ℕ} (a b : Fin m → ℂ) : 0 ≤ detector_prefixMaxSq a b := by
  classical
  exact (sq_nonneg _).trans (Finset.le_sup' (s := Finset.univ) (f := fun l => ‖detector_prefixSum a b l‖ ^ 2) (Finset.mem_univ (0 : Fin (m + 1))))

private lemma prefix_le_max {m : ℕ} (a b : Fin m → ℂ) (l : Fin (m+1)) :
    ‖detector_prefixSum a b l‖ ^ 2 ≤ detector_prefixMaxSq a b := by
  classical
  exact Finset.le_sup' (f := fun l => ‖detector_prefixSum a b l‖ ^ 2) (Finset.mem_univ l)

private lemma split_max {m : ℕ} (a b : Fin m → ℂ) (p : ℕ) (t : ℝ) (ht : 0 < t) :
    let b₁ := fun k : Fin m => if k.val < p then b k else 0
    let b₂ := fun k : Fin m => if k.val < p then 0 else b k
    t * detector_prefixMaxSq a b ≤
      t * detector_prefixMaxSq a b₁ + (t + 1) * detector_prefixMaxSq a b₂ +
        t * (t+1) * ‖∑ k, a k * b₁ k‖ ^ 2 := by
  classical
  dsimp only
  rw [detector_prefixMaxSq]
  rw [Finset.mul₀_sup' (le_of_lt ht)]
  apply Finset.sup'_le
  intro l hl
  by_cases hp : l.val ≤ p
  · have he : detector_prefixSum a b l = detector_prefixSum a (fun k => if k.val < p then b k else 0) l := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk' : k.val < l.val
      · have hkp : k.val < p := lt_of_lt_of_le hk' hp
        simp [hk', hkp]
      · simp [hk']
    rw [he]
    have h1 := prefix_le_max a (fun k => if k.val < p then b k else 0) l
    have h2 := max_nonneg a (fun k => if k.val < p then 0 else b k)
    have h3 : 0 ≤ ‖∑ k, a k * (if k.val < p then b k else 0)‖ ^ 2 := sq_nonneg _
    have h12 := mul_le_mul_of_nonneg_left h1 ht.le
    have h22 := mul_nonneg (by linarith : 0 ≤ t+1) h2
    have h32 := mul_nonneg (mul_nonneg ht.le (by linarith : 0 ≤ t+1)) h3
    linarith
  · have he : detector_prefixSum a b l =
        (∑ k, a k * (if k.val < p then b k else 0)) +
          detector_prefixSum a (fun k => if k.val < p then 0 else b k) l := by
      rw [detector_prefixSum, detector_prefixSum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkp : k.val < p
      · have hkl : k.val < l.val := by omega
        simp [hkp, hkl]
      · by_cases hkl : k.val < l.val <;> simp [hkp, hkl]
    rw [he]
    have hw := weighted_norm t ht (∑ k, a k * (if k.val < p then b k else 0))
      (detector_prefixSum a (fun k => if k.val < p then 0 else b k) l)
    have h1 := max_nonneg a (fun k => if k.val < p then b k else 0)
    have h2 := prefix_le_max a (fun k => if k.val < p then 0 else b k) l
    nlinarith

private lemma base_max {m : ℕ} (a b : Fin m → ℂ) (r : ℕ)
    (hb : ∀ k : Fin m, b k ≠ 0 → r ≤ k.val ∧ k.val < r+1) :
    detector_prefixMaxSq a b ≤ ‖∑ k, a k * b k‖ ^ 2 := by
  classical
  apply Finset.sup'_le
  intro l hl
  by_cases hr : r < l.val
  · have he : detector_prefixSum a b l = ∑ k, a k * b k := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hbk : b k = 0
      · simp [hbk]
      · have := hb k hbk
        have hkl : k.val < l.val := by omega
        simp [hkl]
    rw [he]
  · have he : detector_prefixSum a b l = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hbk : b k = 0
      · simp [hbk]
      · have := hb k hbk
        have hkl : ¬k.val < l.val := by omega
        simp [hkl]
    rw [he]
    simp

private lemma recursive_max (m : ℕ) (J : Type) [Fintype J] (A : J → Fin m → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hop : ∀ b : Fin m → ℂ, (∑ j, ‖∑ k, A j k * b k‖ ^ 2) ≤ K * ∑ k, ‖b k‖ ^ 2)
    (n : ℕ) : ∀ (r : ℕ) (b : Fin m → ℂ),
    (∀ k : Fin m, b k ≠ 0 → r ≤ k.val ∧ k.val < r + 2^n) →
    (∑ j, detector_prefixMaxSq (A j) b) ≤ (n+1 : ℝ)^2 * K * ∑ k, ‖b k‖ ^ 2 := by
  classical
  induction n with
  | zero =>
    intro r b hb
    simpa using (Finset.sum_le_sum (fun j _ => base_max (A j) b r (by simpa using hb))).trans (hop b)
  | succ n ih =>
    intro r b hb
    let p := r + 2^n
    let b₁ := fun k : Fin m => if k.val < p then b k else 0
    let b₂ := fun k : Fin m => if k.val < p then 0 else b k
    have hb₁ : ∀ k : Fin m, b₁ k ≠ 0 → r ≤ k.val ∧ k.val < r + 2^n := by
      intro k hk
      dsimp [b₁] at hk
      split_ifs at hk with hkp
      · exact ⟨(hb k hk).1, hkp⟩
      · contradiction
    have hb₂ : ∀ k : Fin m, b₂ k ≠ 0 → p ≤ k.val ∧ k.val < p + 2^n := by
      intro k hk
      dsimp [b₂] at hk
      split_ifs at hk with hkp
      · contradiction
      · have := hb k hk
        rw [pow_succ] at this
        dsimp [p]
        omega
    have h1 := ih r b₁ hb₁
    have h2 := ih p b₂ hb₂
    have h3 := hop b₁
    have ht : 0 < (n+1 : ℝ) := by positivity
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => split_max (A j) b p (n+1) ht)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    change (n+1 : ℝ) * (∑ j, detector_prefixMaxSq (A j) b) ≤
      (n+1 : ℝ) * (∑ j, detector_prefixMaxSq (A j) b₁) +
      ((n+1 : ℝ)+1) * (∑ j, detector_prefixMaxSq (A j) b₂) +
      (n+1 : ℝ) * ((n+1 : ℝ)+1) * (∑ j, ‖∑ k, A j k * b₁ k‖^2) at hs
    have he : (∑ k, ‖b k‖^2) = (∑ k, ‖b₁ k‖^2) + (∑ k, ‖b₂ k‖^2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [b₁, b₂]
      split_ifs <;> simp
    have he1 : 0 ≤ K * ∑ k, ‖b₁ k‖^2 := mul_nonneg hK (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have he2 : 0 ≤ K * ∑ k, ‖b₂ k‖^2 := mul_nonneg hK (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have h1' := mul_le_mul_of_nonneg_left h1 ht.le
    have h2' := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ (n+1 : ℝ)+1)
    have h3' := mul_le_mul_of_nonneg_left h3 (mul_nonneg ht.le (by linarith : 0 ≤ (n+1 : ℝ)+1))
    rw [he]
    push_cast
    nlinarith [mul_nonneg (by positivity : 0 ≤ (n : ℝ)) he1,
      mul_nonneg (by positivity : 0 ≤ (n+1 : ℝ)) he2]

theorem detector_prefix_maximal :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (J : Type) [Fintype J] (A : J → Fin m → ℂ) (K : ℝ),
        0 ≤ K →
        (∀ b : Fin m → ℂ,
          (∑ j : J, ‖∑ k : Fin m, A j k * b k‖ ^ 2) ≤
            K * ∑ k : Fin m, ‖b k‖ ^ 2) →
        ∀ b : Fin m → ℂ,
          (∑ j : J, detector_prefixMaxSq (A j) b) ≤
            C * K * (1 + Real.log (m + 1)) ^ 2 * ∑ k : Fin m, ‖b k‖ ^ 2 := by
  refine ⟨16, by norm_num, ?_⟩
  intro m J inst A K hK hop b
  let n := Nat.log2 (m+1) + 1
  have hb : ∀ k : Fin m, b k ≠ 0 → 0 ≤ k.val ∧ k.val < 0 + 2^n := by
    intro k hk
    have := Nat.lt_log2_self (n := m+1)
    exact ⟨Nat.zero_le _, by dsimp [n]; omega⟩
  have hbound := recursive_max m J A K hK hop n 0 b hb
  have hlog : 0 ≤ Real.log (m+1) := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 m)
  have hl2 : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl := Real.log2_le_logb (m+1)
  rw [Real.logb] at hl
  have hm : ((m+1 : ℕ) : ℝ) = (m : ℝ)+1 := by norm_cast
  rw [hm] at hl
  have hl' : (Nat.log2 (m+1) : ℝ) * Real.log 2 ≤ Real.log (m+1) :=
    (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hl
  have hn : (n+1 : ℝ) ≤ 4 * (1 + Real.log (m+1)) := by
    dsimp [n]
    push_cast
    have hnl : 0 ≤ (Nat.log2 (m+1) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hn0 : 0 ≤ (n+1 : ℝ) := by positivity
  have hs : (n+1 : ℝ)^2 ≤ 16 * (1+Real.log (m+1))^2 := by nlinarith
  have he : 0 ≤ K * ∑ k, ‖b k‖^2 := mul_nonneg hK (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ (n+1 : ℝ)^2 * K * ∑ k, ‖b k‖^2 := hbound
    _ ≤ 16 * K * (1+Real.log (m+1))^2 * ∑ k, ‖b k‖^2 := by
      convert mul_le_mul_of_nonneg_right hs he using 1 <;> ring

theorem detector_normCutoff_eq_prefix (m : ℕ) (q : Fin m → ℝ)
    (hq : Monotone q) (x : ℝ) :
    ∃ l : Fin (m + 1),
      (Finset.univ.filter fun k : Fin m => q k ≤ x) =
        (Finset.univ.filter fun k : Fin m => k.val < l.val) := by
  classical
  let s := Finset.univ.filter fun k : Fin m => q k ≤ x
  refine ⟨⟨s.card, Nat.lt_succ_of_le (by simpa [s] using Finset.card_le_card (Finset.filter_subset (fun k : Fin m => q k ≤ x) Finset.univ))⟩, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change q k ≤ x ↔ k.val < s.card
  constructor
  · intro hk
    have hsub : (Finset.univ.filter fun i : Fin m => i.val ≤ k.val) ⊆ s := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hq (by simpa using (Finset.mem_filter.mp hi).2)).trans hk⟩
    have hc := Finset.card_le_card hsub
    have he : (Finset.univ.filter fun i : Fin m => i.val ≤ k.val).card = k.val + 1 := by
      rw [show (Finset.univ.filter fun i : Fin m => i.val ≤ k.val) = Finset.Iic k by ext i; simp]
      exact Fin.card_Iic k
    omega
  · intro hk
    by_contra h
    have hsub : s ⊆ (Finset.univ.filter fun i : Fin m => i.val < k.val) := by
      intro i hi
      change i ∈ Finset.univ.filter (fun k : Fin m => q k ≤ x) at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hlt
      exact h ((hq (by simpa using Nat.le_of_not_gt hlt)).trans hi)
    have hc := Finset.card_le_card hsub
    have he : (Finset.univ.filter fun i : Fin m => i.val < k.val).card = k.val := by
      rw [show (Finset.univ.filter fun i : Fin m => i.val < k.val) = Finset.Iio k by ext i; simp]
      exact Fin.card_Iio k
    omega

end
end DedekindZetaZeroFree
