module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

open scoped NumberField Classical

private theorem tail_shell_sum_le
    {ι : Type*} (w : ι → ℝ) (C : ℝ)
    (hcount : ∀ Y : ℝ, 1 ≤ Y → ∀ s : Finset ι,
      (∀ i ∈ s, w i ≤ Y) → (s.card : ℝ) ≤ C * Y)
    (p : ℝ) (hp : 1 < p) (A : ℝ) (hA : 1 ≤ A)
    (s : Finset ι) (hlo : ∀ i ∈ s, A < w i)
    (hup : ∀ i ∈ s, w i ≤ 2 * A) :
    ∑ i ∈ s, (w i) ^ (-p) ≤ 2 * C * A ^ (1 - p) := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hc := hcount (2 * A) (by linarith) s hup
  calc
    ∑ i ∈ s, (w i) ^ (-p) ≤ ∑ _i ∈ s, A ^ (-p) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_rpow_of_nonpos hA0 (hlo i hi).le (by linarith)
    _ = (s.card : ℝ) * A ^ (-p) := by simp
    _ ≤ (C * (2 * A)) * A ^ (-p) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hA0.le _)
    _ = 2 * C * A ^ (1 - p) := by
      rw [show 1 - p = 1 + (-p) by ring, Real.rpow_add hA0, Real.rpow_one]
      ring

private theorem tail_scale_rpow (X p : ℝ) (hX : 0 < X) (n : ℕ) :
    ((2 : ℝ) ^ n * X) ^ (1 - p) = X ^ (1 - p) * ((2 : ℝ) ^ (1 - p)) ^ n := by
  rw [Real.mul_rpow (by positivity) hX.le]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_comm (n : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  ring

private theorem tail_partial_sum_le
    {ι : Type*} (w : ι → ℝ) (C : ℝ)
    (hcount : ∀ Y : ℝ, 1 ≤ Y → ∀ s : Finset ι,
      (∀ i ∈ s, w i ≤ Y) → (s.card : ℝ) ≤ C * Y)
    (p : ℝ) (hp : 1 < p) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    ∀ s : Finset ι, (∀ i ∈ s, X < w i) → (∀ i ∈ s, w i ≤ (2 : ℝ) ^ n * X) →
      ∑ i ∈ s, (w i) ^ (-p) ≤
        (2 * C * X ^ (1 - p)) * ∑ k ∈ Finset.range n, ((2 : ℝ) ^ (1 - p)) ^ k := by
  classical
  induction n with
  | zero =>
      intro s hs hu
      have he : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro i hi
        have := hu i hi
        simp only [pow_zero, one_mul] at this
        exact (not_le_of_gt (hs i hi)) this)
      simp [he]
  | succ n ih =>
      intro s hs hu
      let t := s.filter (fun i => w i ≤ (2 : ℝ) ^ n * X)
      let u := s.filter (fun i => ¬w i ≤ (2 : ℝ) ^ n * X)
      have ht : ∑ i ∈ t, (w i) ^ (-p) ≤
          (2 * C * X ^ (1 - p)) * ∑ k ∈ Finset.range n, ((2 : ℝ) ^ (1 - p)) ^ k := by
        apply ih t
        · intro i hi
          exact hs i (Finset.mem_filter.mp hi).1
        · intro i hi
          exact (Finset.mem_filter.mp hi).2
      have hA : 1 ≤ (2 : ℝ) ^ n * X := by
        have hn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        nlinarith
      have hu' : ∑ i ∈ u, (w i) ^ (-p) ≤
          2 * C * ((2 : ℝ) ^ n * X) ^ (1 - p) := by
        apply tail_shell_sum_le w C hcount p hp _ hA u
        · intro i hi
          exact lt_of_not_ge (Finset.mem_filter.mp hi).2
        · intro i hi
          have := hu i (Finset.mem_filter.mp hi).1
          simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using this
      have hsplit : ∑ i ∈ s, (w i) ^ (-p) =
          (∑ i ∈ t, (w i) ^ (-p)) + ∑ i ∈ u, (w i) ^ (-p) :=
        (Finset.sum_filter_add_sum_filter_not s (fun i => w i ≤ (2 : ℝ) ^ n * X) _).symm
      rw [tail_scale_rpow X p (by linarith) n] at hu'
      rw [hsplit, Finset.sum_range_succ, mul_add]
      exact add_le_add ht (by simpa [mul_assoc] using hu')

theorem inversePower_tail_sum_le
    {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 1 ≤ w i)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ Y : ℝ, 1 ≤ Y → ∀ s : Finset ι,
      (∀ i ∈ s, w i ≤ Y) → (s.card : ℝ) ≤ C * Y)
    (p : ℝ) (hp : 1 < p) (X : ℝ) (hX : 1 ≤ X)
    (s : Finset ι) (hs : ∀ i ∈ s, X < w i) :
    ∑ i ∈ s, (w i) ^ (-p) ≤
      (2 * C / (1 - (2 : ℝ) ^ (1 - p))) * X ^ (1 - p) := by
  classical
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((∑ i ∈ s, w i) / X)
    (by norm_num : (1 : ℝ) < 2)
  have hu : ∀ i ∈ s, w i ≤ (2 : ℝ) ^ n * X := by
    intro i hi
    calc
      w i ≤ ∑ j ∈ s, w j :=
        Finset.single_le_sum (fun j _ => by linarith [hw j]) hi
      _ ≤ (2 : ℝ) ^ n * X := ((div_lt_iff₀ hX0).mp hn).le
  have hr0 : 0 ≤ (2 : ℝ) ^ (1 - p) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (1 - p) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : ∑ k ∈ Finset.range n, ((2 : ℝ) ^ (1 - p)) ^ k ≤
      1 / (1 - (2 : ℝ) ^ (1 - p)) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    rw [geom_sum_mul_neg]
    have := pow_nonneg hr0 n
    linarith
  calc
    ∑ i ∈ s, (w i) ^ (-p) ≤
        (2 * C * X ^ (1 - p)) * ∑ k ∈ Finset.range n, ((2 : ℝ) ^ (1 - p)) ^ k :=
      tail_partial_sum_le w C hcount p hp X hX n s hs hu
    _ ≤ (2 * C * X ^ (1 - p)) * (1 / (1 - (2 : ℝ) ^ (1 - p))) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (2 * C / (1 - (2 : ℝ) ^ (1 - p))) * X ^ (1 - p) := by
      ring

end DedekindZetaZeroFree.LargeSieve.Vendor
