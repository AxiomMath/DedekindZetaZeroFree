module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

open scoped NumberField Classical

private lemma div_rpow_neg (X q p : ℝ) (hX : 0 < X) (hq : 0 < q) :
    (X / q) ^ (-p) = X ^ (-p) * q ^ p := by
  rw [Real.div_rpow hX.le hq.le, Real.rpow_neg hq.le, div_inv_eq_mul]

private lemma dyadic_pointwise (x X p : ℝ) (hx1 : 1 ≤ x) (hxX : x ≤ X) (hX1 : 1 ≤ X)
    (hp0 : 0 ≤ p) (hp1 : p < 1) (N : ℕ) (hN : X < 2 ^ N) :
    x ^ (-p) ≤ 2 ^ p * X ^ (-p) *
      ∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ ((k : ℝ) * p) *
        (if x ≤ X / 2 ^ k then (1 : ℝ) else 0) := by
  have hXpos : 0 < X := by linarith
  have hxpos : 0 < x := by linarith
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hex : ∃ k : ℕ, X / 2 ^ k < x := by
    refine ⟨N, ?_⟩
    have : X / 2 ^ N < 1 := by rw [div_lt_one h2N]; exact hN
    linarith
  obtain ⟨K, hKspec, hKmin, hKle⟩ :
      ∃ K, X / 2 ^ K < x ∧ (∀ k < K, x ≤ X / 2 ^ k) ∧ K ≤ N :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => le_of_not_gt (Nat.find_min hex hk), by
      apply Nat.find_min' hex
      have : X / 2 ^ N < 1 := by rw [div_lt_one h2N]; exact hN
      linarith⟩
  have hKpos : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hKspec; simp at hKspec; linarith
    · exact h
  have hxY : x ≤ X / 2 ^ (K - 1) := hKmin (K - 1) (by omega)
  have hstep1 : x ^ (-p) ≤ (X / 2 ^ K) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hKspec.le (by linarith)
  have hterm : (X / 2 ^ K) ^ (-p) = 2 ^ p * X ^ (-p) * (2 : ℝ) ^ (((K - 1 : ℕ) : ℝ) * p) := by
    rw [div_rpow_neg X ((2:ℝ)^K) p hXpos (by positivity),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) K p]
    have hexp : (K : ℝ) * p = p + ((K - 1 : ℕ) : ℝ) * p := by
      have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by rw [Nat.cast_sub hKpos]; norm_num
      rw [hcast]; ring
    rw [hexp, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    ring
  have hmem : K - 1 ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range]; omega
  have hnonneg : ∀ k ∈ Finset.range (N + 1),
      0 ≤ (2 : ℝ) ^ ((k : ℝ) * p) * (if x ≤ X / 2 ^ k then (1 : ℝ) else 0) := by
    intro k hk
    have : 0 ≤ (2:ℝ) ^ ((k:ℝ) * p) := Real.rpow_nonneg (by norm_num) _
    split <;> positivity
  have hsum : (2 : ℝ) ^ (((K - 1 : ℕ) : ℝ) * p) ≤
      ∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ ((k : ℝ) * p) *
        (if x ≤ X / 2 ^ k then (1 : ℝ) else 0) := by
    have h := Finset.single_le_sum hnonneg hmem
    rw [if_pos hxY, mul_one] at h
    exact h
  calc x ^ (-p) ≤ (X / 2 ^ K) ^ (-p) := hstep1
    _ = 2 ^ p * X ^ (-p) * (2 : ℝ) ^ (((K - 1 : ℕ) : ℝ) * p) := hterm
    _ ≤ 2 ^ p * X ^ (-p) *
        ∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ ((k : ℝ) * p) *
          (if x ≤ X / 2 ^ k then (1 : ℝ) else 0) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity

private lemma dyadic_term (X p : ℝ) (k : ℕ) :
    (2:ℝ)^((k:ℝ)*p) * (X / 2^k) = X * ((2:ℝ)^(p-1))^k := by
  have h1 : (2:ℝ)^k = (2:ℝ)^(k:ℝ) := by rw [Real.rpow_natCast]
  rw [h1]
  rw [show (2:ℝ)^((k:ℝ)*p) * (X / (2:ℝ)^(k:ℝ))
        = X * ((2:ℝ)^((k:ℝ)*p) / (2:ℝ)^(k:ℝ)) by ring]
  rw [← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  rw [show (k:ℝ)*p - (k:ℝ) = (p-1)*(k:ℝ) by ring]
  rw [Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]

theorem inversePower_initial_sum_le
    {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 1 ≤ w i)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ Y : ℝ, 1 ≤ Y → ∀ s : Finset ι,
      (∀ i ∈ s, w i ≤ Y) → (s.card : ℝ) ≤ C * Y)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (X : ℝ) (hX : 1 ≤ X) (s : Finset ι) (hs : ∀ i ∈ s, w i ≤ X) :
    ∑ i ∈ s, (w i) ^ (-p) ≤
      ((2 : ℝ) ^ p * C / (1 - (2 : ℝ) ^ (p - 1))) * X ^ (1 - p) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, X < 2 ^ N := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, X < n := exists_nat_gt X
    have h2n : (n:ℝ) < (2:ℝ)^n := by
      exact_mod_cast (Nat.lt_two_pow_self : n < 2 ^ n)
    exact ⟨n, lt_trans hn h2n⟩
  have hXpos : 0 < X := by linarith
  have hr1 : (2:ℝ)^(p-1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2) (by linarith : p - 1 < 0)
  have hrpos : 0 < 1 - (2:ℝ)^(p-1) := by linarith
  have hpt : ∀ i ∈ s, (w i) ^ (-p) ≤ 2 ^ p * X ^ (-p) *
      ∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ ((k : ℝ) * p) *
        (if w i ≤ X / 2 ^ k then (1 : ℝ) else 0) :=
    fun i hi => dyadic_pointwise (w i) X p (hw i) (hs i hi) hX hp0 hp1 N hN
  have hcard : ∀ k ∈ Finset.range (N+1),
      ((s.filter (fun i => w i ≤ X / 2 ^ k)).card : ℝ) ≤ C * (X / 2 ^ k) := by
    intro k hk
    by_cases hY : 1 ≤ X / 2 ^ k
    · exact hcount (X / 2 ^ k) hY (s.filter _) (fun i hi => (Finset.mem_filter.mp hi).2)
    · have hempty : s.filter (fun i => w i ≤ X / 2 ^ k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i hi
        have h2 : 1 ≤ w i := hw i
        have hYlt : X / 2 ^ k < 1 := not_le.mp hY
        linarith
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      have h0 : 0 ≤ X / 2 ^ k := by positivity
      nlinarith [hC]
  have hgeom : ∑ k ∈ Finset.range (N+1), ((2:ℝ)^(p-1))^k ≤ (1 - (2:ℝ)^(p-1))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hrpos, mul_comm, mul_neg_geom_sum]
    have : 0 ≤ ((2:ℝ)^(p-1))^(N+1) := by positivity
    linarith
  have hX1p : X^(1-p) = X^(-p) * X := by
    rw [show (1:ℝ) - p = -p + 1 by ring, Real.rpow_add hXpos, Real.rpow_one]
  have hsum_eq : ∑ k ∈ Finset.range (N+1), (2:ℝ)^((k:ℝ)*p) * (C * (X/2^k))
      = C * X * ∑ k ∈ Finset.range (N+1), ((2:ℝ)^(p-1))^k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (2:ℝ)^((k:ℝ)*p) * (C * (X/2^k))
          = C * ((2:ℝ)^((k:ℝ)*p) * (X/2^k)) by ring, dyadic_term X p k]
    ring
  have hfinal : 2^p * X^(-p) * (C*X) * (1 - (2:ℝ)^(p-1))⁻¹
      = ((2:ℝ)^p * C / (1 - (2:ℝ)^(p-1))) * X^(1-p) := by
    rw [show 2^p * X^(-p) * (C*X) * (1 - (2:ℝ)^(p-1))⁻¹
          = 2^p * C * (X^(-p) * X) * (1 - (2:ℝ)^(p-1))⁻¹ by ring,
        ← hX1p, inv_eq_one_div]
    ring
  calc
    ∑ i ∈ s, (w i) ^ (-p)
      ≤ ∑ i ∈ s, 2 ^ p * X ^ (-p) * (∑ k ∈ Finset.range (N+1), (2:ℝ)^((k:ℝ)*p) * (if w i ≤ X/2^k then (1:ℝ) else 0)) := Finset.sum_le_sum hpt
    _ = 2 ^ p * X ^ (-p) * ∑ i ∈ s, ∑ k ∈ Finset.range (N+1), (2:ℝ)^((k:ℝ)*p) * (if w i ≤ X/2^k then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ = 2 ^ p * X ^ (-p) * ∑ k ∈ Finset.range (N+1), ∑ i ∈ s, (2:ℝ)^((k:ℝ)*p) * (if w i ≤ X/2^k then (1:ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = 2 ^ p * X ^ (-p) * ∑ k ∈ Finset.range (N+1), (2:ℝ)^((k:ℝ)*p) * ∑ i ∈ s, (if w i ≤ X/2^k then (1:ℝ) else 0) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
    _ = 2 ^ p * X ^ (-p) * ∑ k ∈ Finset.range (N+1), (2:ℝ)^((k:ℝ)*p) * ((s.filter (fun i => w i ≤ X/2^k)).card : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_boole]
    _ ≤ 2 ^ p * X ^ (-p) * ∑ k ∈ Finset.range (N+1), (2:ℝ)^((k:ℝ)*p) * (C * (X/2^k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left (hcard k hk)
        exact Real.rpow_nonneg (by norm_num) _
    _ = 2 ^ p * X ^ (-p) * (C * X) * ∑ k ∈ Finset.range (N+1), ((2:ℝ)^(p-1))^k := by
        rw [hsum_eq]; ring
    _ ≤ 2 ^ p * X ^ (-p) * (C*X) * (1 - (2:ℝ)^(p-1))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = ((2:ℝ)^p * C / (1 - (2:ℝ)^(p-1))) * X^(1-p) := hfinal

end DedekindZetaZeroFree.LargeSieve.Vendor
