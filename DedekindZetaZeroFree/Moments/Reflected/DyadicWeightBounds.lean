module

public import DedekindZetaZeroFree.Moments.Reflected.PowerfulSquarefreeIdealDyads

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.ActualRowTransfer
noncomputable section

private lemma dyad_card_bound (X Y : ℝ) (hY : 1 ≤ Y) (hXY : X ≤ Y) :
    ((dyadIndices X).card : ℝ) ≤ (1 + Real.log Y / Real.log 2) ^ 2 := by
  classical
  have hlog : 0 ≤ Real.log Y / Real.log 2 :=
    div_nonneg (Real.log_nonneg hY) (Real.log_nonneg (by norm_num))
  have hs : dyadIndices X ⊆
      (Finset.range (⌊Real.log Y / Real.log 2⌋₊ + 1)).product
        (Finset.range (⌊Real.log Y / Real.log 2⌋₊ + 1)) := by
    intro pq hpq
    have hp := (Finset.mem_filter.mp hpq).2
    have hP : 1 ≤ (2 : ℝ) ^ pq.1 := one_le_pow₀ (by norm_num)
    have hQ : 1 ≤ (2 : ℝ) ^ pq.2 := one_le_pow₀ (by norm_num)
    have hi (n : ℕ) (hn : (2 : ℝ) ^ n ≤ Y) :
        n < ⌊Real.log Y / Real.log 2⌋₊ + 1 := by
      rw [Nat.lt_add_one_iff, Nat.le_floor_iff hlog]
      apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
      exact Real.le_log_of_pow_le (by norm_num) hn
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (hi pq.1 (by nlinarith)),
      Finset.mem_range.mpr (hi pq.2 (by nlinarith))⟩
  have hc := Finset.card_le_card hs
  have hn := Nat.floor_le hlog
  calc
    ((dyadIndices X).card : ℝ) ≤ ((⌊Real.log Y / Real.log 2⌋₊ + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast (show (dyadIndices X).card ≤ (⌊Real.log Y / Real.log 2⌋₊ + 1) ^ 2 by
        simpa [Finset.card_product, pow_two] using hc)
    _ ≤ (1 + Real.log Y / Real.log 2) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      linarith

private lemma dyad_weight_bound (M D Z : ℝ) (hM : 1 ≤ M) (hD : 0 ≤ D)
    (hZ : 1 ≤ Z) (pq : ℕ × ℕ) (hpq : pq ∈ dyadIndices (D * Z ^ M)) :
    Real.sqrt ((2 : ℝ) ^ pq.1) *
      ((2 : ℝ) ^ pq.2 + ((2 : ℝ) ^ pq.2) ^ 2 * (2 : ℝ) ^ pq.1 / Z) ≤
      (D + D ^ 2) * Z ^ (2 * M - 1) := by
  have hz : 0 < Z := by linarith
  have hP : 1 ≤ (2 : ℝ) ^ pq.1 := one_le_pow₀ (by norm_num)
  have hQ : 1 ≤ (2 : ℝ) ^ pq.2 := one_le_pow₀ (by norm_num)
  have hp := (Finset.mem_filter.mp hpq).2
  have hs : Real.sqrt ((2 : ℝ) ^ pq.1) ≤ (2 : ℝ) ^ pq.1 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) ^ pq.1 by positivity),
      Real.sqrt_nonneg ((2 : ℝ) ^ pq.1)]
  have he : Z ^ M ≤ Z ^ (2 * M - 1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hsq : ((2 : ℝ) ^ pq.1 * (2 : ℝ) ^ pq.2) ^ 2 ≤ (D * Z ^ M) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hp 2
  have hpow : (Z ^ M) ^ 2 / Z = Z ^ (2 * M - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    conv_lhs => rhs; rw [← Real.rpow_one Z]
    rw [← Real.rpow_sub hz]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (2 : ℝ) ^ pq.1 *
        ((2 : ℝ) ^ pq.2 + ((2 : ℝ) ^ pq.2) ^ 2 * (2 : ℝ) ^ pq.1 / Z) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = (2 : ℝ) ^ pq.1 * (2 : ℝ) ^ pq.2 +
        ((2 : ℝ) ^ pq.1 * (2 : ℝ) ^ pq.2) ^ 2 / Z := by ring
    _ ≤ D * Z ^ M + (D * Z ^ M) ^ 2 / Z :=
      add_le_add hp (div_le_div_of_nonneg_right hsq hz.le)
    _ = D * Z ^ M + D ^ 2 * Z ^ (2 * M - 1) := by
      rw [mul_pow, mul_div_assoc, hpow]
    _ ≤ (D + D ^ 2) * Z ^ (2 * M - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left he hD]

theorem sum_dyad_weights_bound
    (M Cstar : ℝ) (hM : 1 ≤ M) (hCstar : 0 < Cstar) :
    ∃ T : ℝ, 0 < T ∧ ∀ Z : ℝ, 1 ≤ Z →
      (∑ pq ∈ dyadIndices (Cstar * Z ^ M),
        Real.sqrt ((2 : ℝ) ^ pq.1) *
          ((2 : ℝ) ^ pq.2 + ((2 : ℝ) ^ pq.2) ^ 2 * (2 : ℝ) ^ pq.1 / Z)) ≤
      T * Z ^ (2 * M - 1) * (1 + Real.log Z) ^ 2 := by
  let D : ℝ := max Cstar 1
  let K : ℝ := 1 + Real.log D / Real.log 2 + M / Real.log 2
  have hD : 1 ≤ D := le_max_right _ _
  have hCD : Cstar ≤ D := le_max_left _ _
  have hDpos : 0 < D := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlD : 0 ≤ Real.log D / Real.log 2 := div_nonneg (Real.log_nonneg hD) hl2.le
  have hMK : 0 < M / Real.log 2 := div_pos (by linarith) hl2
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨(Cstar + Cstar ^ 2) * K ^ 2, by positivity, ?_⟩
  intro Z hZ
  have hz : 0 < Z := by linarith
  have hr : 1 ≤ Z ^ M := Real.one_le_rpow hZ (by linarith)
  have hY : 1 ≤ D * Z ^ M := by nlinarith
  have hXY : Cstar * Z ^ M ≤ D * Z ^ M := mul_le_mul_of_nonneg_right hCD (by positivity)
  have hlZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hlog : 1 + Real.log (D * Z ^ M) / Real.log 2 ≤ K * (1 + Real.log Z) := by
    rw [Real.log_mul hDpos.ne' (Real.rpow_pos_of_pos hz M).ne', Real.log_rpow hz]
    dsimp [K]
    have : 0 ≤ (1 + Real.log D / Real.log 2) * Real.log Z := by positivity
    rw [add_div, show M * Real.log Z / Real.log 2 = (M / Real.log 2) * Real.log Z by ring]
    nlinarith [this]
  have hc : ((dyadIndices (Cstar * Z ^ M)).card : ℝ) ≤ K ^ 2 * (1 + Real.log Z) ^ 2 := by
    calc
      _ ≤ (1 + Real.log (D * Z ^ M) / Real.log 2) ^ 2 := dyad_card_bound _ _ hY hXY
      _ ≤ (K * (1 + Real.log Z)) ^ 2 :=
        pow_le_pow_left₀ (by
          have := div_nonneg (Real.log_nonneg hY) hl2.le
          linarith) hlog 2
      _ = _ := mul_pow _ _ _
  calc
    _ ≤ ∑ pq ∈ dyadIndices (Cstar * Z ^ M),
        (Cstar + Cstar ^ 2) * Z ^ (2 * M - 1) := by
      apply Finset.sum_le_sum
      intro pq hpq
      exact dyad_weight_bound M Cstar Z hM hCstar.le hZ pq hpq
    _ = ((dyadIndices (Cstar * Z ^ M)).card : ℝ) *
        ((Cstar + Cstar ^ 2) * Z ^ (2 * M - 1)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K ^ 2 * (1 + Real.log Z) ^ 2) *
        ((Cstar + Cstar ^ 2) * Z ^ (2 * M - 1)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end
end DedekindZetaZeroFree.RepresentationTheory.ActualRowTransfer
