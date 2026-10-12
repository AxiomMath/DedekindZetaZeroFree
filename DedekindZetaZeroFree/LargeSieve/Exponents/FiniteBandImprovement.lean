module

public import DedekindZetaZeroFree.LargeSieve.Exponents.LargeScaleCrossoverBounds
public import DedekindZetaZeroFree.LargeSieve.Exponents.LogarithmicCrossoverBounds

@[expose] public section

open scoped BigOperators

namespace DedekindZetaZeroFree.LargeSieve

theorem HasRecursiveEnvelope.improve_of_band {B : ℝ → ℝ → ℝ}
    (hNonneg : ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → 0 ≤ B M N)
    (hBand : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ (A : ℝ) (J : ℕ) (D : ℝ), 1 ≤ A ∧ 0 < D ∧
        ∀ M N V : ℝ, 1 ≤ M → 1 ≤ N → M ≤ V →
          B M N ≤ D * ∑ j ∈ Finset.range (J + 1),
            B ((2 : ℝ) ^ j * A * V * (2 * M * N) ^ δ) N)
    {α : ℝ} (hα : 1 ≤ α) (hα₂ : α ≤ 2)
    (hEnvelope : HasRecursiveEnvelope B α) :
    HasExponent B (2 - 1 / α) := by
  intro ε hε
  let δ : ℝ := min 1 (ε / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / 2 := min_le_right _ _
  let η : ℝ := ε / (2 * (3 + δ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hloss : δ + (3 + δ) * η ≤ ε := by
    have he : (3 + δ) * η = ε / 2 := by
      dsimp [η]
      field_simp
      <;> ring
    rw [he]
    linarith
  obtain ⟨A, J, D, hA, hD, hband⟩ := hBand δ hδ hδ1
  obtain ⟨C, hC, henv⟩ := hEnvelope η hη
  let K : ℝ := (2 : ℝ) ^ J * A * (2 : ℝ) ^ δ
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨D * (J + 1) * (3 * C * K ^ η * K), by positivity, ?_⟩
  intro M N hM hN
  let β : ℝ := 2 - 1 / α
  let T : ℝ := M * N
  let V : ℝ := max M (N ^ β)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hM hN
  have hT0 : 0 < T := by dsimp [T]; positivity
  obtain ⟨hβ, hNb, hNNb, hprod⟩ := crossover_large_scale_bound α M N hα hα₂ hM hN
  change 1 ≤ N ^ β at hNb
  change N ≤ N ^ β at hNNb
  change N ^ β * N ≤ T ^ (3 : ℝ) at hprod
  have hMV : M ≤ V := le_max_left _ _
  have hNV : N ^ β ≤ V := le_max_right _ _
  have hV0 : 0 < V := hM0.trans_le hMV
  have hVN : V * N ≤ T ^ (3 : ℝ) := by
    dsimp [V]
    rw [max_mul_of_nonneg _ _ hN0.le]
    apply max_le
    · exact (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1 : ℝ) ≤ 3))
    · exact hprod
  have hVsum : V ≤ M + N ^ β := max_le (by linarith [Real.rpow_nonneg hN0.le β]) (by linarith)
  have hterm : ∀ j ∈ Finset.range (J + 1),
      B ((2 : ℝ) ^ j * A * V * (2 * M * N) ^ δ) N ≤
        (3 * C * K ^ η * K) * T ^ ε * (M + N ^ β) := by
    intro j hj
    have hjJ : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    let R : ℝ := (2 : ℝ) ^ j * A * V * (2 * M * N) ^ δ
    have h2j : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have h2jJ : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J := pow_le_pow_right₀ (by norm_num) hjJ
    have h2T : 1 ≤ 2 * M * N := by nlinarith
    have hpow : 1 ≤ (2 * M * N) ^ δ := Real.one_le_rpow h2T hδ.le
    have hVR : V ≤ R := by
      dsimp [R]
      nlinarith [mul_le_mul h2j hA (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (2 : ℝ) ^ j),
        mul_pos hV0 (by positivity : 0 < (2 * M * N) ^ δ)]
    have hR1 : 1 ≤ R := hM.trans (hMV.trans hVR)
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hNR : N ≤ R := hNNb.trans (hNV.trans hVR)
    have hmixed : N ^ (2 * α - 1) * R ^ (1 - α) ≤ R := by
      calc
        N ^ (2 * α - 1) * R ^ (1 - α) ≤
            N ^ (2 * α - 1) * (N ^ β) ^ (1 - α) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 _) (hNV.trans hVR) (by linarith))
            (Real.rpow_nonneg hN0.le _)
        _ = N ^ β := crossover_identity α M N hα hα₂ hM hN
        _ ≤ R := hNV.trans hVR
    have hRup : R ≤ K * V * T ^ δ := by
      dsimp [R, K, T]
      rw [show 2 * M * N = 2 * (M * N) by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (mul_pos hM0 hN0).le]
      calc
        (2 : ℝ) ^ j * A * V * (2 ^ δ * (M * N) ^ δ) ≤
          (2 : ℝ) ^ J * A * V * (2 ^ δ * (M * N) ^ δ) := by gcongr
        _ = _ := by ring
    have hRN : R * N ≤ K * T ^ (3 + δ) := by
      calc
        R * N ≤ (K * V * T ^ δ) * N := mul_le_mul_of_nonneg_right hRup hN0.le
        _ = K * (V * N) * T ^ δ := by ring
        _ ≤ K * T ^ (3 : ℝ) * T ^ δ := by gcongr
        _ = K * T ^ (3 + δ) := by rw [mul_assoc, ← Real.rpow_add hT0]
    have hRp : (R * N) ^ η ≤ K ^ η * T ^ ((3 + δ) * η) := by
      calc
        (R * N) ^ η ≤ (K * T ^ (3 + δ)) ^ η := Real.rpow_le_rpow (by positivity) hRN hη.le
        _ = _ := by rw [Real.mul_rpow hK.le (Real.rpow_nonneg hT0.le _), ← Real.rpow_mul hT0.le]
    have hRsum : R ≤ K * (M + N ^ β) * T ^ δ := by
      exact hRup.trans (by gcongr)
    calc
      B R N ≤ C * (R * N) ^ η * (R + N + N ^ (2 * α - 1) * R ^ (1 - α)) := henv R N hR1 hN
      _ ≤ C * (K ^ η * T ^ ((3 + δ) * η)) * (3 * (K * (M + N ^ β) * T ^ δ)) := by
        gcongr
        linarith
      _ = (3 * C * K ^ η * K) * T ^ (δ + (3 + δ) * η) * (M + N ^ β) := by
        rw [Real.rpow_add hT0]
        ring
      _ ≤ (3 * C * K ^ η * K) * T ^ ε * (M + N ^ β) := by
        gcongr
  calc
    B M N ≤ D * ∑ j ∈ Finset.range (J + 1), B ((2 : ℝ) ^ j * A * V * (2 * M * N) ^ δ) N := hband M N V hM hN hMV
    _ ≤ D * ∑ j ∈ Finset.range (J + 1), (3 * C * K ^ η * K) * T ^ ε * (M + N ^ β) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Finset.sum_le_sum hterm
    _ = D * (J + 1) * (3 * C * K ^ η * K) * T ^ ε * (M + N ^ β) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

end DedekindZetaZeroFree.LargeSieve
