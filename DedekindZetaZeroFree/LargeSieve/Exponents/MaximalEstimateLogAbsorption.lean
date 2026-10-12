module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree
namespace LogAbsorption

open Real

lemma one_add_log_le_mul_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → 1 + Real.log x ≤ C * x ^ δ := by
  refine ⟨1 + 1 / δ, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h1 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
  have h2 : (1 : ℝ) ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have h3 : 1 + x ^ δ / δ ≤ (1 + 1 / δ) * x ^ δ := by
    have : (1 + 1 / δ) * x ^ δ = x ^ δ + x ^ δ / δ := by ring
    rw [this]
    linarith
  linarith

lemma one_add_log_two_mul_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → 1 + Real.log (2 * N) ≤ C * N ^ δ := by
  obtain ⟨C, hC, h⟩ := one_add_log_le_mul_rpow hδ
  refine ⟨C * (2 : ℝ) ^ δ, ?_, fun N hN => ?_⟩
  · have h2 : 0 < (2 : ℝ) ^ δ := Real.rpow_pos_of_pos (by norm_num) δ
    positivity
  · have h2N : (1 : ℝ) ≤ 2 * N := by linarith
    have h1 := h (2 * N) h2N
    have h2 : (2 * N) ^ δ = (2 : ℝ) ^ δ * N ^ δ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_trans zero_le_one hN)]
    rw [h2] at h1
    calc 1 + Real.log (2 * N) ≤ C * (2 ^ δ * N ^ δ) := h1
      _ = C * (2 : ℝ) ^ δ * N ^ δ := by ring

lemma one_add_log_succ_le_poly (d : ℕ) (A : ℝ) (hA : 0 ≤ A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (N : ℝ), 2 ≤ N → (m : ℝ) ≤ A * N ^ d →
      1 + Real.log ((m : ℝ) + 1) ≤ C * N ^ δ := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := one_add_log_le_mul_rpow hδ
  let B : ℝ := 2 * (A + 1)
  have hB1 : (1 : ℝ) ≤ B := by dsimp [B]; linarith
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  refine ⟨C₁ * B ^ δ / (2 : ℝ) ^ δ + (d : ℝ) / δ, ?_, ?_⟩
  · have h1 : 0 < C₁ * B ^ δ / (2 : ℝ) ^ δ := by
      have hb := Real.rpow_pos_of_pos hBpos δ
      have h2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) δ
      positivity
    have h2 : 0 ≤ (d : ℝ) / δ := by positivity
    linarith
  · intro m N hN hm
    have hN1 : (1 : ℝ) ≤ N := by linarith
    have hNpos : 0 < N := by linarith
    have hNd : (1 : ℝ) ≤ N ^ d := one_le_pow₀ hN1
    have hm1 : (m : ℝ) + 1 ≤ B * N ^ d := by
      have h1 : (m : ℝ) + 1 ≤ A * N ^ d + 1 := by linarith
      have h2 : A * N ^ d + 1 ≤ A * N ^ d + N ^ d := by linarith
      have h3 : A * N ^ d + N ^ d = (A + 1) * N ^ d := by ring
      have hAB : A + 1 ≤ B := by dsimp [B]; linarith
      have h4 : (A + 1) * N ^ d ≤ B * N ^ d :=
        mul_le_mul_of_nonneg_right hAB (by positivity)
      linarith
    have hmpos : 0 < (m : ℝ) + 1 := by positivity
    have hlog : Real.log ((m : ℝ) + 1) ≤ Real.log (B * N ^ d) :=
      Real.log_le_log hmpos hm1
    have hsplit : Real.log (B * N ^ d) = Real.log B + (d : ℝ) * Real.log N := by
      rw [Real.log_mul (ne_of_gt hBpos) (by positivity : (N : ℝ) ^ d ≠ 0), Real.log_pow]
    have hlogN : Real.log N ≤ N ^ δ / δ := Real.log_le_rpow_div hNpos.le hδ
    have hBbound : 1 + Real.log B ≤ C₁ * B ^ δ := hC₁ B hB1
    have hmain : 1 + Real.log ((m : ℝ) + 1) ≤ C₁ * B ^ δ + (d : ℝ) / δ * N ^ δ := by
      rw [hsplit] at hlog
      have hdl : (d : ℝ) * Real.log N ≤ (d : ℝ) * (N ^ δ / δ) :=
        mul_le_mul_of_nonneg_left hlogN (by positivity)
      have hdδ : (d : ℝ) * (N ^ δ / δ) = (d : ℝ) / δ * N ^ δ := by ring
      linarith [hlog, hBbound, hdl, hdδ.le, hdδ.ge]
    have h2δ : 0 < (2 : ℝ) ^ δ := Real.rpow_pos_of_pos (by norm_num) δ
    have hNδ : (2 : ℝ) ^ δ ≤ N ^ δ := Real.rpow_le_rpow (by norm_num) hN hδ.le
    have hK : C₁ * B ^ δ ≤ (C₁ * B ^ δ / (2 : ℝ) ^ δ) * N ^ δ := by
      have hge : (1 : ℝ) ≤ N ^ δ / 2 ^ δ := by
        rw [← div_self (ne_of_gt h2δ)]
        exact div_le_div_of_nonneg_right hNδ h2δ.le
      have hKnn : 0 ≤ C₁ * B ^ δ := by positivity
      calc C₁ * B ^ δ = (C₁ * B ^ δ) * 1 := by ring
        _ ≤ (C₁ * B ^ δ) * (N ^ δ / 2 ^ δ) := mul_le_mul_of_nonneg_left hge hKnn
        _ = (C₁ * B ^ δ / (2 : ℝ) ^ δ) * N ^ δ := by ring
    calc 1 + Real.log ((m : ℝ) + 1) ≤ C₁ * B ^ δ + (d : ℝ) / δ * N ^ δ := hmain
      _ ≤ (C₁ * B ^ δ / (2 : ℝ) ^ δ) * N ^ δ + (d : ℝ) / δ * N ^ δ := by linarith
      _ = (C₁ * B ^ δ / (2 : ℝ) ^ δ + (d : ℝ) / δ) * N ^ δ := by ring

theorem log_absorption_polynomial_sq (d : ℕ) (A : ℝ) (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (N U : ℝ), 2 ≤ N → 2 ≤ U →
      (m : ℝ) ≤ A * N ^ d →
      (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N)) ^ 2 * (N * U) ^ (ε / 2)
        ≤ C * (N * U) ^ ε := by
  have hδ : 0 < ε / 16 := by linarith
  obtain ⟨C₁, hC₁pos, hC₁⟩ := one_add_log_succ_le_poly d A hA hδ
  obtain ⟨C₂, hC₂pos, hC₂⟩ := one_add_log_two_mul_le hδ
  refine ⟨(C₁ * C₂) ^ 2, by positivity, ?_⟩
  intro m N U hN hU hm
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hNU1 : (1 : ℝ) ≤ N * U := by nlinarith
  have hNUpos : 0 < N * U := by nlinarith
  have ha : 1 + Real.log ((m : ℝ) + 1) ≤ C₁ * N ^ (ε / 16) := hC₁ m N hN hm
  have hb : 1 + Real.log (2 * N) ≤ C₂ * N ^ (ε / 16) := hC₂ N hN1
  have ha0 : 0 ≤ 1 + Real.log ((m : ℝ) + 1) := by
    have hle : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have := Real.log_nonneg hle
    linarith
  have hb0 : 0 ≤ 1 + Real.log (2 * N) := by
    have hle : (1 : ℝ) ≤ 2 * N := by linarith
    have := Real.log_nonneg hle
    linarith
  have hsq1 : (1 + Real.log ((m : ℝ) + 1)) ^ 2 ≤ (C₁ * N ^ (ε / 16)) ^ 2 :=
    pow_le_pow_left₀ ha0 ha 2
  have hsq2 : (1 + Real.log (2 * N)) ^ 2 ≤ (C₂ * N ^ (ε / 16)) ^ 2 :=
    pow_le_pow_left₀ hb0 hb 2
  have hprod : (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N)) ^ 2
      ≤ (C₁ * N ^ (ε / 16)) ^ 2 * (C₂ * N ^ (ε / 16)) ^ 2 :=
    mul_le_mul hsq1 hsq2 (sq_nonneg _) (sq_nonneg _)
  have hkey : (C₁ * N ^ (ε / 16)) ^ 2 * (C₂ * N ^ (ε / 16)) ^ 2
      ≤ (C₁ * C₂) ^ 2 * (N * U) ^ (ε / 4) := by
    have hN4 : (N ^ (ε / 16)) ^ 4 = N ^ (ε / 4) := by
      rw [← Real.rpow_mul_natCast hNpos.le (ε / 16) 4]
      congr 1
      ring
    have hNU : N ^ (ε / 4) ≤ (N * U) ^ (ε / 4) :=
      Real.rpow_le_rpow hNpos.le (by nlinarith) (by linarith : (0 : ℝ) ≤ ε / 4)
    calc (C₁ * N ^ (ε / 16)) ^ 2 * (C₂ * N ^ (ε / 16)) ^ 2
        = (C₁ * C₂) ^ 2 * (N ^ (ε / 16)) ^ 4 := by ring
      _ = (C₁ * C₂) ^ 2 * N ^ (ε / 4) := by rw [hN4]
      _ ≤ (C₁ * C₂) ^ 2 * (N * U) ^ (ε / 4) :=
          mul_le_mul_of_nonneg_left hNU (by positivity)
  have hstep : (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N)) ^ 2
        * (N * U) ^ (ε / 2)
      ≤ (C₁ * C₂) ^ 2 * (N * U) ^ (ε / 4) * (N * U) ^ (ε / 2) :=
    mul_le_mul_of_nonneg_right (le_trans hprod hkey) (Real.rpow_nonneg hNUpos.le _)
  have hcomb : (C₁ * C₂) ^ 2 * (N * U) ^ (ε / 4) * (N * U) ^ (ε / 2)
      = (C₁ * C₂) ^ 2 * (N * U) ^ (3 * ε / 4) := by
    have hexp : ε / 4 + ε / 2 = 3 * ε / 4 := by ring
    rw [mul_assoc, ← Real.rpow_add hNUpos, hexp]
  have hfin : (C₁ * C₂) ^ 2 * (N * U) ^ (3 * ε / 4) ≤ (C₁ * C₂) ^ 2 * (N * U) ^ ε :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNU1 (by linarith)) (by positivity)
  linarith [hstep, hcomb.le, hcomb.ge, hfin]

theorem log_absorption_polynomial (d : ℕ) (A : ℝ) (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (N U : ℝ), 2 ≤ N → 2 ≤ U →
      (m : ℝ) ≤ A * N ^ d →
      (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N) ^ 2) * (N * U) ^ (ε / 2)
        ≤ C * (N * U) ^ ε := by
  obtain ⟨C, hC, h⟩ := log_absorption_polynomial_sq d A hA hε
  refine ⟨C, hC, fun m N U hN hU hm => ?_⟩
  have hNUpos : 0 < N * U := by nlinarith
  have hb : 1 + Real.log (2 * N) ^ 2 ≤ (1 + Real.log (2 * N)) ^ 2 := by
    have hlog : (0 : ℝ) ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
    nlinarith
  have hstep : (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N) ^ 2)
      ≤ (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N)) ^ 2 :=
    mul_le_mul_of_nonneg_left hb (sq_nonneg _)
  have hstep2 := mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hNUpos.le (ε / 2))
  linarith [hstep2, h m N U hN hU hm]

theorem log_absorption_linear (D : ℝ) (hD : 0 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (N U : ℝ), 2 ≤ N → 2 ≤ U → (m : ℝ) ≤ D * N →
      (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N) ^ 2) * (N * U) ^ (ε / 2)
        ≤ C * (N * U) ^ ε := by
  obtain ⟨C, hC, h⟩ := log_absorption_polynomial 1 D hD hε
  exact ⟨C, hC, fun m N U hN hU hm => h m N U hN hU (by simpa using hm)⟩

theorem log_absorption_linear_two (D : ℝ) (hD : 0 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (N U : ℝ), 2 ≤ N → 2 ≤ U → (m : ℝ) ≤ D * N →
      (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N) ^ 2) * (2 * N * U) ^ (ε / 2)
        ≤ C * (N * U) ^ ε := by
  obtain ⟨C, hC, h⟩ := log_absorption_linear D hD hε
  refine ⟨(2 : ℝ) ^ (ε / 2) * C, ?_, fun m N U hN hU hm => ?_⟩
  · have h2 : 0 < (2 : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  · have hNUpos : 0 < N * U := by nlinarith
    have h2 : 0 < (2 : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hsplit : (2 * N * U) ^ (ε / 2) = (2 : ℝ) ^ (ε / 2) * (N * U) ^ (ε / 2) := by
      rw [show (2 * N * U : ℝ) = 2 * (N * U) by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hNUpos.le]
    calc (1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N) ^ 2) * (2 * N * U) ^ (ε / 2)
        = (2 : ℝ) ^ (ε / 2)
            * ((1 + Real.log ((m : ℝ) + 1)) ^ 2 * (1 + Real.log (2 * N) ^ 2)
              * (N * U) ^ (ε / 2)) := by rw [hsplit]; ring
      _ ≤ (2 : ℝ) ^ (ε / 2) * (C * (N * U) ^ ε) :=
          mul_le_mul_of_nonneg_left (h m N U hN hU hm) h2.le
      _ = ((2 : ℝ) ^ (ε / 2) * C) * (N * U) ^ ε := by ring

end LogAbsorption
end DedekindZetaZeroFree
