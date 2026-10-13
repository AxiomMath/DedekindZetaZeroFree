module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorExponentBookkeeping

open DedekindZetaZeroFree.Quantitative.DetectorDef

theorem log_rpow_le (k δ : ℝ) (hk : 0 < k) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → Real.log U ^ k ≤ C * U ^ δ := by
  refine ⟨(k / δ) ^ k, by positivity, fun U hU => ?_⟩
  have hU0 : 0 ≤ U := by linarith
  have hL : 0 ≤ Real.log U := Real.log_nonneg hU
  have hkd : 0 < δ / k := by positivity
  have h1 : Real.log U ≤ U ^ (δ / k) / (δ / k) := Real.log_le_rpow_div hU0 hkd
  have e1 : δ / k * k = δ := div_mul_cancel₀ δ hk.ne'
  have e2 : k / δ = (δ / k)⁻¹ := (inv_div δ k).symm
  calc Real.log U ^ k ≤ (U ^ (δ / k) / (δ / k)) ^ k := Real.rpow_le_rpow hL h1 hk.le
    _ = (U ^ (δ / k)) ^ k / (δ / k) ^ k :=
        Real.div_rpow (Real.rpow_nonneg hU0 _) hkd.le k
    _ = U ^ δ / (δ / k) ^ k := by rw [← Real.rpow_mul hU0, e1]
    _ = (k / δ) ^ k * U ^ δ := by
        rw [e2, Real.inv_rpow hkd.le]
        ring

theorem boundB (U M e : ℝ) (hU : 1 ≤ U) (hM1 : U ^ (9 / 5 : ℝ) / 2 ≤ M)
    (hM2 : M ≤ 2 * U ^ (21 / 8 : ℝ)) (he : e = -(75999 / 100000)) :
    (M + U ^ 2) * M ^ e ≤ 4 * U ^ (63203 / 100000 : ℝ) := by
  have hU0 : 0 < U := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM1
  have he0 : e ≤ 0 := by rw [he]; norm_num

  have h1 : M ^ e ≤ (U ^ (9 / 5 : ℝ) / 2) ^ e :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hM1 he0
  have h2 : (U ^ (9 / 5 : ℝ) / 2) ^ e = U ^ (9 / 5 * e) * 2 ^ (-e) := by
    rw [Real.div_rpow (Real.rpow_nonneg hU0.le _) (by norm_num), ← Real.rpow_mul hU0.le,
      Real.rpow_neg (by norm_num), div_eq_mul_inv]
  have h3 : (2 : ℝ) ^ (-e) ≤ 2 := by
    calc (2 : ℝ) ^ (-e) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [he]; norm_num)
      _ = 2 := Real.rpow_one 2
  have hMe : M ^ e ≤ 2 * U ^ (9 / 5 * e) := by
    calc M ^ e ≤ U ^ (9 / 5 * e) * 2 ^ (-e) := h2 ▸ h1
      _ ≤ U ^ (9 / 5 * e) * 2 := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hU0.le _)
      _ = 2 * U ^ (9 / 5 * e) := by ring

  have t1 : M * M ^ e ≤ 2 * U ^ (63203 / 100000 : ℝ) := by
    have a1 : M * M ^ e = M ^ (1 + e) := by rw [Real.rpow_add hMpos, Real.rpow_one]
    have he1 : 0 ≤ 1 + e := by rw [he]; norm_num
    have a2 : M ^ (1 + e) ≤ (2 * U ^ (21 / 8 : ℝ)) ^ (1 + e) :=
      Real.rpow_le_rpow hMpos.le hM2 he1
    have a3 : (2 * U ^ (21 / 8 : ℝ)) ^ (1 + e) = 2 ^ (1 + e) * U ^ (21 / 8 * (1 + e)) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hU0.le _), ← Real.rpow_mul hU0.le]
    have a4 : (2 : ℝ) ^ (1 + e) ≤ 2 := by
      calc (2 : ℝ) ^ (1 + e) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [he]; norm_num)
        _ = 2 := Real.rpow_one 2
    have a5 : U ^ (21 / 8 * (1 + e)) ≤ U ^ (63203 / 100000 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hU (by rw [he]; norm_num)
    rw [a1]
    calc M ^ (1 + e) ≤ 2 ^ (1 + e) * U ^ (21 / 8 * (1 + e)) := a3 ▸ a2
      _ ≤ 2 * U ^ (63203 / 100000 : ℝ) :=
        mul_le_mul a4 a5 (Real.rpow_nonneg hU0.le _) (by norm_num)

  have t2 : U ^ 2 * M ^ e ≤ 2 * U ^ (63203 / 100000 : ℝ) := by
    have b1 : U ^ 2 = U ^ (2 : ℝ) := (Real.rpow_two U).symm
    have b2 : U ^ (2 : ℝ) * U ^ (9 / 5 * e) = U ^ (2 + 9 / 5 * e) :=
      (Real.rpow_add hU0 _ _).symm
    have b3 : U ^ (2 + 9 / 5 * e) ≤ U ^ (63203 / 100000 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hU (by rw [he]; norm_num)
    calc U ^ 2 * M ^ e ≤ U ^ 2 * (2 * U ^ (9 / 5 * e)) :=
          mul_le_mul_of_nonneg_left hMe (by positivity)
      _ = 2 * (U ^ (2 : ℝ) * U ^ (9 / 5 * e)) := by rw [b1]; ring
      _ = 2 * U ^ (2 + 9 / 5 * e) := by rw [b2]
      _ ≤ 2 * U ^ (63203 / 100000 : ℝ) := by linarith
  calc (M + U ^ 2) * M ^ e = M * M ^ e + U ^ 2 * M ^ e := by ring
    _ ≤ 4 * U ^ (63203 / 100000 : ℝ) := by linarith

theorem boundC (U M : ℝ) (hU : 1 ≤ U) (hMpos : 0 < M) (hM2 : M ≤ 2 * U ^ (21 / 8 : ℝ)) :
    (M * U) ^ (1 / 100000 : ℝ) ≤ 2 * U ^ ((21 / 8 + 1) / 100000 : ℝ) := by
  have hU0 : 0 < U := by linarith
  have h1 : M * U ≤ 2 * U ^ (21 / 8 + 1 : ℝ) := by
    rw [Real.rpow_add_one hU0.ne']
    have := mul_le_mul_of_nonneg_right hM2 hU0.le
    linarith
  have h2 : (2 : ℝ) ^ (1 / 100000 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 100000 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h3 : (21 / 8 + 1 : ℝ) * (1 / 100000) = (21 / 8 + 1) / 100000 := by ring
  calc (M * U) ^ (1 / 100000 : ℝ) ≤ (2 * U ^ (21 / 8 + 1 : ℝ)) ^ (1 / 100000 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = 2 ^ (1 / 100000 : ℝ) * (U ^ (21 / 8 + 1 : ℝ)) ^ (1 / 100000 : ℝ) :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hU0.le _)
    _ = 2 ^ (1 / 100000 : ℝ) * U ^ ((21 / 8 + 1 : ℝ) * (1 / 100000)) := by
        rw [← Real.rpow_mul hU0.le]
    _ = 2 ^ (1 / 100000 : ℝ) * U ^ ((21 / 8 + 1) / 100000 : ℝ) := by rw [h3]
    _ ≤ 2 * U ^ ((21 / 8 + 1) / 100000 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hU0.le _)

theorem boundD (U M Clog : ℝ) (hClog : 0 ≤ Clog) (hU : 8 ≤ U) (hL2 : 2 ≤ Real.log U)
    (hM4 : 4 ≤ M) (hM2 : M ≤ 2 * U ^ (21 / 8 : ℝ)) :
    Real.log (2 * M) ^ Clog ≤ 6 ^ Clog * Real.log U ^ Clog := by
  have hU0 : 0 < U := by linarith
  have hlog0 : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
  have h1 : Real.log (2 * M) ≤ 6 * Real.log U := by
    have h2 : 2 * M ≤ 4 * U ^ (21 / 8 : ℝ) := by linarith
    have h3 : Real.log (2 * M) ≤ Real.log (4 * U ^ (21 / 8 : ℝ)) :=
      Real.log_le_log (by linarith) h2
    have h4 : Real.log (4 * U ^ (21 / 8 : ℝ)) = Real.log 4 + 21 / 8 * Real.log U := by
      rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hU0 _).ne', Real.log_rpow hU0]
    have h5 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  calc Real.log (2 * M) ^ Clog ≤ (6 * Real.log U) ^ Clog := Real.rpow_le_rpow hlog0 h1 hClog
    _ = 6 ^ Clog * Real.log U ^ Clog := Real.mul_rpow (by norm_num) (by linarith)

theorem detector_exponent_bookkeeping (c₁ Cs Ce Clog ρ : ℝ) (hc₁ : 0 < c₁) (hCs : 0 < Cs)
    (hCe : 0 < Ce) (hClog : 0 ≤ Clog) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 10000) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ U₂ : ℝ, 8 ≤ U₂ ∧ ∀ U : ℝ, U₂ ≤ U → ∀ M : ℝ,
      U ^ qExp / 2 ≤ M → M ≤ 2 * U ^ r' →
      (6 * Real.log U) * ((3 * Real.log U / c₁) ^ 2 *
        (Cs * (4 * U ^ ρ + 1) * (M + U ^ 2) * (M * U) ^ (1 / 100000 : ℝ) *
          Real.log (2 * M) ^ Clog * (Ce * M ^ (1 - 2 * σ₀ + 1 / 100000)))) ≤
        C₂ * U ^ DetectorDef.α := by
  have hr : r' = 21 / 8 := rfl
  have hq : qExp = 9 / 5 := rfl
  have hσ : σ₀ = 22 / 25 := rfl
  have hα : DetectorDef.α = 317 / 500 := rfl
  obtain ⟨CL, hCL, hLb⟩ := log_rpow_le (3 + Clog) (1 / 1000) (by linarith) (by norm_num)
  have hKc : 0 < 54 / c₁ ^ 2 * Cs * Ce := by positivity
  refine ⟨54 / c₁ ^ 2 * Cs * Ce * 40 * 6 ^ Clog * CL, by positivity, 8, le_rfl, ?_⟩
  intro U hU M hM1 hM2
  rw [hq] at hM1
  rw [hr] at hM2
  rw [hα]
  have hU1 : 1 ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have hL2 : 2 ≤ Real.log U := by
    have h1 : Real.log 8 ≤ Real.log U := Real.log_le_log (by norm_num) hU
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h3 := Real.log_two_gt_d9
    linarith
  have hLpos : 0 < Real.log U := by linarith
  have hUq : U ≤ U ^ (9 / 5 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hU1 (show (1 : ℝ) ≤ 9 / 5 by norm_num)
    rwa [Real.rpow_one] at this
  have hM4 : 4 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hA : 4 * U ^ ρ + 1 ≤ 5 * U ^ ρ := by
    have := Real.one_le_rpow hU1 hρ0.le
    linarith
  have hB := boundB U M (1 - 2 * σ₀ + 1 / 100000) hU1 hM1 hM2 (by rw [hσ]; norm_num)
  have hC := boundC U M hU1 hMpos hM2
  have hD := boundD U M Clog hClog hU hL2 hM4 hM2
  have hUρ : 0 ≤ U ^ ρ := Real.rpow_nonneg hU0.le _
  have hUβ : 0 ≤ U ^ (63203 / 100000 : ℝ) := Real.rpow_nonneg hU0.le _
  have hUγ : 0 ≤ U ^ ((21 / 8 + 1) / 100000 : ℝ) := Real.rpow_nonneg hU0.le _
  have hLC : 0 ≤ 6 ^ Clog * Real.log U ^ Clog :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLpos.le _)
  have hApos : 0 ≤ 4 * U ^ ρ + 1 := by linarith
  have hBnn : 0 ≤ (M + U ^ 2) * M ^ (1 - 2 * σ₀ + 1 / 100000) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hMpos.le _)
  have hCnn : 0 ≤ (M * U) ^ (1 / 100000 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hprod : (4 * U ^ ρ + 1) * ((M + U ^ 2) * M ^ (1 - 2 * σ₀ + 1 / 100000)) *
        (M * U) ^ (1 / 100000 : ℝ) * Real.log (2 * M) ^ Clog ≤
      (5 * U ^ ρ) * (4 * U ^ (63203 / 100000 : ℝ)) *
        (2 * U ^ ((21 / 8 + 1) / 100000 : ℝ)) * (6 ^ Clog * Real.log U ^ Clog) := by
    refine mul_le_mul (mul_le_mul (mul_le_mul hA hB hBnn (by positivity)) hC hCnn
      (by positivity)) hD (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _) (by positivity)
  have hLL : Real.log U ^ 3 * Real.log U ^ Clog = Real.log U ^ (3 + Clog) := by
    rw [Real.rpow_add hLpos, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hLb' := hLb U hU1
  have hP : U ^ ρ * U ^ (63203 / 100000 : ℝ) * U ^ ((21 / 8 + 1) / 100000 : ℝ) *
      U ^ (1 / 1000 : ℝ) ≤ U ^ (317 / 500 : ℝ) := by
    rw [← Real.rpow_add hU0, ← Real.rpow_add hU0, ← Real.rpow_add hU0]
    exact Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
  have hL3 : 0 ≤ Real.log U ^ 3 := by positivity
  calc (6 * Real.log U) * ((3 * Real.log U / c₁) ^ 2 *
        (Cs * (4 * U ^ ρ + 1) * (M + U ^ 2) * (M * U) ^ (1 / 100000 : ℝ) *
          Real.log (2 * M) ^ Clog * (Ce * M ^ (1 - 2 * σ₀ + 1 / 100000))))
      = (54 / c₁ ^ 2 * Cs * Ce) * (Real.log U ^ 3 *
        ((4 * U ^ ρ + 1) * ((M + U ^ 2) * M ^ (1 - 2 * σ₀ + 1 / 100000)) *
        (M * U) ^ (1 / 100000 : ℝ) * Real.log (2 * M) ^ Clog)) := by ring
    _ ≤ (54 / c₁ ^ 2 * Cs * Ce) * (Real.log U ^ 3 *
        ((5 * U ^ ρ) * (4 * U ^ (63203 / 100000 : ℝ)) *
        (2 * U ^ ((21 / 8 + 1) / 100000 : ℝ)) * (6 ^ Clog * Real.log U ^ Clog))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hL3) hKc.le
    _ = (54 / c₁ ^ 2 * Cs * Ce * 40 * 6 ^ Clog) * (Real.log U ^ (3 + Clog) *
        (U ^ ρ * U ^ (63203 / 100000 : ℝ) * U ^ ((21 / 8 + 1) / 100000 : ℝ))) := by
        rw [← hLL]; ring
    _ ≤ (54 / c₁ ^ 2 * Cs * Ce * 40 * 6 ^ Clog) * ((CL * U ^ (1 / 1000 : ℝ)) *
        (U ^ ρ * U ^ (63203 / 100000 : ℝ) * U ^ ((21 / 8 + 1) / 100000 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLb' (by positivity))
          (by positivity)
    _ = (54 / c₁ ^ 2 * Cs * Ce * 40 * 6 ^ Clog * CL) * (U ^ ρ * U ^ (63203 / 100000 : ℝ) *
        U ^ ((21 / 8 + 1) / 100000 : ℝ) * U ^ (1 / 1000 : ℝ)) := by ring
    _ ≤ (54 / c₁ ^ 2 * Cs * Ce * 40 * 6 ^ Clog * CL) * U ^ (317 / 500 : ℝ) :=
        mul_le_mul_of_nonneg_left hP (by positivity)

end DedekindZetaZeroFree.Quantitative.DetectorExponentBookkeeping
