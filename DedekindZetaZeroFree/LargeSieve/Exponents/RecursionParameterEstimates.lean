module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

private lemma rpow_exp_congr {a x y : ℝ} (h : x = y) : Real.rpow a x = Real.rpow a y := by
  rw [h]

private lemma rpow_mul' {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) :
    Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) :=
  (Real.rpow_mul hx y z).symm

private lemma mul_rpow' {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.rpow (x * y) z = Real.rpow x z * Real.rpow y z :=
  Real.mul_rpow hx hy

private lemma div_rpow' {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.rpow (x / y) z = Real.rpow x z / Real.rpow y z :=
  Real.div_rpow hx hy z

private lemma rpow_add' {x : ℝ} (hx : 0 < x) (y z : ℝ) :
    Real.rpow x y * Real.rpow x z = Real.rpow x (y + z) :=
  (Real.rpow_add hx y z).symm

private lemma rpow_le_rpow' {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    Real.rpow x z ≤ Real.rpow y z := Real.rpow_le_rpow hx hxy hz

private lemma rpow_le_rpow_exp' {x y z : ℝ} (hx : 1 ≤ x) (h : y ≤ z) :
    Real.rpow x y ≤ Real.rpow x z := Real.rpow_le_rpow_of_exponent_le hx h

private lemma one_le_rpow' {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) :
    1 ≤ Real.rpow x z := Real.one_le_rpow hx hz

private lemma rpow_pos' {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < Real.rpow x y :=
  Real.rpow_pos_of_pos hx y

private lemma rpow_nonneg' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ Real.rpow x y :=
  Real.rpow_nonneg hx y

private lemma rpow_neg' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    Real.rpow x (-y) = (Real.rpow x y)⁻¹ := Real.rpow_neg hx y

private lemma rpow_natCast' (x : ℝ) (n : ℕ) : Real.rpow x n = x ^ n :=
  Real.rpow_natCast x n

private lemma rpow_zero' (x : ℝ) : Real.rpow x 0 = 1 := Real.rpow_zero x

private lemma sqrt_eq_rpow' (x : ℝ) : Real.sqrt x = Real.rpow x (1 / 2) :=
  Real.sqrt_eq_rpow x

private lemma nat_le_of_one_le {r : ℕ} (hr : 1 ≤ r) : (0 : ℝ) < (r : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)

private lemma rpow_H5_le {M N η : ℝ} {r : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hη : 0 < η)
    (hr : 1 ≤ r) (hrη : 20 / η ≤ (r : ℝ)) :
    Real.rpow (Real.rpow N (1 / (r : ℝ))) 5 ≤ Real.rpow (M * N) (η / 4) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := nat_le_of_one_le hr
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hη4 : 0 ≤ η / 4 := by positivity
  have h20 : 20 ≤ (r : ℝ) * η := by
    rw [div_le_iff₀ hη] at hrη
    linarith
  have h5 : 5 / (r : ℝ) ≤ η / 4 := by
    rw [div_le_iff₀ hr0]
    nlinarith
  have hHN : Real.rpow (Real.rpow N (1 / (r : ℝ))) 5 = Real.rpow N (5 / (r : ℝ)) := by
    rw [rpow_mul' (le_of_lt hN0)]
    rw [rpow_exp_congr (show (1 / (r : ℝ)) * 5 = 5 / (r : ℝ) by ring)]
  rw [hHN]
  calc Real.rpow N (5 / (r : ℝ))
      ≤ Real.rpow N (η / 4) := rpow_le_rpow_exp' hN h5
    _ ≤ Real.rpow (M * N) (η / 4) := by
        rw [mul_rpow' (le_of_lt hM0) (le_of_lt hN0)]
        have h1 : (1 : ℝ) ≤ Real.rpow M (η / 4) := one_le_rpow' hM hη4
        have h2 : 0 ≤ Real.rpow N (η / 4) := rpow_nonneg' (le_of_lt hN0) _
        calc Real.rpow N (η / 4) = 1 * Real.rpow N (η / 4) := (one_mul _).symm
          _ ≤ Real.rpow M (η / 4) * Real.rpow N (η / 4) :=
              mul_le_mul_of_nonneg_right h1 h2

theorem recursion_parameter_basic (α M N η : ℝ) (r : ℕ)
    (hα : 1 ≤ α) (hM : 1 ≤ M) (hN : 1 ≤ N) (hη : 0 < η)
    (hr : 1 ≤ r) (hrη : 20 / η ≤ (r : ℝ)) :
    let T := M * N
    let δ := η / (8 * (r : ℝ) * (α + 1))
    let H := Real.rpow N (1 / (r : ℝ))
    0 < δ ∧
    1 ≤ H ∧
    Real.rpow (H) 5 ≤ Real.rpow (T) (η / 4) := by
  dsimp only []
  refine ⟨?_, ?_, ?_⟩
  · rw [div_pos_iff]
    left
    exact ⟨hη, by positivity⟩
  · exact one_le_rpow' hN (by positivity)
  · exact rpow_H5_le hM hN hη hr hrη

private lemma far_aux (α M N η T δ K R : ℝ) (r : ℕ)
    (hα : 1 ≤ α) (hM : 1 ≤ M) (hN : 1 ≤ N) (hη : 0 < η)
    (hr : 1 ≤ r) (hrη : 20 / η ≤ (r : ℝ))
    (hT : T = M * N) (hδ : δ = η / (8 * (r : ℝ) * (α + 1)))
    (hK : K = N ^ 2 / M * Real.rpow T δ)
    (hR : R = M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α))
    (hfar : 2 * N * Real.rpow T δ ≤ M) :
    0 < K ∧ K < M / 2 ∧
    (∀ n : ℝ, 1 ≤ n → n ≤ N →
      n ^ 2 / M * Real.rpow (M * n) δ ≤ K ∧
      K ≤ M * Real.rpow (M * n) (-δ) ∧
      M + n + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * n ≤
        2 * Real.rpow T (δ * (α + 1)) * R) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := nat_le_of_one_le hr
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hT0 : 0 < T := by rw [hT]; nlinarith
  have hT1 : 1 ≤ T := by rw [hT]; nlinarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδnn : 0 ≤ δ := le_of_lt hδ0
  have hTδ0 : 0 < Real.rpow T δ := rpow_pos' hT0 δ
  have hTδ1 : 1 ≤ Real.rpow T δ := one_le_rpow' hT1 hδnn
  have h2N : 2 * N ≤ M := by nlinarith [hfar, hTδ1]
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨hKpos, ?_, ?_⟩
  · have hKle : K ≤ N / 2 := by
      rw [hK, div_mul_eq_mul_div, div_le_div_iff₀ hM0 (by norm_num)]
      nlinarith [hfar, hN0]
    linarith
  · intro n hn1 hnN
    have hn0 : 0 ≤ n := by linarith
    have hn2 : n ^ 2 ≤ N ^ 2 := by nlinarith
    have hMnle : Real.rpow (M * n) δ ≤ Real.rpow T δ := by
      rw [hT]
      exact rpow_le_rpow' (by positivity) (by nlinarith) hδnn
    refine ⟨?_, ?_, ?_⟩
    · have h1 : n ^ 2 / M ≤ N ^ 2 / M := by
        rw [div_le_div_iff₀ hM0 hM0]
        nlinarith
      calc n ^ 2 / M * Real.rpow (M * n) δ ≤ N ^ 2 / M * Real.rpow T δ :=
            mul_le_mul h1 hMnle (rpow_nonneg' (by positivity) δ) (by positivity)
        _ = K := hK.symm
    · have hMnpos : 0 < Real.rpow (M * n) δ := rpow_pos' (by positivity) δ
      have hMnpow : Real.rpow (M * n) (-δ) = (Real.rpow (M * n) δ)⁻¹ :=
        rpow_neg' (by positivity) δ
      have hpow2 : (2 * N * Real.rpow T δ) ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (by positivity) hfar 2
      have hTsq : Real.rpow T (2 * δ) = (Real.rpow T δ) ^ 2 := by
        rw [show (2 : ℝ) * δ = δ * 2 by ring, ← rpow_mul' (le_of_lt hT0)]
        exact rpow_natCast' (Real.rpow T δ) 2
      have hkey : N ^ 2 * Real.rpow T (2 * δ) ≤ M ^ 2 := by
        rw [hTsq]
        nlinarith [hpow2]
      have hstep1 : N ^ 2 * Real.rpow T δ / M ≤ M / Real.rpow T δ := by
        rw [div_le_div_iff₀ hM0 hTδ0]
        have hadd : Real.rpow T δ * Real.rpow T δ = Real.rpow T (2 * δ) := by
          rw [rpow_add' hT0]
          rw [rpow_exp_congr (show δ + δ = 2 * δ by ring)]
        nlinarith [hkey, hadd]
      have hstep2 : M / Real.rpow T δ ≤ M * Real.rpow (M * n) (-δ) := by
        rw [hMnpow, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hTδ0 hMnpos).mpr hMnle) (by linarith)
      calc K = N ^ 2 / M * Real.rpow T δ := hK
        _ = N ^ 2 * Real.rpow T δ / M := by ring
        _ ≤ M * Real.rpow (M * n) (-δ) := le_trans hstep1 hstep2
    · have hαhalf : 0 ≤ δ * (α - 1 / 2) := by
        apply mul_nonneg hδnn; linarith
      have hTe : 1 ≤ Real.rpow T (δ * (α - 1 / 2)) := one_le_rpow' hT1 hαhalf
      have hTenn : 0 ≤ Real.rpow T (δ * (α - 1 / 2)) := le_trans zero_le_one hTe
      have ht1 : M + n ≤ Real.rpow T (δ * (α - 1 / 2)) * (M + N) := by
        calc M + n ≤ M + N := by linarith
          _ = 1 * (M + N) := by ring
          _ ≤ Real.rpow T (δ * (α - 1 / 2)) * (M + N) :=
              mul_le_mul_of_nonneg_right hTe (by linarith)
      have hKpow : Real.rpow K (α - 1 / 2) =
          Real.rpow N (2 * α - 1) * Real.rpow M (1 / 2 - α) *
            Real.rpow T (δ * (α - 1 / 2)) := by
        rw [hK]
        rw [mul_rpow' (by positivity) (rpow_nonneg' (le_of_lt hT0) δ)]
        rw [div_rpow' (by positivity) (le_of_lt hM0)]
        rw [rpow_mul' (le_of_lt hT0) δ (α - 1 / 2)]
        rw [div_eq_mul_inv]
        rw [← rpow_neg' (le_of_lt hM0) (α - 1 / 2)]
        rw [rpow_exp_congr (show -(α - 1 / 2) = 1 / 2 - α by ring)]
        rw [← rpow_natCast' N 2]
        rw [rpow_mul' (le_of_lt hN0) ((2 : ℕ) : ℝ) (α - 1 / 2)]
        rw [rpow_exp_congr (show ((2 : ℕ) : ℝ) * (α - 1 / 2) = 2 * α - 1 by ring)]
        try ring
      have ht2 : Real.sqrt M * Real.rpow K (α - 1 / 2) =
          Real.rpow T (δ * (α - 1 / 2)) *
            (Real.rpow N (2 * α - 1) * Real.rpow M (1 - α)) := by
        rw [sqrt_eq_rpow', hKpow]
        rw [show Real.rpow M (1 / 2) *
              (Real.rpow N (2 * α - 1) * Real.rpow M (1 / 2 - α) *
                Real.rpow T (δ * (α - 1 / 2))) =
            Real.rpow N (2 * α - 1) *
              (Real.rpow M (1 / 2) * Real.rpow M (1 / 2 - α)) *
              Real.rpow T (δ * (α - 1 / 2)) by ring]
        rw [rpow_add' hM0 (1 / 2) (1 / 2 - α)]
        rw [rpow_exp_congr (show (1 : ℝ) / 2 + (1 / 2 - α) = 1 - α by ring)]
        try ring
      have ht3 : Real.sqrt (M / K) * n ≤ Real.rpow T (δ * (α - 1 / 2)) * M := by
        have hMn : 0 ≤ Real.sqrt (M / K) * n := by positivity
        have hsq : (Real.sqrt (M / K) * n) ^ 2 ≤ M ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          rw [div_mul_eq_mul_div, div_le_iff₀ hKpos]
          rw [show M ^ 2 * K = M * N ^ 2 * Real.rpow T δ by
            rw [hK]
            rw [show M ^ 2 * (N ^ 2 / M * Real.rpow T δ) =
                M ^ 2 * (N ^ 2 / M) * Real.rpow T δ by ring]
            rw [show M ^ 2 * (N ^ 2 / M) = M * N ^ 2 by field_simp]
            try ring]
          have hMN2 : 0 ≤ M * N ^ 2 := by positivity
          have h1 : M * n ^ 2 ≤ M * N ^ 2 := mul_le_mul_of_nonneg_left hn2 (le_of_lt hM0)
          have h2 : M * N ^ 2 ≤ M * N ^ 2 * Real.rpow T δ :=
            le_mul_of_one_le_right hMN2 hTδ1
          linarith
        have hKM : Real.sqrt (M / K) * n ≤ M :=
          (pow_le_pow_iff_left₀ hMn (by linarith) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
        calc Real.sqrt (M / K) * n ≤ M := hKM
          _ = 1 * M := (one_mul M).symm
          _ ≤ Real.rpow T (δ * (α - 1 / 2)) * M :=
              mul_le_mul_of_nonneg_right hTe (by linarith)
      have hsum : M + n + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * n ≤
          Real.rpow T (δ * (α - 1 / 2)) *
            (2 * M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α)) := by
        have h4 : Real.rpow T (δ * (α - 1 / 2)) * (M + N) +
              Real.rpow T (δ * (α - 1 / 2)) *
                (Real.rpow N (2 * α - 1) * Real.rpow M (1 - α)) +
              Real.rpow T (δ * (α - 1 / 2)) * M =
            Real.rpow T (δ * (α - 1 / 2)) *
              (2 * M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α)) := by ring
        linarith [ht1, ht2.le, ht3, h4]
      have hX : 0 ≤ Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) :=
        mul_nonneg (rpow_nonneg' (le_of_lt hN0) _) (rpow_nonneg' (le_of_lt hM0) _)
      have h2R : 2 * M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) ≤ 2 * R := by
        rw [hR]
        linarith
      have hRnn : 0 ≤ R := by
        rw [hR]
        linarith
      calc M + n + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * n
          ≤ Real.rpow T (δ * (α - 1 / 2)) *
              (2 * M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α)) := hsum
        _ ≤ Real.rpow T (δ * (α - 1 / 2)) * (2 * R) :=
              mul_le_mul_of_nonneg_left h2R hTenn
        _ = 2 * Real.rpow T (δ * (α - 1 / 2)) * R := by ring
        _ ≤ 2 * Real.rpow T (δ * (α + 1)) * R := by
            have hle : Real.rpow T (δ * (α - 1 / 2)) ≤ Real.rpow T (δ * (α + 1)) :=
              rpow_le_rpow_exp' hT1 (by nlinarith [hδnn])
            calc 2 * Real.rpow T (δ * (α - 1 / 2)) * R
                ≤ 2 * Real.rpow T (δ * (α + 1)) * R := by
                  apply mul_le_mul_of_nonneg_right _ hRnn
                  exact mul_le_mul_of_nonneg_left hle (by norm_num)

theorem recursion_parameter_far (α M N η : ℝ) (r : ℕ)
    (hα : 1 ≤ α) (hM : 1 ≤ M) (hN : 1 ≤ N) (hη : 0 < η)
    (hr : 1 ≤ r) (hrη : 20 / η ≤ (r : ℝ))
    (hfar : 2 * N * Real.rpow (M * N) (η / (8 * (r : ℝ) * (α + 1))) ≤ M) :
    let T := M * N
    let δ := η / (8 * (r : ℝ) * (α + 1))
    let K := N ^ 2 / M * Real.rpow T δ
    let R := M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α)
    0 < K ∧ K < M / 2 ∧
    (∀ n : ℝ, 1 ≤ n → n ≤ N →
      n ^ 2 / M * Real.rpow (M * n) (δ) ≤
        K ∧
      K ≤
        M * Real.rpow (M * n) (-δ) ∧
      M + n + Real.sqrt M * Real.rpow (K) (α - 1 / 2) +
          Real.sqrt (M / K) * n ≤
        2 * Real.rpow (T)
          (δ * (α + 1)) * R) := by
  dsimp only []
  exact far_aux α M N η (M * N) (η / (8 * (r : ℝ) * (α + 1)))
    (N ^ 2 / M * Real.rpow (M * N) (η / (8 * (r : ℝ) * (α + 1))))
    (M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α))
    r hα hM hN hη hr hrη rfl rfl rfl rfl hfar

private lemma near_aux (α M N η δ : ℝ) (r : ℕ)
    (hα : 1 ≤ α) (hM : 1 ≤ M) (hN : 1 ≤ N) (hη : 0 < η)
    (hr : 1 ≤ r) (hrη : 20 / η ≤ (r : ℝ))
    (hδ : δ = η / (8 * (r : ℝ) * (α + 1)))
    (hnear : M ≤ 2 * N * Real.rpow (M * N) δ) :
    Real.rpow N α ≤ Real.rpow 2 (α - 1) * Real.rpow (M * N) (δ * (α - 1)) *
      Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) ∧
    Real.rpow (M * N) (η / 4 + δ * (α - 1)) ≤ Real.rpow (M * N) η := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hT1 : 1 ≤ M * N := by nlinarith
  have hT0 : 0 < M * N := by nlinarith
  have hα1 : 0 < α + 1 := by linarith
  have hδnn : 0 ≤ δ := by rw [hδ]; positivity
  have hN2 : 0 < Real.rpow N (2 * α - 1) := rpow_pos' hN0 _
  have hM1 : 0 < Real.rpow M (1 - α) := rpow_pos' hM0 _
  refine ⟨?_, ?_⟩
  · have hMN : M / N ≤ 2 * Real.rpow (M * N) δ := by
      rw [div_le_iff₀ hN0]
      nlinarith [hnear]
    have hcore : Real.rpow (M / N) (α - 1) ≤ Real.rpow (2 * Real.rpow (M * N) δ) (α - 1) :=
      rpow_le_rpow' (by positivity) hMN (by linarith)
    have h1 : Real.rpow (M / N) (α - 1) = Real.rpow N (1 - α) * Real.rpow M (α - 1) := by
      rw [div_rpow' (le_of_lt hM0) (le_of_lt hN0), div_eq_mul_inv,
        ← rpow_neg' (le_of_lt hN0) (α - 1)]
      rw [rpow_exp_congr (show -(α - 1) = 1 - α by ring)]
      ring
    have h2 : Real.rpow (2 * Real.rpow (M * N) δ) (α - 1) =
        Real.rpow 2 (α - 1) * Real.rpow (M * N) (δ * (α - 1)) := by
      rw [mul_rpow' (by norm_num) (rpow_nonneg' (le_of_lt hT0) δ),
        rpow_mul' (le_of_lt hT0) δ (α - 1)]
    have hcore' : Real.rpow N (1 - α) * Real.rpow M (α - 1) ≤
        Real.rpow 2 (α - 1) * Real.rpow (M * N) (δ * (α - 1)) := by
      rw [← h1, ← h2]
      exact hcore
    have hNa : Real.rpow N (1 - α) * Real.rpow N (2 * α - 1) = Real.rpow N α := by
      rw [rpow_add' hN0]
      rw [rpow_exp_congr (show (1 - α) + (2 * α - 1) = α by ring)]
    have hMa : Real.rpow M (α - 1) * Real.rpow M (1 - α) = 1 := by
      rw [rpow_add' hM0]
      rw [rpow_exp_congr (show (α - 1) + (1 - α) = 0 by ring)]
      rw [rpow_zero']
    have hl : Real.rpow N (1 - α) * Real.rpow M (α - 1) * Real.rpow N (2 * α - 1) *
        Real.rpow M (1 - α) = Real.rpow N α := by
      rw [show Real.rpow N (1 - α) * Real.rpow M (α - 1) * Real.rpow N (2 * α - 1) *
            Real.rpow M (1 - α) =
          Real.rpow N (1 - α) * Real.rpow N (2 * α - 1) *
            (Real.rpow M (α - 1) * Real.rpow M (1 - α)) by ring]
      rw [hNa, hMa]
      ring
    calc Real.rpow N α
        = Real.rpow N (1 - α) * Real.rpow M (α - 1) * Real.rpow N (2 * α - 1) *
            Real.rpow M (1 - α) := hl.symm
      _ ≤ Real.rpow 2 (α - 1) * Real.rpow (M * N) (δ * (α - 1)) *
            Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcore' (le_of_lt hN2)) (le_of_lt hM1)
          simpa only [mul_assoc] using this
  · have hδa : δ * (α - 1) ≤ η / 8 := by
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have hrr : α - 1 ≤ (r : ℝ) * (α + 1) := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (r : ℝ) - 1)
          (by linarith : (0 : ℝ) ≤ α), hr1]
      nlinarith [hrr, hη]
    exact rpow_le_rpow_exp' hT1 (by linarith)

theorem recursion_parameter_near (α M N η : ℝ) (r : ℕ)
    (hα : 1 ≤ α) (hM : 1 ≤ M) (hN : 1 ≤ N) (hη : 0 < η)
    (hr : 1 ≤ r) (hrη : 20 / η ≤ (r : ℝ))
    (hnear : M ≤ 2 * N * Real.rpow (M * N) (η / (8 * (r : ℝ) * (α + 1)))) :
    let T := M * N
    let δ := η / (8 * (r : ℝ) * (α + 1))
    Real.rpow N α ≤ Real.rpow 2 (α - 1) *
      Real.rpow (T) (δ * (α - 1)) *
        Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) ∧
    Real.rpow (T) (η / 4 + δ * (α - 1)) ≤
      Real.rpow (T) η := by
  dsimp only []
  exact near_aux α M N η (η / (8 * (r : ℝ) * (α + 1))) r
    hα hM hN hη hr hrη rfl hnear

end DedekindZetaZeroFree.LargeSieve
