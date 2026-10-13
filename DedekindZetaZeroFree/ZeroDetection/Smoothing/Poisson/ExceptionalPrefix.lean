module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Height
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.SmoothingTail

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorPrefix

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private theorem abel_nat (c : ℕ → ℂ) (w : ℕ → ℝ) (hw : ∀ i, w (i + 1) ≤ w i) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : w 0 ≤ 1) (m : ℕ) :
    ∃ j ≤ m, ‖∑ i ∈ Finset.range m, c i * (w i : ℂ)‖ ≤ ‖∑ i ∈ Finset.range j, c i‖ := by
  set P : ℕ → ℂ := fun j => ∑ i ∈ Finset.range j, c i with hP
  have key : ∀ k, ∑ i ∈ Finset.range k, c i * (w i : ℂ) =
      ∑ i ∈ Finset.range k, P (i + 1) * ((w i - w (i + 1) : ℝ) : ℂ) + P k * (w k : ℂ) := by
    intro k
    induction k with
    | zero => simp [P]
    | succ k ih =>
      have hPk : P (k + 1) = P k + c k := Finset.sum_range_succ _ _
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hPk]
      push_cast
      ring
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (m + 1)) (fun j => ‖P j‖)
    ⟨0, by simp⟩
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine ⟨j, hjm, ?_⟩
  set M := ‖P j‖ with hM
  have hbound : ∀ i ∈ Finset.range (m + 1), ‖P i‖ ≤ M := fun i hi => hmax i hi
  rw [key m]
  have h1 : ‖∑ i ∈ Finset.range m, P (i + 1) * ((w i - w (i + 1) : ℝ) : ℂ) + P m * (w m : ℂ)‖
      ≤ ∑ i ∈ Finset.range m, M * (w i - w (i + 1)) + M * w m := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      have hi' : i < m := Finset.mem_range.mp hi
      have hnn : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr (hw i)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right (hbound (i + 1) (Finset.mem_range.mpr (by omega))) hnn
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 m)]
      exact mul_le_mul_of_nonneg_right (hbound m (Finset.mem_range.mpr (by omega))) (hw0 m)
  have h2 : ∑ i ∈ Finset.range m, M * (w i - w (i + 1)) + M * w m = M * w 0 := by
    rw [← Finset.mul_sum, Finset.sum_range_sub']
    ring
  have hM0 : 0 ≤ M := norm_nonneg _
  have h3 : M * w 0 ≤ M := by nlinarith [hw0 0]
  linarith

def prefixSum (F : Type) [Field F] [NumberField F] (U : ℝ) {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (γ N y : ℝ) : ℂ :=
  ∑ᶠ n : Ideal (𝓞 F),
    if N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ y then
      ((DetectorDef.a F U n : ℝ) : ℂ) * ω n *
        (Ideal.absNorm n : ℂ) ^ (-((DetectorDef.σ₀ : ℂ) + (γ : ℂ) * Complex.I))
    else 0

private theorem abel_ideal {ι : Type*} (T : Finset ι) (nrm : ι → ℕ) (m : ℕ)
    (hpos : ∀ i ∈ T, 1 ≤ nrm i) (hle : ∀ i ∈ T, nrm i ≤ m) (c : ι → ℂ) (w : ℕ → ℝ)
    (hw : ∀ i, w (i + 1) ≤ w i) (hw0 : ∀ i, 0 ≤ w i) (hw1 : w 0 ≤ 1) :
    ∃ j : ℕ, ‖∑ i ∈ T, c i * (w (nrm i - 1) : ℂ)‖ ≤ ‖∑ i ∈ T, if nrm i ≤ j then c i else 0‖ := by
  obtain ⟨j, hj, hjb⟩ := abel_nat (fun k => ∑ i ∈ T, if nrm i = k + 1 then c i else 0) w hw hw0 hw1 m
  refine ⟨j, ?_⟩
  have e1 : ∑ k ∈ Finset.range m, (∑ i ∈ T, if nrm i = k + 1 then c i else 0) * (w k : ℂ) =
      ∑ i ∈ T, c i * (w (nrm i - 1) : ℂ) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hp := hpos i hi
    have hl := hle i hi
    rw [Finset.sum_eq_single (nrm i - 1)]
    · rw [if_pos (show nrm i = nrm i - 1 + 1 by omega)]
    · intro k _ hk
      rw [if_neg (show ¬ nrm i = k + 1 by omega), zero_mul]
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range]
      omega
  have e2 : ∑ k ∈ Finset.range j, (∑ i ∈ T, if nrm i = k + 1 then c i else 0) =
      ∑ i ∈ T, if nrm i ≤ j then c i else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hp := hpos i hi
    by_cases h : nrm i ≤ j
    · rw [if_pos h, Finset.sum_eq_single (nrm i - 1)]
      · rw [if_pos (show nrm i = nrm i - 1 + 1 by omega)]
      · intro k _ hk
        rw [if_neg (show ¬ nrm i = k + 1 by omega)]
      · intro hk
        exfalso
        apply hk
        rw [Finset.mem_range]
        omega
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      rw [if_neg (show ¬ nrm i = k + 1 by omega)]
  rw [← e1, ← e2]
  exact hjb

private theorem dyad (a0 R B : ℝ) (Qf : ℝ → ℝ → ℂ) (ha0 : 0 < a0) (hB0 : 0 ≤ B)
    (hadd : ∀ N y z, N ≤ y → y ≤ z → Qf N z = Qf N y + Qf y z)
    (hnil : ∀ N y, y ≤ N → Qf N y = 0)
    (hB : ∀ N y, a0 ≤ N → N ≤ R → N ≤ y → y ≤ 2 * N → y ≤ R → ‖Qf N y‖ ≤ B) :
    ∀ k : ℕ, ∀ y, y ≤ a0 * 2 ^ k → y ≤ R → ‖Qf a0 y‖ ≤ k * B := by
  intro k
  induction k with
  | zero =>
    intro y hy _
    rw [hnil a0 y (by simpa using hy)]
    simp
  | succ k ih =>
    intro y hy hyR
    by_cases h : y ≤ a0 * 2 ^ k
    · have h1 := ih y h hyR
      have h2 : (k : ℝ) * B ≤ ((k + 1 : ℕ) : ℝ) * B := by
        push_cast
        nlinarith
      linarith
    · push_neg at h
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hN : a0 ≤ a0 * 2 ^ k := by nlinarith
      have hy2 : y ≤ 2 * (a0 * 2 ^ k) := by
        rw [pow_succ] at hy
        linarith
      have hsplit := hadd a0 (a0 * 2 ^ k) y hN h.le
      have e1 := ih (a0 * 2 ^ k) le_rfl (h.le.trans hyR)
      have e2 := hB (a0 * 2 ^ k) y hN (h.le.trans hyR) h.le hy2 hyR
      rw [hsplit]
      calc ‖Qf a0 (a0 * 2 ^ k) + Qf (a0 * 2 ^ k) y‖
          ≤ ‖Qf a0 (a0 * 2 ^ k)‖ + ‖Qf (a0 * 2 ^ k) y‖ := norm_add_le _ _
        _ ≤ k * B + B := add_le_add e1 e2
        _ = ((k + 1 : ℕ) : ℝ) * B := by push_cast; ring

private def wt (Y e : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ e * Real.exp (-((k : ℝ) + 1) / Y)

private theorem wt_props (Y e : ℝ) (hY : 0 < Y) (he : e ≤ 0) :
    (∀ k, wt Y e (k + 1) ≤ wt Y e k) ∧ (∀ k, 0 ≤ wt Y e k) ∧ wt Y e 0 ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    unfold wt
    push_cast
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h1 : ((k : ℝ) + 1 + 1) ^ e ≤ ((k : ℝ) + 1) ^ e :=
      Real.rpow_le_rpow_of_nonpos hk (by linarith) he
    have hinv : 0 ≤ 1 / Y := by positivity
    have e1 : -((k : ℝ) + 1 + 1) / Y = -((k : ℝ) + 1 + 1) * (1 / Y) := by ring
    have e2 : -((k : ℝ) + 1) / Y = -((k : ℝ) + 1) * (1 / Y) := by ring
    have h2 : Real.exp (-((k : ℝ) + 1 + 1) / Y) ≤ Real.exp (-((k : ℝ) + 1) / Y) := by
      apply Real.exp_le_exp.mpr
      rw [e1, e2]
      nlinarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg hk.le _)
  · intro k
    unfold wt
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact mul_nonneg (Real.rpow_nonneg hk.le _) (Real.exp_pos _).le
  · unfold wt
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, one_mul]
    apply Real.exp_le_one_iff.mpr
    have : (0 : ℝ) ≤ 1 / Y := by positivity
    have e1 : -1 / Y = -(1 / Y) := by ring
    rw [e1]
    linarith

private def Tf (F : Type) [Field F] [NumberField F] (B : ℕ) : Finset (Ideal (𝓞 F)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) B).toFinset

private theorem mem_Tf (B : ℕ) (n : Ideal (𝓞 F)) : n ∈ Tf F B ↔ Ideal.absNorm n ≤ B := by
  simp [Tf]

private def term (U β γ : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (n : Ideal (𝓞 F)) : ℂ :=
  ((DetectorDef.a F U n : ℝ) : ℂ) * ω n *
      (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
      ((Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℝ) : ℂ)

private theorem term_bot (U β γ : ℝ) (hβ : 0 < β) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) :
    term U β γ ω ⊥ = 0 := by
  have h : (-((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold term
  simp [Ideal.absNorm_bot, Complex.zero_cpow h]

private theorem term_unit (U β γ : ℝ) (hU : 2 ≤ U) {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) :
    term U β γ ω 1 = ((Real.exp (-1 / U ^ DetectorDef.r) : ℝ) : ℂ) := by
  have h1 : DetectorDef.a F U 1 = 1 := DetectorCoefficients.a_one F U hU
  have h2 : ω 1 = 1 := by
    rw [Ideal.one_eq_top]
    exact ω.map_top'
  unfold term
  rw [h1, h2]
  simp

private theorem term_mid_zero (U β γ : ℝ) (hU : 2 ≤ U) {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (n : Ideal (𝓞 F))
    (h1 : (1 : ℝ) < (Ideal.absNorm n : ℝ)) (h2 : (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.qExp) :
    term U β γ ω n = 0 := by
  have := DetectorCoefficients.a_eq_zero F U hU n h1 h2
  unfold term
  rw [this]
  simp

private theorem exp_cube_le (t : ℝ) (ht : 0 ≤ t) : Real.exp (-t) * t ^ 3 ≤ 6 := by
  have hfac : t ^ 3 / 6 ≤ Real.exp t := by
    have := Real.pow_div_factorial_le_exp t ht 3
    norm_num [Nat.factorial] at this
    linarith
  have hexpmul : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have h6 : t ^ 3 ≤ 6 * Real.exp t := by linarith
  calc Real.exp (-t) * t ^ 3 ≤ Real.exp (-t) * (6 * Real.exp t) :=
        mul_le_mul_of_nonneg_left h6 hpos
    _ = 6 * (Real.exp (-t) * Real.exp t) := by ring
    _ = 6 := by rw [hexpmul]; ring

private theorem term_norm_le (U β γ : ℝ) (hU : 2 ≤ U) (hβ : DetectorDef.σ₀ ≤ β)
    (ω : Detector.PrimitiveFrequencyCharacter F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Ideal (𝓞 F),
      ‖term U β γ ω.character n‖ ≤ C * (Ideal.absNorm n : ℝ) ^ (-3 : ℝ) := by
  obtain ⟨Ca, hCa, hA⟩ := DetectorCoefficients.abs_a_le F (1 / 10 : ℝ) (by norm_num)
  have hU0 : (0 : ℝ) < U := by linarith
  have hY : 0 < U ^ DetectorDef.r := Real.rpow_pos_of_pos hU0 _
  refine ⟨Ca * (6 * (U ^ DetectorDef.r) ^ 3), by positivity, ?_⟩
  intro n
  by_cases hn : n = ⊥
  · subst hn
    rw [term_bot U β γ (by have : (0 : ℝ) < DetectorDef.σ₀ := by norm_num [DetectorDef.σ₀]
                           linarith)]
    simp only [norm_zero]
    simp [Ideal.absNorm_bot]
  · have hne : Ideal.absNorm n ≠ 0 := fun h0 => hn (Ideal.absNorm_eq_zero_iff.mp h0)
    have hNnat : 0 < Ideal.absNorm n := Nat.pos_of_ne_zero hne
    have hN1 : (1 : ℝ) ≤ (Ideal.absNorm n : ℝ) := by exact_mod_cast hNnat
    have hN0 : (0 : ℝ) < (Ideal.absNorm n : ℝ) := by linarith
    have hω : ‖ω.character n‖ ≤ 1 :=
      RayUnitary.ray_character_norm_le_one F _ ω.conductor_ne_zero ω.character n
    have hpow : ‖(Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I))‖
        = (Ideal.absNorm n : ℝ) ^ (-β) := by
      rw [Complex.norm_natCast_cpow_of_pos hNnat]
      simp
    have hσ : (0 : ℝ) < DetectorDef.σ₀ := by norm_num [DetectorDef.σ₀]
    have hσ1 : DetectorDef.σ₀ > 1 / 10 := by norm_num [DetectorDef.σ₀]
    have hpow_nn : 0 ≤ (Ideal.absNorm n : ℝ) ^ (-β) := Real.rpow_nonneg hN0.le _
    have hab : |DetectorDef.a F U n| * (Ideal.absNorm n : ℝ) ^ (-β) ≤ Ca := by
      have h1 := hA U hU n hn
      have h2 : (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) * (Ideal.absNorm n : ℝ) ^ (-β) ≤ 1 := by
        rw [← Real.rpow_add hN0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      calc |DetectorDef.a F U n| * (Ideal.absNorm n : ℝ) ^ (-β)
          ≤ (Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ)) * (Ideal.absNorm n : ℝ) ^ (-β) :=
            mul_le_mul_of_nonneg_right h1 hpow_nn
        _ = Ca * ((Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) * (Ideal.absNorm n : ℝ) ^ (-β)) := by ring
        _ ≤ Ca * 1 := mul_le_mul_of_nonneg_left h2 hCa.le
        _ = Ca := mul_one _
    have hexp : Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) ≤
        6 * (U ^ DetectorDef.r) ^ 3 * ((Ideal.absNorm n : ℝ) ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hN0 3)]
      have h := exp_cube_le ((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) (by positivity)
      have e : Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) =
          Real.exp (-((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r)) := by
        rw [neg_div]
      rw [e]
      calc Real.exp (-((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r)) * (Ideal.absNorm n : ℝ) ^ 3
          = (Real.exp (-((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r)) *
              ((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) ^ 3) * (U ^ DetectorDef.r) ^ 3 := by
            field_simp
        _ ≤ 6 * (U ^ DetectorDef.r) ^ 3 :=
            mul_le_mul_of_nonneg_right h (pow_nonneg hY.le 3)
    have hm3 : (Ideal.absNorm n : ℝ) ^ (-3 : ℝ) = ((Ideal.absNorm n : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hN0.le]
      congr 1
      exact_mod_cast Real.rpow_natCast (Ideal.absNorm n : ℝ) 3
    have hexpn : ‖((Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℝ) : ℂ)‖
        = Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    unfold term
    rw [norm_mul, norm_mul, norm_mul, hpow, hexpn, Complex.norm_real, Real.norm_eq_abs, hm3]
    have hnn : 0 ≤ Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) := (Real.exp_pos _).le
    have h3 : |DetectorDef.a F U n| * ‖ω.character n‖ * (Ideal.absNorm n : ℝ) ^ (-β) ≤ Ca := by
      calc |DetectorDef.a F U n| * ‖ω.character n‖ * (Ideal.absNorm n : ℝ) ^ (-β)
          ≤ |DetectorDef.a F U n| * 1 * (Ideal.absNorm n : ℝ) ^ (-β) := by
            apply mul_le_mul_of_nonneg_right _ hpow_nn
            exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)
        _ ≤ Ca := by rw [mul_one]; exact hab
    calc |DetectorDef.a F U n| * ‖ω.character n‖ * (Ideal.absNorm n : ℝ) ^ (-β) *
          Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r)
        ≤ Ca * (6 * (U ^ DetectorDef.r) ^ 3 * ((Ideal.absNorm n : ℝ) ^ 3)⁻¹) :=
          mul_le_mul h3 hexp hnn hCa.le
      _ = Ca * (6 * (U ^ DetectorDef.r) ^ 3) * ((Ideal.absNorm n : ℝ) ^ 3)⁻¹ := by ring

private theorem summable_ind (U β γ : ℝ) (hU : 2 ≤ U) (hβ : DetectorDef.σ₀ ≤ β)
    (ω : Detector.PrimitiveFrequencyCharacter F) (P : Ideal (𝓞 F) → Prop) [DecidablePred P] :
    Summable (fun n => if P n then term U β γ ω.character n else 0) := by
  obtain ⟨C, hC, hb⟩ := term_norm_le U β γ hU hβ ω
  have hs : Summable (fun n : Ideal (𝓞 F) => (Ideal.absNorm n : ℝ) ^ (-3 : ℝ)) := by
    have := Odlyzko.summable_ideal_absNorm_rpow F (σ := 3) (by norm_num)
    simpa using this
  refine Summable.of_norm_bounded (hs.mul_left C) (fun n => ?_)
  by_cases h : P n
  · rw [if_pos h]; exact hb n
  · rw [if_neg h, norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private def Q (F : Type) [Field F] [NumberField F] (U γ : ℝ) {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (N y : ℝ) : ℂ :=
  ∑ n ∈ Tf F ⌈U ^ DetectorDef.r'⌉₊,
    if N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ y then
      ((DetectorDef.a F U n : ℝ) : ℂ) * ω n *
        (Ideal.absNorm n : ℂ) ^ (-((DetectorDef.σ₀ : ℂ) + (γ : ℂ) * Complex.I))
    else 0

private theorem prefixSum_eq_Q (U γ : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (N y : ℝ) (hy : y ≤ U ^ DetectorDef.r') :
    prefixSum F U ω γ N y = Q F U γ ω N y := by
  unfold prefixSum Q
  apply finsum_eq_sum_of_support_subset
  intro n hn
  rw [Function.mem_support] at hn
  by_contra hnot
  apply hn
  rw [Finset.mem_coe, mem_Tf] at hnot
  rw [if_neg]
  rintro ⟨_, h2⟩
  apply hnot
  have : ((Ideal.absNorm n : ℕ) : ℝ) ≤ (⌈U ^ DetectorDef.r'⌉₊ : ℝ) :=
    h2.trans (hy.trans (Nat.le_ceil _))
  exact_mod_cast this

private theorem Q_add (U γ : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (N y z : ℝ) (hNy : N ≤ y) (hyz : y ≤ z) :
    Q F U γ ω N z = Q F U γ ω N y + Q F U γ ω y z := by
  unfold Q
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : (Ideal.absNorm n : ℝ) ≤ y
  · have hz : (Ideal.absNorm n : ℝ) ≤ z := h.trans hyz
    have h' : ¬ y < (Ideal.absNorm n : ℝ) := not_lt.mpr h
    simp [h, hz, h']
  · have hlt : y < (Ideal.absNorm n : ℝ) := not_le.mp h
    have hNx : N < (Ideal.absNorm n : ℝ) := lt_of_le_of_lt hNy hlt
    simp [h, hlt, hNx]

private theorem Q_nil (U γ : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (N y : ℝ) (h : y ≤ N) : Q F U γ ω N y = 0 := by
  unfold Q
  apply Finset.sum_eq_zero
  intro n _
  rw [if_neg]
  rintro ⟨h1, h2⟩
  linarith

private theorem term_eq (U β γ : ℝ) {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m)
    (n : Ideal (𝓞 F)) (hN : 0 < Ideal.absNorm n) :
    term U β γ ω n =
      (((DetectorDef.a F U n : ℝ) : ℂ) * ω n *
        (Ideal.absNorm n : ℂ) ^ (-((DetectorDef.σ₀ : ℂ) + (γ : ℂ) * Complex.I))) *
      ((wt (U ^ DetectorDef.r) (DetectorDef.σ₀ - β) (Ideal.absNorm n - 1) : ℝ) : ℂ) := by
  have hNc : ((Ideal.absNorm n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcast : (((Ideal.absNorm n - 1 : ℕ) : ℝ) + 1) = (Ideal.absNorm n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  unfold term wt
  rw [hcast]
  have hsplit : (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) =
      (Ideal.absNorm n : ℂ) ^ (-((DetectorDef.σ₀ : ℂ) + (γ : ℂ) * Complex.I)) *
        (Ideal.absNorm n : ℂ) ^ (((DetectorDef.σ₀ - β : ℝ)) : ℂ) := by
    rw [← Complex.cpow_add _ _ hNc]
    congr 1
    push_cast
    ring
  have hc2 : (((Ideal.absNorm n : ℝ) ^ (DetectorDef.σ₀ - β) : ℝ) : ℂ) =
      (Ideal.absNorm n : ℂ) ^ (((DetectorDef.σ₀ - β : ℝ)) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [Complex.ofReal_mul, hc2, hsplit]
  ring

private theorem core (U β γ : ℝ) (ω : Detector.PrimitiveFrequencyCharacter F)
    (hU : 10 ≤ U) (hβ : DetectorDef.σ₀ ≤ β)
    (hsm : ‖smoothedSum F U ω.character β γ‖ ≤ 1 / 4)
    (htail : ‖DetectorTail.smoothedTail F U β γ ω‖ < 1 / 10) :
    ∃ N y : ℝ, U ^ DetectorDef.qExp / 2 < N ∧ N ≤ U ^ DetectorDef.r' ∧ N ≤ y ∧ y ≤ 2 * N ∧
      (1 / 12 : ℝ) / Real.log U ≤ ‖prefixSum F U ω.character γ N y‖ := by
  have hU2 : 2 ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have hσpos : (0 : ℝ) < DetectorDef.σ₀ := by norm_num [DetectorDef.σ₀]
  have hβpos : 0 < β := by linarith
  have hY : 0 < U ^ DetectorDef.r := Real.rpow_pos_of_pos hU0 _
  have ha0pos : 0 < U ^ DetectorDef.qExp := Real.rpow_pos_of_pos hU0 _
  have ha01 : 1 ≤ U ^ DetectorDef.qExp :=
    Real.one_le_rpow (by linarith) (by norm_num [DetectorDef.qExp])
  have hR1 : (1 : ℝ) ≤ U ^ DetectorDef.r' :=
    Real.one_le_rpow (by linarith) (by norm_num [DetectorDef.r'])
  obtain ⟨M, hMdef⟩ : ∃ M : ℂ, M = ∑ n ∈ Tf F ⌈U ^ DetectorDef.r'⌉₊,
      (if U ^ DetectorDef.qExp < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'
        then term U β γ ω.character n else 0) := ⟨_, rfl⟩

  have hdec : smoothedSum F U ω.character β γ =
      ((Real.exp (-1 / U ^ DetectorDef.r) : ℝ) : ℂ) + M +
        DetectorTail.smoothedTail F U β γ ω := by
    have h0 := summable_ind U β γ hU2 hβ ω (fun n => (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r')
    have h1 := summable_ind U β γ hU2 hβ ω
      (fun n => n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ))
    have hpt : ∀ n, term U β γ ω.character n =
        (if (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r' then term U β γ ω.character n else 0) +
        (if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ)
          then term U β γ ω.character n else 0) := by
      intro n
      by_cases h : (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'
      · rw [if_pos h, if_neg (fun hh => absurd hh.2 (not_lt.mpr h)), add_zero]
      · have hn : n ≠ ⊥ := by
          rintro rfl
          apply h
          rw [Ideal.absNorm_bot, Nat.cast_zero]
          exact Real.rpow_nonneg hU0.le _
        rw [if_neg h, if_pos ⟨hn, not_le.mp h⟩, zero_add]
    have e1 : smoothedSum F U ω.character β γ = ∑' n, term U β γ ω.character n := rfl
    have e2 : DetectorTail.smoothedTail F U β γ ω = ∑' n,
        (if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ)
          then term U β γ ω.character n else 0) := rfl
    have e3 : ∑' n, term U β γ ω.character n = ∑' n,
        ((if (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r' then term U β γ ω.character n else 0) +
        (if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ)
          then term U β γ ω.character n else 0)) := tsum_congr hpt
    have e4 : ∑' n, (if (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'
        then term U β γ ω.character n else 0) =
        ∑ n ∈ Tf F ⌈U ^ DetectorDef.r'⌉₊, (if (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'
        then term U β γ ω.character n else 0) := by
      apply tsum_eq_sum
      intro n hn
      rw [if_neg]
      intro h
      apply hn
      rw [mem_Tf]
      have : (Ideal.absNorm n : ℝ) ≤ (⌈U ^ DetectorDef.r'⌉₊ : ℝ) := h.trans (Nat.le_ceil _)
      exact_mod_cast this
    have e5 : ∀ n, (if (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'
        then term U β γ ω.character n else 0) =
        (if n = 1 then term U β γ ω.character n else 0) +
        (if U ^ DetectorDef.qExp < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'
          then term U β γ ω.character n else 0) := by
      intro n
      by_cases hn1 : n = 1
      · subst hn1
        have h1 : ((Ideal.absNorm (1 : Ideal (𝓞 F)) : ℕ) : ℝ) = 1 := by simp
        have h2 : ¬ (U ^ DetectorDef.qExp < 1) := not_lt.mpr ha01
        simp [h1, hR1, h2]
      · by_cases hb : n = ⊥
        · subst hb
          rw [term_bot U β γ hβpos]
          simp
        · have hN : 2 ≤ Ideal.absNorm n := by
            have h0 : Ideal.absNorm n ≠ 0 := fun h => hb (Ideal.absNorm_eq_zero_iff.mp h)
            have h1' : Ideal.absNorm n ≠ 1 := fun h =>
              hn1 ((Ideal.absNorm_eq_one_iff.mp h).trans Ideal.one_eq_top.symm)
            omega
          have hN' : (1 : ℝ) < Ideal.absNorm n := by
            have : (2 : ℝ) ≤ Ideal.absNorm n := by exact_mod_cast hN
            linarith
          by_cases hq : (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.qExp
          · rw [term_mid_zero U β γ hU2 ω.character n hN' hq]
            simp
          · have hq' := not_le.mp hq
            by_cases hr : (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'
            · rw [if_pos hr, if_neg hn1, if_pos ⟨hq', hr⟩, zero_add]
            · rw [if_neg hr, if_neg hn1, if_neg (fun h => hr h.2), zero_add]
    have h1mem : (1 : Ideal (𝓞 F)) ∈ Tf F ⌈U ^ DetectorDef.r'⌉₊ := by
      rw [mem_Tf]
      have h3 : (1 : ℝ) ≤ (⌈U ^ DetectorDef.r'⌉₊ : ℝ) := hR1.trans (Nat.le_ceil _)
      have h1 : Ideal.absNorm (1 : Ideal (𝓞 F)) = 1 := by simp
      rw [h1]
      exact_mod_cast h3
    have hs1 : ∑ n ∈ Tf F ⌈U ^ DetectorDef.r'⌉₊, (if n = 1 then term U β γ ω.character n else 0)
        = term U β γ ω.character 1 := by
      rw [Finset.sum_eq_single (1 : Ideal (𝓞 F))]
      · rw [if_pos rfl]
      · intro n _ hn
        rw [if_neg hn]
      · intro h
        exact absurd h1mem h
    have e6 : ∑' n, ((if (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r' then term U β γ ω.character n else 0) +
        (if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ)
          then term U β γ ω.character n else 0)) =
        ∑' n, (if (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r' then term U β γ ω.character n else 0) +
        ∑' n, (if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ)
          then term U β γ ω.character n else 0) := h0.tsum_add h1
    rw [e1, e2, e3, e6, e4, Finset.sum_congr rfl (fun n _ => e5 n),
      Finset.sum_add_distrib, hs1, term_unit U β γ hU2 ω.character, hMdef]

  have hE : ‖((Real.exp (-1 / U ^ DetectorDef.r) : ℝ) : ℂ)‖ =
      Real.exp (-1 / U ^ DetectorDef.r) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hYge : 10 ≤ U ^ DetectorDef.r := by
    calc (10 : ℝ) ≤ U := hU
      _ = U ^ (1 : ℝ) := (Real.rpow_one U).symm
      _ ≤ U ^ DetectorDef.r :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num [DetectorDef.r])
  have hexp : 9 / 10 ≤ Real.exp (-1 / U ^ DetectorDef.r) := by
    have h := Real.add_one_le_exp (-1 / U ^ DetectorDef.r)
    have h2 : 1 / U ^ DetectorDef.r ≤ 1 / 10 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have e : -1 / U ^ DetectorDef.r = -(1 / U ^ DetectorDef.r) := by ring
    linarith
  have hM : 1 / 2 ≤ ‖M‖ := by
    have h1 : ((Real.exp (-1 / U ^ DetectorDef.r) : ℝ) : ℂ) =
        smoothedSum F U ω.character β γ - M - DetectorTail.smoothedTail F U β γ ω := by
      rw [hdec]
      ring
    have h2 : ‖((Real.exp (-1 / U ^ DetectorDef.r) : ℝ) : ℂ)‖ ≤
        ‖smoothedSum F U ω.character β γ‖ + ‖M‖ + ‖DetectorTail.smoothedTail F U β γ ω‖ := by
      calc ‖((Real.exp (-1 / U ^ DetectorDef.r) : ℝ) : ℂ)‖
          = ‖smoothedSum F U ω.character β γ - M - DetectorTail.smoothedTail F U β γ ω‖ :=
            congrArg norm h1
        _ ≤ ‖smoothedSum F U ω.character β γ - M‖ + ‖DetectorTail.smoothedTail F U β γ ω‖ :=
            norm_sub_le _ _
        _ ≤ ‖smoothedSum F U ω.character β γ‖ + ‖M‖ +
            ‖DetectorTail.smoothedTail F U β γ ω‖ := by
            have := norm_sub_le (smoothedSum F U ω.character β γ) M
            linarith
    linarith

  have habel : ∃ y : ℝ, y ≤ U ^ DetectorDef.r' ∧
      ‖M‖ ≤ ‖Q F U γ ω.character (U ^ DetectorDef.qExp) y‖ := by
    have hmid : ∀ n ∈ (Tf F ⌈U ^ DetectorDef.r'⌉₊).filter (fun n =>
        U ^ DetectorDef.qExp < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'),
        1 ≤ Ideal.absNorm n := by
      intro n hn
      rw [Finset.mem_filter] at hn
      have h1' : (1 : ℝ) < ((Ideal.absNorm n : ℕ) : ℝ) := lt_of_le_of_lt ha01 hn.2.1
      have : 1 < Ideal.absNorm n := by exact_mod_cast h1'
      omega
    have hle : ∀ n ∈ (Tf F ⌈U ^ DetectorDef.r'⌉₊).filter (fun n =>
        U ^ DetectorDef.qExp < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'),
        Ideal.absNorm n ≤ ⌈U ^ DetectorDef.r'⌉₊ := by
      intro n hn
      rw [Finset.mem_filter, mem_Tf] at hn
      exact hn.1
    obtain ⟨hw1, hw2, hw3⟩ := wt_props (U ^ DetectorDef.r) (DetectorDef.σ₀ - β) hY (by linarith)
    obtain ⟨j, hj⟩ := abel_ideal
      ((Tf F ⌈U ^ DetectorDef.r'⌉₊).filter (fun n =>
        U ^ DetectorDef.qExp < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'))
      Ideal.absNorm ⌈U ^ DetectorDef.r'⌉₊ hmid hle
      (fun n => ((DetectorDef.a F U n : ℝ) : ℂ) * ω.character n *
        (Ideal.absNorm n : ℂ) ^ (-((DetectorDef.σ₀ : ℂ) + (γ : ℂ) * Complex.I)))
      (wt (U ^ DetectorDef.r) (DetectorDef.σ₀ - β)) hw1 hw2 hw3
    have hMf : M = ∑ n ∈ (Tf F ⌈U ^ DetectorDef.r'⌉₊).filter (fun n =>
        U ^ DetectorDef.qExp < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'),
        ((DetectorDef.a F U n : ℝ) : ℂ) * ω.character n *
          (Ideal.absNorm n : ℂ) ^ (-((DetectorDef.σ₀ : ℂ) + (γ : ℂ) * Complex.I)) *
        ((wt (U ^ DetectorDef.r) (DetectorDef.σ₀ - β) (Ideal.absNorm n - 1) : ℝ) : ℂ) := by
      rw [hMdef, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs with h
      · apply term_eq
        have h1' : (1 : ℝ) < ((Ideal.absNorm n : ℕ) : ℝ) := lt_of_le_of_lt ha01 h.1
        have : 1 < Ideal.absNorm n := by exact_mod_cast h1'
        omega
      · rfl
    refine ⟨min (j : ℝ) (U ^ DetectorDef.r'), min_le_right _ _, ?_⟩
    have hQ : ∑ n ∈ (Tf F ⌈U ^ DetectorDef.r'⌉₊).filter (fun n =>
        U ^ DetectorDef.qExp < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r'),
        (if Ideal.absNorm n ≤ j then ((DetectorDef.a F U n : ℝ) : ℂ) * ω.character n *
          (Ideal.absNorm n : ℂ) ^ (-((DetectorDef.σ₀ : ℂ) + (γ : ℂ) * Complex.I)) else 0) =
        Q F U γ ω.character (U ^ DetectorDef.qExp) (min (j : ℝ) (U ^ DetectorDef.r')) := by
      rw [Finset.sum_filter]
      unfold Q
      apply Finset.sum_congr rfl
      intro n _
      have h3r : (Ideal.absNorm n ≤ j) ↔ ((Ideal.absNorm n : ℝ) ≤ (j : ℝ)) :=
        (Nat.cast_le (α := ℝ)).symm
      simp only [h3r, le_min_iff]
      by_cases h1 : U ^ DetectorDef.qExp < (Ideal.absNorm n : ℝ) <;>
      by_cases h2 : (Ideal.absNorm n : ℝ) ≤ U ^ DetectorDef.r' <;>
      by_cases h3 : (Ideal.absNorm n : ℝ) ≤ (j : ℝ) <;> simp [h1, h2, h3]
    rw [hMf, ← hQ]
    exact hj
  obtain ⟨y', hy'R, hy'⟩ := habel

  have hlog1 : 1 ≤ Real.log U := by
    rw [Real.le_log_iff_exp_le hU0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog2 := Real.log_two_gt_d9
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌈2 * Real.log U⌉₊ := ⟨_, rfl⟩
  have hKge : 2 * Real.log U ≤ K := by rw [hKdef]; exact Nat.le_ceil _
  have hKle : (K : ℝ) < 2 * Real.log U + 1 := by
    rw [hKdef]; exact Nat.ceil_lt_add_one (by linarith)
  have hUK : U ≤ 2 ^ K := by
    have h : Real.log U ≤ Real.log ((2 : ℝ) ^ K) := by
      rw [Real.log_pow]
      nlinarith [mul_nonneg (sub_nonneg.mpr hKge) (by linarith : (0 : ℝ) ≤ Real.log 2),
        mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log U)
          (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2)]
    exact (Real.log_le_log_iff hU0 (by positivity)).mp h
  have hRle : U ^ DetectorDef.r' ≤ U ^ DetectorDef.qExp * 2 ^ K := by
    have e : U ^ DetectorDef.r' = U ^ DetectorDef.qExp * U ^ (DetectorDef.r' - DetectorDef.qExp) := by
      rw [← Real.rpow_add hU0]
      congr 1
      ring
    have h2 : U ^ (DetectorDef.r' - DetectorDef.qExp) ≤ U := by
      calc U ^ (DetectorDef.r' - DetectorDef.qExp) ≤ U ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith)
              (by norm_num [DetectorDef.r', DetectorDef.qExp])
        _ = U := Real.rpow_one U
    rw [e]
    calc U ^ DetectorDef.qExp * U ^ (DetectorDef.r' - DetectorDef.qExp)
        ≤ U ^ DetectorDef.qExp * U := mul_le_mul_of_nonneg_left h2 ha0pos.le
      _ ≤ U ^ DetectorDef.qExp * 2 ^ K := mul_le_mul_of_nonneg_left hUK ha0pos.le
  have hB0 : (0 : ℝ) ≤ (1 / 12 : ℝ) / Real.log U := by
    apply div_nonneg (by norm_num)
    linarith
  by_contra hcon
  have hBd : ∀ N y : ℝ, U ^ DetectorDef.qExp ≤ N → N ≤ U ^ DetectorDef.r' → N ≤ y → y ≤ 2 * N →
      y ≤ U ^ DetectorDef.r' → ‖Q F U γ ω.character N y‖ ≤ (1 / 12 : ℝ) / Real.log U := by
    intro N y h1 h2 h3 h4 h5
    by_contra hlt
    push_neg at hlt
    apply hcon
    refine ⟨N, y, by linarith, h2, h3, h4, ?_⟩
    rw [prefixSum_eq_Q U γ ω.character N y h5]
    exact hlt.le
  have hfin := dyad (U ^ DetectorDef.qExp) (U ^ DetectorDef.r') ((1 / 12 : ℝ) / Real.log U)
    (Q F U γ ω.character) ha0pos hB0 (fun N y z h1 h2 => Q_add U γ ω.character N y z h1 h2)
    (fun N y h => Q_nil U γ ω.character N y h) hBd K y' (hy'R.trans hRle) hy'R
  have h4 : (K : ℝ) * ((1 / 12 : ℝ) / Real.log U) ≤ (3 * Real.log U) * ((1 / 12 : ℝ) / Real.log U) :=
    mul_le_mul_of_nonneg_right (by linarith) hB0
  have h5 : (3 * Real.log U) * ((1 / 12 : ℝ) / Real.log U) = 1 / 4 := by
    have : Real.log U ≠ 0 := by linarith
    field_simp
    norm_num
  linarith

theorem detector_prefix (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ u ∈ exceptionalSet D ρ U, ∀ s : ℂ, IsLZero (D.omega u) s → σ₀ ≤ s.re → s.re ≤ 1 →
        |s.im| ≤ 4 * U ^ ρ →
        ∃ N y : ℝ, U ^ DetectorDef.qExp / 2 < N ∧ N ≤ U ^ DetectorDef.r' ∧ N ≤ y ∧ y ≤ 2 * N ∧
          c₁ / Real.log U ≤ ‖prefixSum F U (D.omega u).character s.im N y‖ := by
  obtain ⟨_, _, _, _, _, hspec⟩ := hρ
  obtain ⟨U₁, hU₁, hH⟩ := hspec (1 / 4) (by norm_num)
  obtain ⟨U₂, hU₂, hT⟩ := DetectorTail.smoothedTail_tendsto_zero (F := F) (1 / 10) (by norm_num)
  refine ⟨1 / 12, by norm_num, max (max U₁ U₂) 10, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro U hU u hu s hs hσ hs1 hγ
  have hUa : U₁ ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hU
  have hUb : U₂ ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hU
  have hUc : 10 ≤ U := le_trans (le_max_right _ _) hU
  exact core U s.re s.im (D.omega u) hUc hσ (hH U hUa u hu s hs hσ hs1 hγ)
    (hT U s.re s.im (D.omega u) hUb hσ hs1)

end

end DedekindZetaZeroFree.Quantitative.DetectorPrefix
