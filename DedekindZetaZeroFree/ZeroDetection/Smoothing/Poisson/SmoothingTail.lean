module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Coefficients

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorTail

noncomputable section

open DedekindZetaZeroFree NumberField Filter Topology
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def smoothedTail (F : Type) [Field F] [NumberField F] (U β γ : ℝ)
    (ω : Detector.PrimitiveFrequencyCharacter F) : ℂ :=
  ∑' n : Ideal (𝓞 F),
    if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ) then
      (DetectorDef.a F U n : ℂ) * ω.character n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
        (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℂ)
    else 0

private lemma r'_sub_r : DetectorDef.r' - DetectorDef.r = 1 / 200 := by
  norm_num [DetectorDef.r, DetectorDef.r']

private lemma exp_neg_mul_cube_le (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) * t ^ 3 ≤ 6 := by
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

private lemma exp_half_mul_cube_le (N Y : ℝ) (hN : 0 ≤ N) (hY : 0 < Y) :
    Real.exp (-(N / (2 * Y))) * N ^ 3 ≤ 48 * Y ^ 3 := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = N / (2 * Y) := ⟨_, rfl⟩
  have hY2 : (2 * Y) ≠ 0 := (mul_pos two_pos hY).ne'
  have hNt : N = t * (2 * Y) := by
    rw [ht, div_mul_cancel₀ _ hY2]
  have ht0 : 0 ≤ t := by
    rw [ht]; exact div_nonneg hN (mul_pos two_pos hY).le
  rw [← ht, hNt]
  have h1 := exp_neg_mul_cube_le t ht0
  have hY3 : 0 ≤ Y ^ 3 := pow_nonneg hY.le 3
  calc Real.exp (-t) * (t * (2 * Y)) ^ 3 = (Real.exp (-t) * t ^ 3) * (8 * Y ^ 3) := by ring
    _ ≤ 6 * (8 * Y ^ 3) := mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = 48 * Y ^ 3 := by ring

private lemma term_bound (U β γ : ℝ) (ω : Detector.PrimitiveFrequencyCharacter F)
    (hU : 2 ≤ U) (hβ : DetectorDef.σ₀ ≤ β) (Ca : ℝ) (hCa : 0 < Ca)
    (hA : ∀ n : Ideal (𝓞 F), n ≠ ⊥ →
      |DetectorDef.a F U n| ≤ Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ))
    (n : Ideal (𝓞 F)) :
    ‖(if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ) then
      (DetectorDef.a F U n : ℂ) * ω.character n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
        (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℂ)
      else 0)‖ ≤
      48 * Ca * U ^ (3 * DetectorDef.r) * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) *
        (Ideal.absNorm n : ℝ) ^ (-2 : ℝ) := by
  have hU0 : (0 : ℝ) < U := by linarith
  have hE : 0 ≤ Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) := (Real.exp_pos _).le
  have hYpos : 0 < U ^ DetectorDef.r := Real.rpow_pos_of_pos hU0 _
  have hY3 : U ^ (3 * DetectorDef.r) = (U ^ DetectorDef.r) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    congr 1
    push_cast
    ring
  split_ifs with h
  · obtain ⟨hn, hgt⟩ := h
    have hne : Ideal.absNorm n ≠ 0 := fun h0 => hn (Ideal.absNorm_eq_zero_iff.mp h0)
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
    have hpow_le : (Ideal.absNorm n : ℝ) ^ (-β) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hpow_nn : 0 ≤ (Ideal.absNorm n : ℝ) ^ (-β) := Real.rpow_nonneg hN0.le _
    have ha : ‖(DetectorDef.a F U n : ℂ)‖ ≤ Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hA n hn
    have hexpn : ‖(Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℂ)‖
        = Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hsplitY : U ^ DetectorDef.r' = U ^ (1 / 200 : ℝ) * U ^ DetectorDef.r := by
      rw [← Real.rpow_add hU0, ← r'_sub_r]
      congr 1
      ring
    have hX : U ^ (1 / 200 : ℝ) ≤ (Ideal.absNorm n : ℝ) / U ^ DetectorDef.r := by
      rw [le_div_iff₀ hYpos]
      linarith
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Ideal.absNorm n : ℝ) / (2 * U ^ DetectorDef.r) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by
      rw [ht]; exact div_nonneg hN0.le (mul_pos two_pos hYpos).le
    have hEsplit : Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r)
        = Real.exp (-t) * Real.exp (-t) := by
      rw [← Real.exp_add, ht]
      congr 1
      ring
    have hExpT : Real.exp (-t) ≤ Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) := by
      apply Real.exp_le_exp.mpr
      have h2 : t = ((Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) / 2 := by
        rw [ht]; ring
      rw [h2]
      linarith
    have hD : Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r)
        ≤ Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) * Real.exp (-t) := by
      rw [hEsplit]
      exact mul_le_mul_of_nonneg_right hExpT (Real.exp_pos _).le
    have hkey : Real.exp (-t) * (Ideal.absNorm n : ℝ) ^ 3 ≤ 48 * (U ^ DetectorDef.r) ^ 3 := by
      rw [ht]
      exact exp_half_mul_cube_le _ _ hN0.le hYpos
    have hN1' : (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) ≤ (Ideal.absNorm n : ℝ) := by
      calc (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) ≤ (Ideal.absNorm n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = (Ideal.absNorm n : ℝ) := Real.rpow_one _
    have hexp0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have hNm2 : (Ideal.absNorm n : ℝ) ^ (-2 : ℝ) = ((Ideal.absNorm n : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hN0.le, Real.rpow_two]
    have hmain : (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) * Real.exp (-t)
        ≤ 48 * (U ^ DetectorDef.r) ^ 3 * (Ideal.absNorm n : ℝ) ^ (-2 : ℝ) := by
      rw [hNm2, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hN0 2)]
      have h2 : (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) * Real.exp (-t)
          ≤ (Ideal.absNorm n : ℝ) * Real.exp (-t) := mul_le_mul_of_nonneg_right hN1' hexp0
      calc (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) * Real.exp (-t) * (Ideal.absNorm n : ℝ) ^ 2
          ≤ (Ideal.absNorm n : ℝ) * Real.exp (-t) * (Ideal.absNorm n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = Real.exp (-t) * (Ideal.absNorm n : ℝ) ^ 3 := by ring
        _ ≤ 48 * (U ^ DetectorDef.r) ^ 3 := hkey
    have hAB : ‖(DetectorDef.a F U n : ℂ)‖ * ‖ω.character n‖ ≤
        Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) := by
      calc ‖(DetectorDef.a F U n : ℂ)‖ * ‖ω.character n‖
          ≤ (Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ)) * 1 :=
            mul_le_mul ha hω (norm_nonneg _)
              (mul_nonneg hCa.le (Real.rpow_nonneg hN0.le _))
        _ = Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) := mul_one _
    have hABC : ‖(DetectorDef.a F U n : ℂ)‖ * ‖ω.character n‖ *
        (Ideal.absNorm n : ℝ) ^ (-β) ≤ Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) := by
      calc ‖(DetectorDef.a F U n : ℂ)‖ * ‖ω.character n‖ * (Ideal.absNorm n : ℝ) ^ (-β)
          ≤ (Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ)) * 1 :=
            mul_le_mul hAB hpow_le hpow_nn (mul_nonneg hCa.le (Real.rpow_nonneg hN0.le _))
        _ = Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) := mul_one _
    have hL : ‖(DetectorDef.a F U n : ℂ)‖ * ‖ω.character n‖ * (Ideal.absNorm n : ℝ) ^ (-β) *
        Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r)
        ≤ (Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ)) *
          (Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) * Real.exp (-t)) :=
      mul_le_mul hABC hD (Real.exp_pos _).le (mul_nonneg hCa.le (Real.rpow_nonneg hN0.le _))
    rw [norm_mul, norm_mul, norm_mul, hpow, hexpn]
    calc ‖(DetectorDef.a F U n : ℂ)‖ * ‖ω.character n‖ * (Ideal.absNorm n : ℝ) ^ (-β) *
          Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r)
        ≤ (Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ)) *
          (Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) * Real.exp (-t)) := hL
      _ = Ca * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) *
          ((Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) * Real.exp (-t)) := by ring
      _ ≤ Ca * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) *
          (48 * (U ^ DetectorDef.r) ^ 3 * (Ideal.absNorm n : ℝ) ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hmain (mul_nonneg hCa.le hE)
      _ = 48 * Ca * U ^ (3 * DetectorDef.r) * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) *
          (Ideal.absNorm n : ℝ) ^ (-2 : ℝ) := by rw [hY3]; ring
  · simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCa.le)
      (Real.rpow_nonneg hU0.le _)) hE) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem smoothedTail_bound :
    ∃ C A : ℝ, 0 < C ∧ ∀ (U β γ : ℝ) (ω : Detector.PrimitiveFrequencyCharacter F),
      2 ≤ U → DetectorDef.σ₀ ≤ β → β ≤ 1 →
        ‖smoothedTail F U β γ ω‖ ≤ C * U ^ A * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) := by
  obtain ⟨Ca, hCa, hA⟩ := DetectorCoefficients.abs_a_le F (1 / 10 : ℝ) (by norm_num)
  have hsum : Summable (fun n : Ideal (𝓞 F) => (Ideal.absNorm n : ℝ) ^ (-2 : ℝ)) :=
    Odlyzko.summable_ideal_absNorm_rpow F (σ := 2) (by norm_num)
  have hS0 : 0 ≤ ∑' n : Ideal (𝓞 F), (Ideal.absNorm n : ℝ) ^ (-2 : ℝ) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨48 * Ca * (∑' n : Ideal (𝓞 F), (Ideal.absNorm n : ℝ) ^ (-2 : ℝ)) + 1,
    3 * DetectorDef.r, ?_, ?_⟩
  · have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 48) hCa.le) hS0
    linarith
  intro U β γ ω hU hβ hβ1
  have hU0 : (0 : ℝ) < U := by linarith
  have hE : 0 ≤ Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) := (Real.exp_pos _).le
  have hYE : 0 ≤ U ^ (3 * DetectorDef.r) * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) :=
    mul_nonneg (Real.rpow_nonneg hU0.le _) hE
  have hdom := hsum.hasSum.mul_left
    (48 * Ca * U ^ (3 * DetectorDef.r) * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2))
  unfold smoothedTail
  have hb := tsum_of_norm_bounded hdom (fun n =>
    term_bound U β γ ω hU hβ Ca hCa (fun n hn => hA U hU n hn) n)
  refine le_trans hb ?_
  nlinarith [hYE, hS0, hCa]

theorem smoothedTail_tendsto_zero :
    ∀ ε : ℝ, 0 < ε → ∃ U₀ : ℝ, 2 ≤ U₀ ∧
      ∀ (U β γ : ℝ) (ω : Detector.PrimitiveFrequencyCharacter F),
        U₀ ≤ U → DetectorDef.σ₀ ≤ β → β ≤ 1 → ‖smoothedTail F U β γ ω‖ < ε := by
  intro ε hε
  obtain ⟨C, A, hC, hbd⟩ := smoothedTail_bound (F := F)
  have hx : Tendsto (fun U : ℝ => U ^ (1 / 200 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hT : Tendsto (fun x : ℝ => x ^ (200 * A) * Real.exp (-(1 / 2) * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (200 * A) (1 / 2) (by norm_num)
  have hlim : Tendsto (fun U : ℝ => C * ((U ^ (1 / 200 : ℝ)) ^ (200 * A) *
      Real.exp (-(1 / 2) * U ^ (1 / 200 : ℝ)))) atTop (𝓝 0) := by
    have h := (hT.comp hx).const_mul C
    rw [mul_zero] at h
    exact h
  have hev := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp hev
  refine ⟨max U₁ 2, le_max_right _ _, ?_⟩
  intro U β γ ω hU hβ hβ1
  have hU2 : 2 ≤ U := le_trans (le_max_right _ _) hU
  have hU1 : U₁ ≤ U := le_trans (le_max_left _ _) hU
  have hU0 : (0 : ℝ) < U := by linarith
  have e1 : (U ^ (1 / 200 : ℝ)) ^ (200 * A) = U ^ A := by
    rw [← Real.rpow_mul hU0.le]
    congr 1
    ring
  have e2 : -(U ^ (1 / 200 : ℝ)) / 2 = -(1 / 2) * U ^ (1 / 200 : ℝ) := by ring
  calc ‖smoothedTail F U β γ ω‖ ≤ C * U ^ A * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) :=
        hbd U β γ ω hU2 hβ hβ1
    _ = C * ((U ^ (1 / 200 : ℝ)) ^ (200 * A) * Real.exp (-(1 / 2) * U ^ (1 / 200 : ℝ))) := by
        rw [e1, e2]; ring
    _ < ε := hU₁ U hU1

end

end DedekindZetaZeroFree.Quantitative.DetectorTail
