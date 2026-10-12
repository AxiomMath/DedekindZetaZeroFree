module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.HolomorphicLogarithmControl

@[expose] public section

open Set Metric Complex

namespace DedekindZetaZeroFree

private theorem reciprocal_growth_envelope (A B C ρ U : ℝ) (hρ : 0 < ρ)
    (hU : 1 ≤ U) (y : ℝ) (hy : |y| ≤ 4 * U ^ ρ) :
    C * U ^ B * (2 + |y|) ^ A ≤
      (max 0 C * 6 ^ |A|) * U ^ (|B| + ρ * |A|) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hT : 1 ≤ U ^ ρ := Real.one_le_rpow hU hρ.le
  have hb : U ^ B ≤ U ^ |B| := Real.rpow_le_rpow_of_exponent_le hU (le_abs_self _)
  have ha : (2 + |y|) ^ A ≤ (6 * U ^ ρ) ^ |A| := by
    apply (Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 2 + |y| by linarith [abs_nonneg y])
      (le_abs_self A)).trans
    apply Real.rpow_le_rpow (by positivity) (by linarith) (abs_nonneg _)
  calc
    C * U ^ B * (2 + |y|) ^ A ≤ (max 0 C * U ^ |B|) * (6 * U ^ ρ) ^ |A| := by
      exact mul_le_mul
        (mul_le_mul (le_max_right _ _) hb (Real.rpow_nonneg hUp.le _) (le_max_left _ _))
        ha (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = (max 0 C * 6 ^ |A|) * U ^ (|B| + ρ * |A|) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg hUp.le _),
        ← Real.rpow_mul hUp.le, Real.rpow_add hUp]
      ring

theorem detector_reciprocal_disk
    (A B C C₁ ρ U₀ : ℝ) (hρ : 0 < ρ) (hU₀ : 2 ≤ U₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ Cε Uε : ℝ, 0 < Cε ∧ U₀ ≤ Uε ∧
        ∀ (U : ℝ) (f eulerLog : ℂ → ℂ), Uε ≤ U →
          DifferentiableOn ℂ f
            {s : ℂ | 249 / 250 < s.re ∧ |s.im| ≤ 4 * U ^ ρ} →
          (∀ s : ℂ, 249 / 250 < s.re → |s.im| ≤ 4 * U ^ ρ → f s ≠ 0) →
          (∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
            ‖f s‖ ≤ C * U ^ B * (2 + |s.im|) ^ A) →
          DifferentiableOn ℂ eulerLog {s : ℂ | 1 < s.re} →
          (∀ s : ℂ, 1 < s.re → Complex.exp (eulerLog s) = f s) →
          (∀ s : ℂ, 1001 / 1000 ≤ s.re → ‖eulerLog s‖ ≤ C₁) →
          ∀ s : ℂ, 499 / 500 ≤ s.re → |s.im| ≤ 2 * U ^ ρ →
            ‖(f s)⁻¹‖ ≤ Cε * U ^ ε := by
  intro ε hε
  obtain ⟨M, hM, hMb⟩ := LogarithmicControl.absorb_polynomial_constant
    (K := max 0 C * 6 ^ |A|) (p := |B| + ρ * |A|) (by positivity)
  obtain ⟨D, hD, hDb⟩ := LogarithmicControl.logarithmic_control
    (e := 1 / 4000) (A := max 1 C₁) (M := M) (ε := ε)
    (by norm_num) (by norm_num) (le_max_left _ _) hM hε
  refine ⟨D + Real.exp C₁, max U₀ (Real.exp 1), by positivity, le_max_left _ _, ?_⟩
  intro U f E hU hf hzero hg hE hexp hEb s hs ht
  have hUe : Real.exp 1 ≤ U := (le_max_right _ _).trans hU
  have hU1 : 1 ≤ U := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hUe
  have hT : 1 ≤ U ^ ρ := Real.one_le_rpow hU1 hρ.le
  have hpow : 1 ≤ U ^ ε := Real.one_le_rpow hU1 hε.le
  by_cases hsE : 1001 / 1000 ≤ s.re
  · rw [← hexp s (by linarith), ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
    have hb : -(E s).re ≤ C₁ :=
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hEb s hsE))
    exact (Real.exp_le_exp.mpr hb).trans (by
      nlinarith [Real.exp_pos C₁])
  · let c : ℂ := 2 + (s.im : ℂ) * Complex.I
    have disk_rect : ball c (2 - 249 / 250 - 2 * (1 / 4000)) ⊆
        {z : ℂ | 249 / 250 < z.re ∧ |z.im| ≤ 4 * U ^ ρ} := by
      intro z hz
      have hre := LogarithmicControl.disk_re_gt hz
      have hn : ‖z - c‖ < 2 - 249 / 250 - 2 * (1 / 4000) := by
        simpa only [mem_ball, dist_eq_norm] using hz
      have hi := Complex.abs_im_le_norm (z - c)
      have hcim : c.im = s.im := by simp [c]
      rw [Complex.sub_im, hcim] at hi
      have habs := abs_add_le (z.im - s.im) s.im
      have htri : |z.im| ≤ |z.im - s.im| + |s.im| := by
        convert habs using 1 <;> ring
      exact ⟨by linarith, by linarith⟩
    have disk_re : ∀ z ∈ ball c (2 - 249 / 250 - 2 * (1 / 4000)),
        3 / 1000 ≤ z.re ∧ z.re ≤ 4 := by
      intro z hz
      have hn : ‖z - c‖ < 2 - 249 / 250 - 2 * (1 / 4000) := by
        simpa only [mem_ball, dist_eq_norm] using hz
      have hr := Complex.abs_re_le_norm (z - c)
      have hcre : c.re = 2 := by simp [c]
      rw [Complex.sub_re, hcre] at hr
      constructor <;> linarith [le_abs_self (z.re - 2), neg_le_abs (z.re - 2)]
    have hfball := hf.mono disk_rect
    have hpoly : ∀ z ∈ ball c (2 - 249 / 250 - 3 * (1 / 4000)), ‖f z‖ ≤ U ^ M := by
      intro z hz
      have hzbig : z ∈ ball c (2 - 249 / 250 - 2 * (1 / 4000)) :=
        ball_subset_ball (by norm_num) hz
      exact (hg z (disk_re z hzbig).1 (disk_re z hzbig).2).trans
        ((reciprocal_growth_envelope A B C ρ U hρ hU1 z.im (disk_rect hzbig).2).trans (hMb U hUe))
    have half_re : ∀ z ∈ ball c (1 / 2), 1 < z.re := by
      intro z hz
      have hn : ‖z - c‖ < 1 / 2 := by simpa only [mem_ball, dist_eq_norm] using hz
      have hr := Complex.abs_re_le_norm (z - c)
      have hcre : c.re = 2 := by simp [c]
      rw [Complex.sub_re, hcre] at hr
      linarith [neg_le_abs (z.re - 2)]
    have hEball : DifferentiableOn ℂ E (ball c (1 / 2)) :=
      hE.mono (by intro z hz; exact half_re z hz)
    have hELball : EqOn (Complex.exp ∘ E) f (ball c (1 / 2)) :=
      fun z hz => hexp z (half_re z hz)
    have hEin : ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ max 1 C₁ := by
      intro z hz
      have hn : ‖z - c‖ ≤ 49 / 100 := by simpa only [mem_closedBall, dist_eq_norm] using hz
      have hr := Complex.abs_re_le_norm (z - c)
      have hcre : c.re = 2 := by simp [c]
      rw [Complex.sub_re, hcre] at hr
      exact (hEb z (by linarith [neg_le_abs (z.re - 2)])).trans (le_max_right _ _)
    have hz : s ∈ closedBall c (2 - 249 / 250 - 6 * (1 / 4000)) := by
      have hm := LogarithmicControl.same_height_mem_disk
        (a := 249 / 250) (e := 1 / 4000) (v := 1 / 500) (t := s.im)
        (x := s.re) (by norm_num) (by linarith) (by linarith)
      have heq : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
      rw [heq] at hm
      exact closedBall_subset_closedBall (by norm_num) hm
    have hb := (hDb (249 / 250) U f E c (by norm_num) (by norm_num) hUe hfball
      (fun z hz => hzero z (disk_rect hz).1 (disk_rect hz).2) hpoly hEball hELball hEin).1 s hz
    have hinv : ‖(f s)⁻¹‖ ≤ D * U ^ ε := by linarith [norm_nonneg (f s)]
    exact hinv.trans (by nlinarith [Real.exp_pos C₁, Real.rpow_nonneg (show 0 ≤ U by linarith) ε])

end DedekindZetaZeroFree
