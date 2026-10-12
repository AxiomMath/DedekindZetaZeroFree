module

public import DedekindZetaZeroFree.LFunctions.Hecke.EntireRegularizations
public import DedekindZetaZeroFree.LFunctions.Hecke.ReciprocalGammaFactorStripBounds

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField

theorem heckeNonprincipalRegularization_quadratic_strip_growth
    (Q : ℝ) (hQ : 0 < Q) (r : ℕ) (a b : ℝ) (hab : a ≤ b)
    (Λ : ℂ → ℂ)
    (hΛ : ∃ C : ℝ, ∀ s : ℂ, ‖Λ s‖ ≤ C * Real.exp (‖s‖ ^ 2)) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (s : ℂ), a ≤ s.re → s.re ≤ b →
        ‖(Q : ℂ) ^ (-s / 2) * ((Complex.Gammaℂ s)⁻¹) ^ r * Λ s‖ ≤
          M * Real.exp (B * (1 + |s.im|) ^ 2) := by
  obtain ⟨C, hC⟩ := hΛ
  obtain ⟨GC, _hGCpos, hGC⟩ := gammaC_inverse_strip_exp_bound a b hab
  set m : ℝ := max |a| |b| with hm
  have hm0 : 0 ≤ m := by
    rw [hm]; exact le_trans (abs_nonneg a) (le_max_left _ _)
  set Qb : ℝ := max (Q ^ (-a / 2)) (Q ^ (-b / 2)) with hQb
  have hQb0 : 0 ≤ Qb := by
    rw [hQb]; exact le_trans (Real.rpow_nonneg hQ.le _) (le_max_left _ _)
  refine ⟨Qb * GC ^ r * max C 1, 2 * (m ^ 2 + 1) + r * Real.pi, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro s ha hb

    have hQnorm : ‖(Q : ℂ) ^ (-s / 2)‖ ≤ Qb := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ]
      have hre : (-s / 2).re = -s.re / 2 := by simp
      rw [hre, hQb]
      rcases le_or_gt 1 Q with h1 | h1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (le_max_left _ _)
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hQ h1.le (by linarith))
          (le_max_right _ _)

    have hGnorm : ‖((Complex.Gammaℂ s)⁻¹) ^ r‖ ≤
        GC ^ r * Real.exp (r * Real.pi * |s.im|) := by
      rw [norm_pow]
      calc ‖(Complex.Gammaℂ s)⁻¹‖ ^ r ≤ (GC * Real.exp (Real.pi * |s.im|)) ^ r :=
            pow_le_pow_left₀ (norm_nonneg _) (hGC s ⟨ha, hb⟩) r
        _ = GC ^ r * Real.exp (Real.pi * |s.im|) ^ r := by rw [mul_pow]
        _ = GC ^ r * Real.exp (r * (Real.pi * |s.im|)) := by
              rw [Real.exp_nat_mul]
        _ = GC ^ r * Real.exp (r * Real.pi * |s.im|) := by ring_nf
    have hLam : ‖Λ s‖ ≤ max C 1 * Real.exp (‖s‖ ^ 2) :=
      (hC s).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

    have hre_le : |s.re| ≤ m := by
      rw [hm]
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 : -|a| ≤ s.re := le_trans (neg_abs_le a) ha
        have h2 : -(max |a| |b|) ≤ -|a| := neg_le_neg (le_max_left _ _)
        linarith
      · exact le_trans hb (le_trans (le_abs_self b) (le_max_right _ _))

    have hsq : ‖s‖ ^ 2 ≤ 2 * (m ^ 2 + 1) * (1 + |s.im|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have h1 : s.re ^ 2 ≤ m ^ 2 := by
        rw [← sq_abs s.re]
        exact pow_le_pow_left₀ (abs_nonneg _) hre_le 2
      have h2 : s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by
        rw [← sq_abs s.im]
        exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg s.im]) 2
      have h3 : (1 : ℝ) ≤ (1 + |s.im|) ^ 2 := by
        nlinarith [abs_nonneg s.im]
      nlinarith [h1, h2, h3, hm0]

    have hA : r * Real.pi * |s.im| ≤ r * Real.pi * (1 + |s.im|) ^ 2 := by
      have h : |s.im| ≤ (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    calc ‖(Q : ℂ) ^ (-s / 2) * ((Complex.Gammaℂ s)⁻¹) ^ r * Λ s‖
        = ‖(Q : ℂ) ^ (-s / 2)‖ * ‖((Complex.Gammaℂ s)⁻¹) ^ r‖ * ‖Λ s‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ Qb * (GC ^ r * Real.exp (r * Real.pi * |s.im|)) *
            (max C 1 * Real.exp (‖s‖ ^ 2)) := by
          gcongr
      _ = Qb * GC ^ r * max C 1 *
            Real.exp (r * Real.pi * |s.im| + ‖s‖ ^ 2) := by
          rw [Real.exp_add]; ring
      _ ≤ Qb * GC ^ r * max C 1 *
            Real.exp ((2 * (m ^ 2 + 1) + r * Real.pi) * (1 + |s.im|) ^ 2) := by
          gcongr
          nlinarith [hA, hsq]

theorem heckePrincipalRegularization_quadratic_strip_growth
    (Q : ℝ) (hQ : 0 < Q) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (E : ℂ → ℂ)
    (hE : ∃ C : ℝ, ∀ s : ℂ, ‖E s‖ ≤ C * Real.exp (‖s‖ ^ 2)) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (s : ℂ), a ≤ s.re → s.re ≤ b →
        ‖(Q : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
            (Complex.Gammaℂ (s + 1))⁻¹ * ((Complex.Gammaℂ s)⁻¹) ^ (r - 1) * E s‖ ≤
          M * Real.exp (B * (1 + |s.im|) ^ 2) := by
  obtain ⟨C, hC⟩ := hE
  obtain ⟨GC, _hGCpos, hGC⟩ := gammaC_inverse_strip_exp_bound a b hab
  obtain ⟨GC1, _hGC1pos, hGC1⟩ :=
    gammaC_inverse_strip_exp_bound (a + 1) (b + 1) (by linarith)
  set m : ℝ := max |a| |b| with hm
  have hm0 : 0 ≤ m := by
    rw [hm]; exact le_trans (abs_nonneg a) (le_max_left _ _)
  set Qb : ℝ := max (Q ^ (-a / 2)) (Q ^ (-b / 2)) with hQb
  have hQb0 : 0 ≤ Qb := by
    rw [hQb]; exact le_trans (Real.rpow_nonneg hQ.le _) (le_max_left _ _)
  refine ⟨Qb * (2 * Real.pi)⁻¹ * GC1 * GC ^ (r - 1) * max C 1,
    2 * (m ^ 2 + 1) + r * Real.pi, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro s ha hb
    set eA : ℝ := Real.exp (Real.pi * |s.im|) with heA
    set eB : ℝ := Real.exp (((r - 1 : ℕ) : ℝ) * Real.pi * |s.im|) with heB
    set eD : ℝ := Real.exp (‖s‖ ^ 2) with heD
    set eT : ℝ := Real.exp ((2 * (m ^ 2 + 1) + r * Real.pi) * (1 + |s.im|) ^ 2) with heT
    have hQnorm : ‖(Q : ℂ) ^ (-s / 2)‖ ≤ Qb := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ]
      have hre : (-s / 2).re = -s.re / 2 := by simp
      rw [hre, hQb]
      rcases le_or_gt 1 Q with h1 | h1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (le_max_left _ _)
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hQ h1.le (by linarith))
          (le_max_right _ _)
    have hconst : ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

    have hG1norm : ‖(Complex.Gammaℂ (s + 1))⁻¹‖ ≤ GC1 * eA := by
      have hs1 : a + 1 ≤ (s + 1).re ∧ (s + 1).re ≤ b + 1 := by
        simp only [Complex.add_re, Complex.one_re]
        constructor <;> linarith
      have h := hGC1 (s + 1) hs1
      rw [heA]
      simpa using h
    have hGnorm : ‖((Complex.Gammaℂ s)⁻¹) ^ (r - 1)‖ ≤ GC ^ (r - 1) * eB := by
      rw [norm_pow, heB]
      calc ‖(Complex.Gammaℂ s)⁻¹‖ ^ (r - 1) ≤
            (GC * Real.exp (Real.pi * |s.im|)) ^ (r - 1) :=
            pow_le_pow_left₀ (norm_nonneg _) (hGC s ⟨ha, hb⟩) (r - 1)
        _ = GC ^ (r - 1) * Real.exp (Real.pi * |s.im|) ^ (r - 1) := by rw [mul_pow]
        _ = GC ^ (r - 1) * Real.exp (((r - 1 : ℕ) : ℝ) * (Real.pi * |s.im|)) := by
              rw [Real.exp_nat_mul]
        _ = GC ^ (r - 1) * Real.exp (((r - 1 : ℕ) : ℝ) * Real.pi * |s.im|) := by ring_nf
    have hLam : ‖E s‖ ≤ max C 1 * eD := by
      rw [heD]
      exact (hC s).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hre_le : |s.re| ≤ m := by
      rw [hm]
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 : -|a| ≤ s.re := le_trans (neg_abs_le a) ha
        have h2 : -(max |a| |b|) ≤ -|a| := neg_le_neg (le_max_left _ _)
        linarith
      · exact le_trans hb (le_trans (le_abs_self b) (le_max_right _ _))
    have hsq : ‖s‖ ^ 2 ≤ 2 * (m ^ 2 + 1) * (1 + |s.im|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have h1 : s.re ^ 2 ≤ m ^ 2 := by
        rw [← sq_abs s.re]
        exact pow_le_pow_left₀ (abs_nonneg _) hre_le 2
      have h2 : s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by
        rw [← sq_abs s.im]
        exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg s.im]) 2
      have h3 : (1 : ℝ) ≤ (1 + |s.im|) ^ 2 := by
        nlinarith [abs_nonneg s.im]
      nlinarith [h1, h2, h3, hm0]
    have hA : r * Real.pi * |s.im| ≤ r * Real.pi * (1 + |s.im|) ^ 2 := by
      have h : |s.im| ≤ (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]
      exact mul_le_mul_of_nonneg_left h (by positivity)

    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr]; norm_num
    have hexp : eA * eB * eD ≤ eT := by
      rw [heA, heB, heD, heT, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hcast]
      nlinarith [hA, hsq]
    calc ‖(Q : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
            (Complex.Gammaℂ (s + 1))⁻¹ * ((Complex.Gammaℂ s)⁻¹) ^ (r - 1) * E s‖
        = ‖(Q : ℂ) ^ (-s / 2)‖ * ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ *
            ‖(Complex.Gammaℂ (s + 1))⁻¹‖ * ‖((Complex.Gammaℂ s)⁻¹) ^ (r - 1)‖ * ‖E s‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
      _ ≤ Qb * (2 * Real.pi)⁻¹ * (GC1 * eA) * (GC ^ (r - 1) * eB) * (max C 1 * eD) := by
          rw [hconst]
          gcongr
      _ = (Qb * (2 * Real.pi)⁻¹ * GC1 * GC ^ (r - 1) * max C 1) * (eA * eB * eD) := by
          ring
      _ ≤ (Qb * (2 * Real.pi)⁻¹ * GC1 * GC ^ (r - 1) * max C 1) * eT :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (Qb * (2 * Real.pi)⁻¹ * GC1 * GC ^ (r - 1) * max C 1) *
            Real.exp ((2 * (m ^ 2 + 1) + r * Real.pi) * (1 + |s.im|) ^ 2) := by
          rw [heT]

theorem nonprincipalHeckeEntireContinuation_quadratic_strip_growth
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (D : NonprincipalRayHeckeData F 𝔪 η) (a b : ℝ) (hab : a ≤ b) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (s : ℂ), a ≤ s.re → s.re ≤ b →
        ‖nonprincipalHeckeEntireContinuation F 𝔪 η D s‖ ≤
          M * Real.exp (B * (1 + |s.im|) ^ 2) := by
  have hQ : 0 < heckeConductorScale F 𝔪 :=
    lt_of_lt_of_le zero_lt_one (one_le_heckeConductorScale F 𝔪 hm)
  have hΛ : ∃ C : ℝ, ∀ s : ℂ, ‖D.Λ s‖ ≤ C * Real.exp (‖s‖ ^ 2) := by
    obtain ⟨C, hC⟩ := D.order_bound 1 (by norm_num)
    refine ⟨C, fun s => ?_⟩
    have h := hC s
    rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h
  simpa only [nonprincipalHeckeEntireContinuation, heckeReciprocalCompletionFactor]
    using heckeNonprincipalRegularization_quadratic_strip_growth (heckeConductorScale F 𝔪) hQ
      (NumberField.InfinitePlace.nrComplexPlaces F) a b hab D.Λ hΛ

theorem principalHeckeEntireRegularization_quadratic_strip_growth
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (D : PrincipalRayHeckeData F 𝔪 η) (a b : ℝ) (hab : a ≤ b) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (s : ℂ), a ≤ s.re → s.re ≤ b →
        ‖principalHeckeEntireRegularization F 𝔪 η D s‖ ≤
          M * Real.exp (B * (1 + |s.im|) ^ 2) := by
  have hQ : 0 < heckeConductorScale F 𝔪 :=
    lt_of_lt_of_le zero_lt_one (one_le_heckeConductorScale F 𝔪 hm)
  have hr : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces F :=
    one_le_nrComplexPlaces_of_totallyComplex F hF
  have hE : ∃ C : ℝ, ∀ s : ℂ, ‖D.E s‖ ≤ C * Real.exp (‖s‖ ^ 2) := by
    obtain ⟨C, hC⟩ := D.order_bound 1 (by norm_num)
    refine ⟨C, fun s => ?_⟩
    have h := hC s
    rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h
  simpa only [principalHeckeEntireRegularization]
    using heckePrincipalRegularization_quadratic_strip_growth (heckeConductorScale F 𝔪) hQ
      (NumberField.InfinitePlace.nrComplexPlaces F) hr a b hab D.E hE

end
end DedekindZetaZeroFree
