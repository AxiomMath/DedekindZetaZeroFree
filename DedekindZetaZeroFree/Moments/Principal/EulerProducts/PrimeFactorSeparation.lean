module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.Definitions

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

open LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private lemma separation_good_data (C : A.GeneralArithmeticContext σ η hS)
    (U : Frequency C) (p : ExteriorPrime A) (hp : (U.j p).val = 0) :
    U.u = U.unitPart p ∧
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) ∧
      (U.theta p).val = chi (σ := σ) p
        (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
  have hu : U.u = U.unitPart p := by
    simpa [hp] using (U.unitPart_spec p).1
  refine ⟨hu, ?_, ?_⟩
  · rw [hu]
    exact (U.unitPart_spec p).2
  · simp only [Frequency.theta, hu]

private lemma separation_qPower_norm_lt_one (p : ExteriorPrime A) (s : ℂ)
    (hs : s.re < 0) : ‖qPower p s‖ < 1 := by
  have hQ : 1 < Q p := by
    change 1 < (Ideal.absNorm p.val.asIdeal : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val
  have hn : ‖qPower p s‖ = Real.exp (s.re * Real.log (Q p)) := by
    simp [qPower, Complex.norm_exp]
  rw [hn, Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos hs (Real.log_pos hQ)

private lemma separation_sub_ne_zero {a : ℂ} (ha : ‖a‖ < 1) : 1 - a ≠ 0 := by
  intro h
  have he : a = 1 := (sub_eq_zero.mp h).symm
  simpa [he] using ha

private lemma separation_D_ne_zero (C : A.GeneralArithmeticContext σ η hS)
    (U : Frequency C) (p : ExteriorPrime A) (ξ : ℂ) (hξ : 4 < ξ.re) :
    1 - D (σ := σ) (η := η) p U.u ξ ≠ 0 := by
  by_cases hp : (U.j p).val = 0
  · have hθ := (separation_good_data C U p hp).2.2
    have hn : ‖chi (σ := σ) p
        (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u)‖ = 1 := by
      rw [← hθ]
      exact (U.theta p).property
    apply separation_sub_ne_zero
    have he := RayUnitary.ray_character_norm_le_one F A.modulus A.modulus_ne_zero η
      p.val.asIdeal
    have hq := separation_qPower_norm_lt_one p (-ξ) (by simp; linarith)
    simp only [D, norm_mul, norm_star, hn, mul_one]
    calc
      ‖η p.val.asIdeal‖ * ‖qPower p (-ξ)‖ ≤ 1 * ‖qPower p (-ξ)‖ :=
        mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ < 1 := by simpa using hq
  · rw [(primitive_variables_zero C U p hp ξ 0).2]
    norm_num

theorem prime_factor_separation (C : A.GeneralArithmeticContext σ η hS)
    (U : Frequency C) (p : ExteriorPrime A)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    (1 - V p z) * (1 - W (σ := σ) p U.u w) *
        f C p (U.j p) (U.theta p) ξ w z =
      (1 - D (σ := σ) (η := η) p U.u ξ) * localFactor C U p ξ w z := by
  by_cases hp : (U.j p).val = 0
  · obtain ⟨_, hu, hθ⟩ := separation_good_data C U p hp
    have hformula := (good_euler_series C p U.u hu (U.theta p) hθ ξ w z hξ hw hz).2
    have hj : U.j p = 0 := Fin.ext hp
    have hf : f C p (U.j p) (U.theta p) ξ w z = goodRational C p U.u ξ w z := by
      rw [hj]
      simpa [goodRational, V, W, D, E, hθ] using hformula
    rw [hf]
    simp only [localFactor, hp, ↓reduceIte, goodFactor]
    exact (mul_div_cancel₀ _ (separation_D_ne_zero C U p ξ hξ)).symm
  · obtain ⟨hW, hD⟩ := primitive_variables_zero C U p hp ξ w
    simp [localFactor, hp, badFactor, hW, hD]

theorem prime_factor_separation_denominators_nonzero
    (C : A.GeneralArithmeticContext σ η hS)
    (U : Frequency C) (p : ExteriorPrime A)
    (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    1 - V p z ≠ 0 ∧ 1 - W (σ := σ) p U.u w ≠ 0 := by
  constructor
  · apply separation_sub_ne_zero
    exact separation_qPower_norm_lt_one p (-6 * z) (by simp; linarith)
  · by_cases hp : (U.j p).val = 0
    · have hθ := (separation_good_data C U p hp).2.2
      apply separation_sub_ne_zero
      simp only [W, norm_mul, ← hθ, (U.theta p).property, one_mul]
      exact separation_qPower_norm_lt_one p (-w) (by simp; linarith)
    · rw [(primitive_variables_zero C U p hp ξ w).1]
      norm_num

end DedekindZetaZeroFree.CorrectionFactors

end
