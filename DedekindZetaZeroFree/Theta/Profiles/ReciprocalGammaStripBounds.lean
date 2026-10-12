module

public import DedekindZetaZeroFree.Analysis.Gamma.ReflectionAndReciprocalStripBounds

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean.
-/

namespace DedekindZetaZeroFree

noncomputable section

def reciprocalGamma (z : ℂ) : ℂ := (Complex.Gamma z)⁻¹

theorem reciprocalGamma_differentiable : Differentiable ℂ reciprocalGamma := by
  exact Complex.differentiable_one_div_Gamma

@[simp] theorem reciprocalGamma_neg_nat (n : ℕ) : reciprocalGamma (-(n : ℂ)) = 0 := by
  simp [reciprocalGamma, Complex.Gamma_neg_nat_eq_zero]

theorem reciprocalGamma_strip_exp_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖reciprocalGamma z‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨C, hC, hbound⟩ := GammaBounds.inverse_Gamma_strip_exp_bound_complex a b
  exact ⟨C, hC, fun z ha hb => hbound z ⟨ha, hb⟩⟩

def thetaProfileReciprocalMellinFactor (C₀ A₀ : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  (C₀ : ℂ)⁻¹ * (A₀ : ℂ) ^ (-s) *
    (reciprocalGamma (s + 5 / 6) * reciprocalGamma (s + 7 / 6)) ^ r

theorem thetaProfileReciprocalMellinFactor_differentiable
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r) :
    Differentiable ℂ (thetaProfileReciprocalMellinFactor C₀ A₀ r) := by
  have hp : Differentiable ℂ (fun s : ℂ => (A₀ : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hA₀.ne'))
  have h₁ : Differentiable ℂ (fun s : ℂ => reciprocalGamma (s + 5 / 6)) :=
    reciprocalGamma_differentiable.comp (differentiable_id.add_const _)
  have h₂ : Differentiable ℂ (fun s : ℂ => reciprocalGamma (s + 7 / 6)) :=
    reciprocalGamma_differentiable.comp (differentiable_id.add_const _)
  exact (hp.const_mul _).mul ((h₁.mul h₂).pow r)

theorem thetaProfileReciprocalMellinFactor_strip_exp_bound
    (C₀ A₀ : ℝ) (r : ℕ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖thetaProfileReciprocalMellinFactor C₀ A₀ r s‖ ≤
        C * Real.exp (2 * Real.pi * (r : ℝ) * |s.im|) := by
  obtain ⟨C₁, hC₁, h₁⟩ := reciprocalGamma_strip_exp_bound
    (a + 5 / 6) (b + 5 / 6) (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := reciprocalGamma_strip_exp_bound
    (a + 7 / 6) (b + 7 / 6) (by linarith)
  let D : ℝ := Real.exp (|Real.log A₀| * max |a| |b|)
  have hD : 0 < D := Real.exp_pos _
  have hnorm : 0 < ‖(C₀ : ℂ)⁻¹‖ :=
    norm_pos_iff.mpr (inv_ne_zero (Complex.ofReal_ne_zero.mpr hC₀.ne'))
  refine ⟨‖(C₀ : ℂ)⁻¹‖ * D * (C₁ * C₂) ^ r, by positivity, ?_⟩
  intro s ha hb
  have hp : ‖(A₀ : ℂ) ^ (-s)‖ ≤ D := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA₀, Real.rpow_def_of_pos hA₀]
    apply Real.exp_le_exp.mpr
    calc
      Real.log A₀ * (-s).re ≤ |Real.log A₀ * (-s).re| := le_abs_self _
      _ = |Real.log A₀| * |s.re| := by simp [abs_mul]
      _ ≤ |Real.log A₀| * max |a| |b| :=
        mul_le_mul_of_nonneg_left (abs_le_max_abs_abs ha hb) (abs_nonneg _)
  have hb₁ := h₁ (s + 5 / 6) (by norm_num; linarith) (by norm_num; linarith)
  have hb₂ := h₂ (s + 7 / 6) (by norm_num; linarith) (by norm_num; linarith)
  norm_num at hb₁ hb₂
  have hpair : ‖reciprocalGamma (s + 5 / 6) * reciprocalGamma (s + 7 / 6)‖ ≤
      (C₁ * C₂) * Real.exp (2 * Real.pi * |s.im|) := by
    rw [norm_mul]
    calc
      _ ≤ (C₁ * Real.exp (Real.pi * |s.im|)) *
          (C₂ * Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul hb₁ hb₂ (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show 2 * Real.pi * |s.im| = Real.pi * |s.im| + Real.pi * |s.im| by ring,
          Real.exp_add]
        ring
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hpair r
  rw [mul_pow, ← Real.exp_nat_mul] at hpow
  have he : (r : ℝ) * (2 * Real.pi * |s.im|) =
      2 * Real.pi * (r : ℝ) * |s.im| := by ring
  rw [he] at hpow
  simp only [thetaProfileReciprocalMellinFactor, norm_mul, norm_pow]
  rw [norm_mul] at hpow
  calc
    _ ≤ (‖(C₀ : ℂ)⁻¹‖ * D) *
        ((C₁ * C₂) ^ r * Real.exp (2 * Real.pi * (r : ℝ) * |s.im|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) hpow
        (by positivity) (by positivity)
    _ = _ := by ring

end

end DedekindZetaZeroFree
