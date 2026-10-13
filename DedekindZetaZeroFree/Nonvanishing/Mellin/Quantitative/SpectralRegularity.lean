module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralFunction

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.SpectralData

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.Spectral

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem G_eq_recipe (s : ℂ) : G D s = D.recipe.G s := rfl

theorem G_differentiableOn : DifferentiableOn ℂ (G D) {s : ℂ | 1 < s.re} :=
  (PrincipalMellin.actual_principal_spectral_properties S η D.recipe).2.2.1

theorem G_bound (A B : ℝ) (hA : 1 < A) (hAB : A ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, A ≤ σ → σ ≤ B →
      ‖G D ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ :=
    (PrincipalMellin.actual_principal_spectral_properties S η D.recipe).2.2.2.1 A B hA hAB
  refine ⟨C + 1, by linarith, fun σ t h1 h2 => ?_⟩
  have h := hb σ ⟨h1, h2⟩ t
  have hpos : 0 < 1 + t ^ 2 := by positivity
  exact h.trans (div_le_div_of_nonneg_right (by linarith) hpos.le)

theorem G_line_continuous : Continuous (fun t : ℝ => G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hc : ContinuousOn (G D) {s : ℂ | 1 < s.re} := (G_differentiableOn D).continuousOn
  refine hc.comp_continuous (by fun_prop) (fun t => ?_)
  show 1 < ((((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
  first | (simp; norm_num) | simp | norm_num

theorem G_line_bound : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    ‖G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := G_bound D 2 2 (by norm_num) le_rfl
  exact ⟨C, hC, fun t => hb 2 t le_rfl le_rfl⟩

theorem norm_rpow_line (Z : ℝ) (hZ : 0 < Z) (t : ℝ) :
    ‖(Z : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 61 / 100)‖ = Z ^ (139 / 100 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  congr 1
  first | (simp; norm_num) | simp | norm_num

theorem integrable_bound : MeasureTheory.Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) := by
  simpa using integrable_inv_one_add_sq

theorem f_integrable (Z : ℝ) (hZ : 0 < Z) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (Z : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 61 / 100) *
        G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := G_line_bound D
  have hcont : Continuous (fun t : ℝ =>
      (Z : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 61 / 100) *
        G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    refine Continuous.mul ?_ (G_line_continuous D)
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hZ.ne'))
  refine ((integrable_bound.const_mul (Z ^ (139 / 100 : ℝ) * C)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_))
  rw [norm_mul, norm_rpow_line Z hZ t]
  calc _ ≤ Z ^ (139 / 100 : ℝ) * (C / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left (hb t) (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem f_continuousOn : ContinuousOn (f D) (Set.Ioi 0) := by
  intro Z0 hZ0
  have hZ0 : 0 < Z0 := hZ0
  apply ContinuousAt.continuousWithinAt
  obtain ⟨C, hC, hb⟩ := G_line_bound D
  have hnhds : Set.Ioo (Z0 / 2) (2 * Z0) ∈ nhds Z0 :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hcongr : f D =ᶠ[nhds Z0] fun Z : ℝ => (2 * (Real.pi : ℂ))⁻¹ *
      ∫ t : ℝ, (Z : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 61 / 100) *
        G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    filter_upwards [Ioi_mem_nhds hZ0] with Z hZ
    have hZ : 0 < Z := hZ
    simp [f, hZ, comparisonVerticalIntegral]
  refine ContinuousAt.congr ?_ hcongr.symm
  refine ContinuousAt.const_mul ?_ _
  refine MeasureTheory.continuousAt_of_dominated (bound := fun t : ℝ =>
    (2 * Z0) ^ (139 / 100 : ℝ) * C * (1 + t ^ 2)⁻¹) ?_ ?_ ?_ ?_
  · filter_upwards [Ioi_mem_nhds hZ0] with Z hZ
    have hZ : 0 < Z := hZ
    exact (f_integrable D Z hZ).aestronglyMeasurable
  · filter_upwards [hnhds] with Z hZ
    have hZ' : 0 < Z := by linarith [hZ.1]
    refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, norm_rpow_line Z hZ' t]
    calc _ ≤ (2 * Z0) ^ (139 / 100 : ℝ) * (C / (1 + t ^ 2)) :=
          mul_le_mul (Real.rpow_le_rpow hZ'.le hZ.2.le (by norm_num)) (hb t)
            (norm_nonneg _) (by positivity)
      _ = _ := by rw [div_eq_mul_inv]; ring
  · exact integrable_bound.const_mul _
  · refine Filter.Eventually.of_forall fun t => ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    exact ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
      (Complex.ofReal_mem_slitPlane.mpr hZ0)

theorem rpow_mul_f (Z : ℝ) (hZ : 0 < Z) :
    (Z : ℂ) ^ (61 / 100 : ℂ) * f D Z =
      comparisonVerticalIntegral 2 (fun s => (Z : ℂ) ^ s * G D s) := by
  have hZ' : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  simp only [f, hZ, if_true, comparisonVerticalIntegral]
  rw [mul_left_comm, ← MeasureTheory.integral_const_mul]
  congr 2
  funext t
  rw [← mul_assoc, ← Complex.cpow_add _ _ hZ']
  congr 2
  ring

theorem numerator_differentiableOn :
    DifferentiableOn ℂ (fun s : ℂ => Complex.exp ((s - 5 / 6) ^ 2) * H D s)
      {s : ℂ | 31 / 32 < s.re} := by
  have hH : DifferentiableOn ℂ (fun s : ℂ => D.recipe.H s) {s : ℂ | (2 / 3 : ℝ) < s.re} :=
    PrincipalMellin.actual_principal_H_differentiable D.recipe
  have hsub : {s : ℂ | 31 / 32 < s.re} ⊆ {s : ℂ | (2 / 3 : ℝ) < s.re} := fun s hs => by
    simp only [Set.mem_setOf_eq] at hs ⊢
    linarith
  have hexp : DifferentiableOn ℂ (fun s : ℂ => Complex.exp ((s - 5 / 6) ^ 2))
      {s : ℂ | 31 / 32 < s.re} :=
    (by fun_prop : Differentiable ℂ (fun s : ℂ => Complex.exp ((s - 5 / 6) ^ 2))).differentiableOn
  exact hexp.mul (hH.mono hsub)

theorem numerator_ne_zero (s : ℂ) (hs : 31 / 32 < s.re) :
    Complex.exp ((s - 5 / 6) ^ 2) * H D s ≠ 0 := by
  have h : D.recipe.H s ≠ 0 :=
    PrincipalMellin.actual_principal_H_ne_zero D.recipe s (by linarith)
  exact mul_ne_zero (Complex.exp_ne_zero _) h

end

end DedekindZetaZeroFree.Quantitative.SpectralData
