module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelGrowth

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowRectangleDeformation

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight DedekindZetaZeroFree.Quantitative.RowKernelGrowth
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem rect_cauchy (f : ℂ → ℂ) (a b T : ℝ)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-T) T)) :
    (∫ σ in a..b, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ σ in a..b, f ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t in (-T)..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I) (by simpa using hf)
  simpa using h

theorem row_pointwise_integrable (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U → ∀ Z : ℝ, 0 < Z →
        ∀ ξ : ℂ, Scales.goodLine ≤ ξ.re → ξ.re ≤ Scales.rightLine →
          (|ξ.im| ≤ U ^ ρ ∨ ξ.re = Scales.rightLine) →
            (∀ w : ℂ, w.re = Scales.wLine →
              Integrable (fun τ : ℝ =>
                K D u ξ w ((Scales.zLine : ℂ) + (τ : ℂ) * Complex.I) Z)) ∧
            Integrable (fun τ : ℝ =>
              comparisonVerticalIntegral Scales.zLine
                (fun z => K D u ξ ((Scales.wLine : ℂ) + (τ : ℂ) * Complex.I) z Z)) := by
  obtain ⟨C1, hC1, U1, hU1, h1⟩ := kernel_majorant_rect D A_F ρ hA hconv hρ 1 one_pos
  obtain ⟨C2, hC2, h2⟩ := kernel_majorant_right D A_F hconv 1 one_pos
  refine ⟨max U1 2, le_max_right _ _, ?_⟩
  intro U hU u hu hq1 hq2 hex Z hZ ξ hxg hx1 hcase
  have hUa : U1 ≤ U := le_trans (le_max_left _ _) hU
  have hUb : 2 ≤ U := le_trans (le_max_right _ _) hU
  have hU0 : 0 < U := by linarith
  have hq0 : 0 < D.q u := by linarith
  have hent := RowAnalyticContinuation.exists_entire_numerator D u hu
  have hpad : (0 : ℝ) < EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  have hρU : 0 ≤ U ^ ρ := Real.rpow_nonneg hU0.le ρ

  have hmain : ∃ Cf : ℝ, 0 ≤ Cf ∧ D.Llam u ξ ≠ 0 ∧ ∀ p : ℝ × ℝ,
      ‖K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
        Cf * (WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
          (2 + |p.2|) ^ A_F) := by
    rcases hcase with him | hre
    · refine ⟨C1 * Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
          Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + 1 - Scales.zLine), by positivity,
        RowAnalyticContinuation.Llam_ne_zero_central D ρ U hU0.le u hu hq1 hq2 hex ξ hxg him, ?_⟩
      intro p
      exact h1 U hUa u hu hent hq1 hq2 hex ξ Z p hZ hxg
        (him.trans (by linarith))
    · refine ⟨C2 * Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
          Scales.yExponent * (Scales.wLine - 1)) * U ^ ((11 / 25 : ℝ) + 1 - Scales.zLine), by positivity,
        RightHeckeBounds.Llam_ne_zero_of_one_lt D u ξ (by rw [hre, Scales.rightLine_eq]; norm_num), ?_⟩
      intro p
      exact h2 U hUb u hu hent hq1 hq2 ξ Z p hZ hre
  obtain ⟨Cf, hCf, hLl, hbd0⟩ := hmain
  have hbd : ∀ p : ℝ × ℝ, ‖K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
      Cf * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
        (2 + |p.1| + |p.2| + |ξ.im|) ^ A_F := by
    intro p
    refine (hbd0 p).trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCf (norm_nonneg _))
    exact Real.rpow_le_rpow (by positivity)
      (by linarith [abs_nonneg p.1, abs_nonneg ξ.im]) hA
  have hcont : Continuous (fun p : ℝ × ℝ => K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
      ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) := by
    have := RowAnalyticContinuation.K_continuous_heights D u hu hq0 Z hZ ξ
      (by linarith) hLl
    have hsw : Continuous (Prod.swap : ℝ × ℝ → ℝ × ℝ) := continuous_swap
    exact Continuous.comp (g := fun q : ℝ × ℝ => K D u ξ ((Scales.wLine : ℂ) + (q.1 : ℂ) * Complex.I)
      ((Scales.zLine : ℂ) + (q.2 : ℂ) * Complex.I) Z) (f := Prod.swap) this hsw
  have hz0 : (0 : ℝ) < Scales.zLine := by unfold Scales.zLine; norm_num
  have hxle : Scales.goodLine ≤ Scales.rightLine := by
    unfold Scales.goodLine Scales.rightLine Scales.contourOffset; norm_num
  have hx1' : ξ.re ≤ Scales.rightLine := hx1
  refine ⟨fun w hw => ?_, ?_⟩
  · have hsec := KernelWeightIntegration.section_integrable D Scales.zLine Scales.zLine Scales.wLine
      Scales.wLine Scales.goodLine Scales.rightLine hz0 le_rfl le_rfl hxle A_F hA ξ hxg hx1' Scales.zLine
      Scales.wLine le_rfl le_rfl le_rfl le_rfl Cf _ hcont hbd w.im
    have hw' : w = (Scales.wLine : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hw]
    rw [hw']
    exact hsec
  · obtain ⟨Cw, -, hCw⟩ := KernelWeightIntegration.nested_integral_bound D Scales.zLine Scales.zLine
      Scales.wLine Scales.wLine Scales.goodLine Scales.rightLine hz0 le_rfl le_rfl hxle 2 A_F (by norm_num) hA
    exact (hCw ξ hxg hx1' Scales.zLine Scales.wLine le_rfl le_rfl le_rfl le_rfl Cf hCf
      (fun w z => K D u ξ w z Z) hcont.aestronglyMeasurable hbd).2.2.1

theorem row_right_integrable (A_F : ℝ) (hconv : ConvexityExponent D A_F) :
    ∀ U : ℝ, 2 ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 → U ≤ D.q u → D.q u < 2 * U →
      ∀ Z : ℝ, 0 < Z → Integrable (fun t : ℝ =>
        wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) := by
  intro U hU u hu hq1 hq2 Z hZ
  exact wzIntegral_integrable_right D A_F hconv U hU u hu
    (RowAnalyticContinuation.exists_entire_numerator D u hu) hq1 hq2 Z hZ

theorem rect_decomp (f : ℂ → ℂ) (a b T : ℝ) (hab : a ≤ b) (hT : 0 ≤ T)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-T) T))
    (hint : Integrable (fun t : ℝ => f ((b : ℂ) + (t : ℂ) * Complex.I))) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      (2 * (Real.pi : ℂ))⁻¹ * (∫ t in Set.Icc (-T) T, f ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ σ in a..b, f ((σ : ℂ) + ((1 * T : ℝ) : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ σ in b..a, f ((σ : ℂ) + (((-1) * T : ℝ) : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ))⁻¹ *
        (∫ t in {t : ℝ | T < |t|}, f ((b : ℂ) + (t : ℂ) * Complex.I)) := by
  have hC := rect_cauchy f a b T hf
  have hsplit : ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I) =
      (∫ t in Set.Icc (-T) T, f ((b : ℂ) + (t : ℂ) * Complex.I)) +
        ∫ t in {t : ℝ | T < |t|}, f ((b : ℂ) + (t : ℂ) * Complex.I) := by
    have hc : {t : ℝ | T < |t|} = (Set.Icc (-T) T)ᶜ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
      constructor
      · intro h
        rcases lt_abs.mp h with h | h
        · right; exact h
        · left; linarith
      · rintro (h | h)
        · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
        · exact lt_of_lt_of_le h (le_abs_self t)
    rw [hc]
    exact (integral_add_compl measurableSet_Icc hint).symm
  have hIcc : ∀ g : ℝ → ℂ, ∫ t in Set.Icc (-T) T, g t = ∫ t in (-T)..T, g t := by
    intro g
    rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hsplit, hIcc, hIcc, intervalIntegral.integral_symm a b]
  simp only [one_mul, neg_mul, Complex.ofReal_neg] at hC ⊢
  have hRL : Complex.I * (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.I * (∫ t in (-T)..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) +
        ((∫ σ in a..b, f ((σ : ℂ) + (T : ℂ) * Complex.I)) -
          ∫ σ in a..b, f ((σ : ℂ) + -((T : ℂ) * Complex.I))) := by
    linear_combination hC
  have hR : (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t in (-T)..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) +
        Complex.I⁻¹ * ((∫ σ in a..b, f ((σ : ℂ) + (T : ℂ) * Complex.I)) -
          ∫ σ in a..b, f ((σ : ℂ) + -((T : ℂ) * Complex.I))) := by
    rw [← inv_mul_cancel_left₀ hI (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * Complex.I)), hRL,
      mul_add, inv_mul_cancel_left₀ hI]
  rw [hR]
  ring

theorem row_rectangle_deformation_decomp (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U → ∀ Z : ℝ, 0 < Z →
        comparisonVerticalIntegral Scales.rightLine
            (fun ξ => wzIntegral D u ξ Scales.wLine Scales.zLine Z) =
          (2 * (Real.pi : ℂ))⁻¹ *
              (∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
                wzIntegral D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (∫ σ in Scales.goodLine..Scales.rightLine,
                wzIntegral D u ((σ : ℂ) + ((1 * U ^ ρ : ℝ) : ℂ) * Complex.I)
                  Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (∫ σ in Scales.rightLine..Scales.goodLine,
                wzIntegral D u ((σ : ℂ) + (((-1) * U ^ ρ : ℝ) : ℂ) * Complex.I)
                  Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ))⁻¹ *
              (∫ t in {t : ℝ | U ^ ρ < |t|},
                wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) := by
  refine ⟨2, le_rfl, ?_⟩
  intro U hU u hu hq1 hq2 hex Z hZ
  have hU0 : 0 ≤ U := by linarith
  have hT : 0 ≤ U ^ ρ := Real.rpow_nonneg hU0 ρ
  have hent := RowAnalyticContinuation.exists_entire_numerator D u hu
  obtain ⟨-, hdiff⟩ := RowKernelGrowth.wzIntegral_differentiableOn D A_F hconv u hu
    (by linarith) hent Z hZ
  have hxg : Scales.goodLine ≤ Scales.rightLine := by
    unfold Scales.goodLine Scales.rightLine Scales.contourOffset; norm_num
  have hpad : (0 : ℝ) < EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  have hrect : DifferentiableOn ℂ (fun ξ => wzIntegral D u ξ Scales.wLine Scales.zLine Z)
      (Set.uIcc Scales.goodLine Scales.rightLine ×ℂ Set.uIcc (-(U ^ ρ)) (U ^ ρ)) := by
    refine hdiff.mono ?_
    intro ξ hξ
    rw [Set.uIcc_of_le hxg, Set.uIcc_of_le (by linarith)] at hξ
    obtain ⟨h1, h2⟩ := hξ
    have a1 : Scales.goodLine ≤ ξ.re := h1.1
    have a2 : -(U ^ ρ) ≤ ξ.im := h2.1
    have a3 : ξ.im ≤ U ^ ρ := h2.2
    refine ⟨by linarith, ?_⟩
    exact RowAnalyticContinuation.Llam_ne_zero_central D ρ U hU0 u hu hq1 hq2 hex ξ a1
      (abs_le.mpr ⟨a2, a3⟩)
  exact rect_decomp (fun ξ => wzIntegral D u ξ Scales.wLine Scales.zLine Z) Scales.goodLine Scales.rightLine
    (U ^ ρ) hxg hT hrect (row_right_integrable D A_F hconv U hU u hu hq1 hq2 Z hZ)

theorem row_rectangle_deformation (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ u : D.Row, u.toFrequency.u ≠ 1 →
      U ≤ D.q u → D.q u < 2 * U → u ∉ exceptionalSet D ρ U → ∀ Z : ℝ, 0 < Z →
        comparisonVerticalIntegral Scales.rightLine
            (fun ξ => wzIntegral D u ξ Scales.wLine Scales.zLine Z) =
          (2 * (Real.pi : ℂ))⁻¹ *
              (∫ t in Set.Icc (-(U ^ ρ)) (U ^ ρ),
                wzIntegral D u ((Scales.goodLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (∫ σ in Scales.goodLine..Scales.rightLine,
                wzIntegral D u ((σ : ℂ) + ((1 * U ^ ρ : ℝ) : ℂ) * Complex.I)
                  Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (∫ σ in Scales.rightLine..Scales.goodLine,
                wzIntegral D u ((σ : ℂ) + (((-1) * U ^ ρ : ℝ) : ℂ) * Complex.I)
                  Scales.wLine Scales.zLine Z) +
            (2 * (Real.pi : ℂ))⁻¹ *
              (∫ t in {t : ℝ | U ^ ρ < |t|},
                wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z) := by
  exact row_rectangle_deformation_decomp D A_F ρ hA hconv hρ

end

end DedekindZetaZeroFree.Quantitative.RowRectangleDeformation
