module

public import DedekindZetaZeroFree.Analysis.GaussianWeightConvolution

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.KernelWeightIntegration

noncomputable section

open DedekindZetaZeroFree MeasureTheory DedekindZetaZeroFree.Quantitative.WeightConvolution

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem one_add_abs_rpow_integrable (B : ℝ) (hB : 1 < B) :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-B)) volume := by
  have := integrable_one_add_norm (μ := volume) (E := ℝ) (r := B) (by norm_num; linarith)
  simpa [Real.norm_eq_abs] using this

theorem joint_integral_bound (a₁ b₁ a₂ b₂ x₀ x₁ : ℝ) (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (hab₂ : a₂ ≤ b₂) (hx : x₀ ≤ x₁) (B k : ℝ) (hB : 0 < B) (hk : 0 ≤ k) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ ξ : ℂ, x₀ ≤ ξ.re → ξ.re ≤ x₁ →
      ∀ v y : ℝ, a₁ ≤ v → v ≤ b₁ → a₂ ≤ y → y ≤ b₂ →
      ∀ (C : ℝ), 0 ≤ C → ∀ Fn : ℝ × ℝ → ℂ, AEStronglyMeasurable Fn volume →
        (∀ p, ‖Fn p‖ ≤ C * weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) →
        Integrable Fn volume ∧
          ‖∫ p, Fn p‖ ≤ C * Cw * (1 + |ξ.im|) ^ (-B) := by
  obtain ⟨C, hC0, hdec⟩ := weight_kernel_decay D a₁ b₁ a₂ b₂ x₀ x₁ ha₁ hab₁ hab₂ hx B k hB hk
  refine ⟨C, hC0, fun ξ hx0 hx1 v y hv1 hv2 hy1 hy2 Cc hCc Fn hmeas hbd => ?_⟩
  obtain ⟨hint, hle⟩ := hdec ξ hx0 hx1 v y hv1 hv2 hy1 hy2
  have hI' : Integrable (fun p : ℝ × ℝ => Cc * (weightModulus D ξ v y p *
      (2 + |p.1| + |p.2| + |ξ.im|) ^ k)) volume := hint.const_mul Cc
  refine ⟨Integrable.mono' hI' hmeas (Filter.Eventually.of_forall fun p => by
    simpa only [mul_assoc] using hbd p), ?_⟩
  calc ‖∫ p, Fn p‖ ≤ ∫ p, ‖Fn p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, Cc * (weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _) hI'
          (Filter.Eventually.of_forall fun p => by simpa only [mul_assoc] using hbd p)
    _ = Cc * ∫ p, weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k :=
        integral_const_mul _ _
    _ ≤ Cc * (C * (1 + |ξ.im|) ^ (-B)) := mul_le_mul_of_nonneg_left hle hCc
    _ = Cc * C * (1 + |ξ.im|) ^ (-B) := by ring

theorem nested_integral_bound (a₁ b₁ a₂ b₂ x₀ x₁ : ℝ) (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (hab₂ : a₂ ≤ b₂) (hx : x₀ ≤ x₁) (B k : ℝ) (hB : 0 < B) (hk : 0 ≤ k) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ ξ : ℂ, x₀ ≤ ξ.re → ξ.re ≤ x₁ →
      ∀ v y : ℝ, a₁ ≤ v → v ≤ b₁ → a₂ ≤ y → y ≤ b₂ →
      ∀ (C : ℝ), 0 ≤ C → ∀ G : ℂ → ℂ → ℂ,
        AEStronglyMeasurable (fun p : ℝ × ℝ =>
          G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)) volume →
        (∀ p : ℝ × ℝ, ‖G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤
          C * weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) →
        Integrable (fun p : ℝ × ℝ =>
          G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)) volume ∧
        (∀ᵐ t : ℝ ∂volume, Integrable (fun s : ℝ =>
          G ((y : ℂ) + (t : ℂ) * Complex.I) ((v : ℂ) + (s : ℂ) * Complex.I)) volume) ∧
        Integrable (fun t : ℝ =>
          comparisonVerticalIntegral v (fun z => G ((y : ℂ) + (t : ℂ) * Complex.I) z)) volume ∧
        ‖comparisonVerticalIntegral y (fun w => comparisonVerticalIntegral v (fun z => G w z))‖ ≤
          ((2 * Real.pi)⁻¹) ^ 2 * (C * Cw * (1 + |ξ.im|) ^ (-B)) := by
  obtain ⟨Cw, hCw0, hCw⟩ := joint_integral_bound D a₁ b₁ a₂ b₂ x₀ x₁ ha₁ hab₁ hab₂ hx B k hB hk
  refine ⟨Cw, hCw0, fun ξ hx0 hx1 v y hv1 hv2 hy1 hy2 C hC G hmeas hbd => ?_⟩
  obtain ⟨hint, hle⟩ := hCw ξ hx0 hx1 v y hv1 hv2 hy1 hy2 C hC
    (fun p : ℝ × ℝ => G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I))
    hmeas hbd
  have hle' : ‖∫ p : ℝ × ℝ, G ((y : ℂ) + (p.2 : ℂ) * Complex.I)
      ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤ C * Cw * (1 + |ξ.im|) ^ (-B) := hle
  have hint' : Integrable (fun p : ℝ × ℝ =>
      G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I))
      (volume.prod volume) := hint
  have hfub : ∫ p : ℝ × ℝ, G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)
      = ∫ t : ℝ, ∫ s : ℝ, G ((y : ℂ) + (t : ℂ) * Complex.I) ((v : ℂ) + (s : ℂ) * Complex.I) :=
    integral_prod_symm _ hint'
  refine ⟨hint, hint'.prod_left_ae, ?_, ?_⟩
  · simp only [comparisonVerticalIntegral]
    exact (hint'.integral_prod_right).const_mul _
  · have e : comparisonVerticalIntegral y (fun w => comparisonVerticalIntegral v (fun z => G w z))
        = (2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ))⁻¹ *
          ∫ p : ℝ × ℝ, G ((y : ℂ) + (p.2 : ℂ) * Complex.I)
            ((v : ℂ) + (p.1 : ℂ) * Complex.I)) := by
      rw [hfub]
      simp only [comparisonVerticalIntegral, integral_const_mul]
    have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
    have h2 : ((2 * (Real.pi : ℂ))⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [e, h2, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi]
    calc (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ * ‖∫ p : ℝ × ℝ, G ((y : ℂ) + (p.2 : ℂ) * Complex.I)
            ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖)
        ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ * (C * Cw * (1 + |ξ.im|) ^ (-B))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle' hpi) hpi
      _ = ((2 * Real.pi)⁻¹) ^ 2 * (C * Cw * (1 + |ξ.im|) ^ (-B)) := by ring

theorem section_integrable (a₁ b₁ a₂ b₂ x₀ x₁ : ℝ) (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (hab₂ : a₂ ≤ b₂) (hx : x₀ ≤ x₁) (k : ℝ) (hk : 0 ≤ k) :
    ∀ ξ : ℂ, x₀ ≤ ξ.re → ξ.re ≤ x₁ →
      ∀ v y : ℝ, a₁ ≤ v → v ≤ b₁ → a₂ ≤ y → y ≤ b₂ →
      ∀ (C : ℝ), ∀ Fn : ℝ × ℝ → ℂ, Continuous Fn →
        (∀ p, ‖Fn p‖ ≤ C * weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) →
        ∀ t : ℝ, Integrable (fun s : ℝ => Fn (s, t)) volume := by
  intro ξ hx0 hx1 v y hv1 hv2 hy1 hy2 C Fn hFc hbd t
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k + 2 ≤ (n : ℝ) :=
    ⟨⌈k⌉₊ + 2, by have := Nat.le_ceil k; push_cast; linarith⟩
  obtain ⟨C1, hC1⟩ := D.M_vertical_decay a₁ b₁ ha₁ hab₁ n
  have hB : 1 < (n : ℝ) - k := by linarith
  have hexpb : ∀ s : ℝ, ‖Complex.exp ((ξ + ((v : ℂ) + (s : ℂ) * Complex.I) - 1) ^ 2)‖ ≤
      Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) := by
    intro s
    rw [Complex.norm_exp]
    have hre : ((ξ + ((v : ℂ) + (s : ℂ) * Complex.I) - 1) ^ 2).re =
        (ξ.re + v - 1) ^ 2 - (ξ.im + s) ^ 2 := by
      simp [pow_two] <;> ring
    rw [hre]
    apply Real.exp_le_exp.mpr
    have hsq : (ξ.re + v - 1) ^ 2 ≤ (|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (x₀ + a₁ - 1), abs_nonneg (x₁ + b₁ - 1)])
        (by linarith [le_abs_self (x₁ + b₁ - 1), abs_nonneg (x₀ + a₁ - 1)])
    linarith [sq_nonneg (ξ.im + s)]
  have hMn : ∀ s : ℝ, ‖D.M ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤
      |C1| * (1 + |s|) ^ (-(n : ℝ)) := by
    intro s
    have h := hC1 ((v : ℂ) + (s : ℂ) * Complex.I) (by simpa using hv1) (by simpa using hv2)
    have h' : (1 + |s|) ^ n * ‖D.M ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤ |C1| := by
      simpa using h.trans (le_abs_self _)
    have hpos : (0 : ℝ) < 1 + |s| := by positivity
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos n),
      mul_comm]
    exact h'
  have key : ∀ s : ℝ, ‖Fn (s, t)‖ ≤
      (|C| * Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C1| *
        ‖D.W1Hat ((y : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t| + |ξ.im|) ^ k) *
        (1 + |s|) ^ (-((n : ℝ) - k)) := by
    intro s
    have hs : ‖Fn (s, t)‖ ≤ C * weightModulus D ξ v y (s, t) * (2 + |s| + |t| + |ξ.im|) ^ k :=
      hbd (s, t)
    have hwm : weightModulus D ξ v y (s, t) =
        ‖Complex.exp ((ξ + ((v : ℂ) + (s : ℂ) * Complex.I) - 1) ^ 2)‖ *
          ‖D.M ((v : ℂ) + (s : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (t : ℂ) * Complex.I)‖ := by
      simp only [weightModulus, norm_mul]
    have hwm0 : 0 ≤ weightModulus D ξ v y (s, t) := by
      rw [hwm]; positivity
    have hP0 : 0 ≤ (2 + |s| + |t| + |ξ.im|) ^ k := by positivity
    have h1 : 2 + |s| + |t| + |ξ.im| ≤ (1 + |s|) * (2 + |t| + |ξ.im|) := by
      nlinarith [abs_nonneg s, abs_nonneg t, abs_nonneg ξ.im,
        mul_nonneg (abs_nonneg s) (add_nonneg (abs_nonneg t) (abs_nonneg ξ.im))]
    have hP : (2 + |s| + |t| + |ξ.im|) ^ k ≤ (1 + |s|) ^ k * (2 + |t| + |ξ.im|) ^ k := by
      calc (2 + |s| + |t| + |ξ.im|) ^ k ≤ ((1 + |s|) * (2 + |t| + |ξ.im|)) ^ k :=
            Real.rpow_le_rpow (by positivity) h1 hk
        _ = _ := Real.mul_rpow (by positivity) (by positivity)
    have he := hexpb s
    have hM := hMn s
    have hu : (0 : ℝ) < 1 + |s| := by positivity
    have hexp : (1 + |s|) ^ (-(n : ℝ)) * (1 + |s|) ^ k = (1 + |s|) ^ (-((n : ℝ) - k)) := by
      rw [← Real.rpow_add hu]
      congr 1
      ring
    calc ‖Fn (s, t)‖ ≤ C * weightModulus D ξ v y (s, t) * (2 + |s| + |t| + |ξ.im|) ^ k := hs
      _ ≤ |C| * weightModulus D ξ v y (s, t) * (2 + |s| + |t| + |ξ.im|) ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hwm0) hP0
      _ = |C| * (‖Complex.exp ((ξ + ((v : ℂ) + (s : ℂ) * Complex.I) - 1) ^ 2)‖ *
          ‖D.M ((v : ℂ) + (s : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (t : ℂ) * Complex.I)‖) *
          (2 + |s| + |t| + |ξ.im|) ^ k := by rw [hwm]
      _ ≤ |C| * (Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) *
          (|C1| * (1 + |s|) ^ (-(n : ℝ))) *
          ‖D.W1Hat ((y : ℂ) + (t : ℂ) * Complex.I)‖) *
          ((1 + |s|) ^ k * (2 + |t| + |ξ.im|) ^ k) := by gcongr
      _ = (|C| * Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C1| *
          ‖D.W1Hat ((y : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t| + |ξ.im|) ^ k) *
          ((1 + |s|) ^ (-(n : ℝ)) * (1 + |s|) ^ k) := by ring
      _ = _ := by rw [hexp]
  have hI := (one_add_abs_rpow_integrable ((n : ℝ) - k) hB).const_mul
    (|C| * Real.exp ((|x₀ + a₁ - 1| + |x₁ + b₁ - 1|) ^ 2) * |C1| *
        ‖D.W1Hat ((y : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t| + |ξ.im|) ^ k)
  exact Integrable.mono' hI
    ((hFc.comp (by fun_prop : Continuous fun s : ℝ => (s, t))).aestronglyMeasurable)
    (Filter.Eventually.of_forall key)

theorem section_integrable_G (a₁ b₁ a₂ b₂ x₀ x₁ : ℝ) (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (hab₂ : a₂ ≤ b₂) (hx : x₀ ≤ x₁) (k : ℝ) (hk : 0 ≤ k) :
    ∀ ξ : ℂ, x₀ ≤ ξ.re → ξ.re ≤ x₁ →
      ∀ v y : ℝ, a₁ ≤ v → v ≤ b₁ → a₂ ≤ y → y ≤ b₂ →
      ∀ (C : ℝ) (G : ℂ → ℂ → ℂ), Continuous (fun p : ℂ × ℂ => G p.1 p.2) →
        (∀ p : ℝ × ℝ, ‖G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤
          C * weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) →
        ∀ t : ℝ, Integrable (fun s : ℝ =>
          G ((y : ℂ) + (t : ℂ) * Complex.I) ((v : ℂ) + (s : ℂ) * Complex.I)) volume := by
  intro ξ hx0 hx1 v y hv1 hv2 hy1 hy2 C G hG hbd t
  have hc : Continuous (fun p : ℝ × ℝ =>
      G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)) :=
    hG.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
      ((y : ℂ) + (p.2 : ℂ) * Complex.I, (v : ℂ) + (p.1 : ℂ) * Complex.I))
  exact section_integrable D a₁ b₁ a₂ b₂ x₀ x₁ ha₁ hab₁ hab₂ hx k hk ξ hx0 hx1 v y hv1 hv2 hy1 hy2
    C _ hc hbd t

theorem vertical_integrable_of_decay (G : ℂ → ℂ) (hG : Continuous G) (x A B : ℝ) (hB : 1 < B)
    (h : ∀ t : ℝ, ‖G ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 + |t|) ^ (-B)) :
    Integrable (fun t : ℝ => G ((x : ℂ) + (t : ℂ) * Complex.I)) volume := by
  have hI : Integrable (fun t : ℝ => A * (1 + |t|) ^ (-B)) volume := by
    have := integrable_one_add_norm (μ := volume) (E := ℝ) (r := B) (by norm_num; linarith)
    exact (by simpa [Real.norm_eq_abs] using this :
      Integrable (fun t : ℝ => (1 + |t|) ^ (-B)) volume).const_mul A
  refine Integrable.mono' hI ?_ (Filter.Eventually.of_forall fun t => h t)
  exact (hG.comp (by fun_prop)).aestronglyMeasurable

theorem vertical_integral_norm_le (G : ℂ → ℂ) (hG : Continuous G) (x A B : ℝ) (hB : 1 < B)
    (h : ∀ t : ℝ, ‖G ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 + |t|) ^ (-B)) :
    ‖comparisonVerticalIntegral x G‖ ≤
      (2 * Real.pi)⁻¹ * (A * ∫ t : ℝ, (1 + |t|) ^ (-B)) := by
  have hI : Integrable (fun t : ℝ => (1 + |t|) ^ (-B)) volume := by
    have := integrable_one_add_norm (μ := volume) (E := ℝ) (r := B) (by norm_num; linarith)
    simpa [Real.norm_eq_abs] using this
  have hpi : (0:ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  unfold comparisonVerticalIntegral
  have h2 : ((2 * (Real.pi : ℂ))⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi]
  apply mul_le_mul_of_nonneg_left _ hpi
  calc ‖∫ t : ℝ, G ((x : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∫ t : ℝ, ‖G ((x : ℂ) + (t : ℂ) * Complex.I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, A * (1 + |t|) ^ (-B) := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => norm_nonneg _) (hI.const_mul A)
          (Filter.Eventually.of_forall fun t => h t)
    _ = A * ∫ t : ℝ, (1 + |t|) ^ (-B) := integral_const_mul _ _

end

end DedekindZetaZeroFree.Quantitative.KernelWeightIntegration
