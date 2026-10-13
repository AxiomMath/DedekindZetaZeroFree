module

public import DedekindZetaZeroFree.Analysis.GaussianWeightConvolution
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Height
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.AnalyticContinuation
public import DedekindZetaZeroFree.Analysis.Integration.HolomorphicDominatedIntegral
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.SubpowerBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowKernelHolomorphy

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.DetectorHeight

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma exp_shift (x₀ δ r : ℝ) (h : |δ| ≤ r) :
    Real.exp (-(x₀ + δ) ^ 2) ≤
      Real.exp (r ^ 2) * (Real.exp (-(x₀ - r) ^ 2) + Real.exp (-(x₀ + r) ^ 2)) := by
  have h1 := abs_le.1 h
  rcases le_total 0 x₀ with hx | hx
  · have : -(x₀ + δ) ^ 2 ≤ r ^ 2 + -(x₀ - r) ^ 2 := by
      nlinarith [mul_nonneg hx (show 0 ≤ δ + r by linarith [h1.1]), sq_nonneg δ]
    calc Real.exp (-(x₀ + δ) ^ 2) ≤ Real.exp (r ^ 2 + -(x₀ - r) ^ 2) := Real.exp_le_exp.2 this
      _ = Real.exp (r ^ 2) * Real.exp (-(x₀ - r) ^ 2) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le
  · have : -(x₀ + δ) ^ 2 ≤ r ^ 2 + -(x₀ + r) ^ 2 := by
      nlinarith [mul_nonneg (neg_nonneg.2 hx) (show 0 ≤ r - δ by linarith [h1.2]), sq_nonneg δ]
    calc Real.exp (-(x₀ + δ) ^ 2) ≤ Real.exp (r ^ 2 + -(x₀ + r) ^ 2) := Real.exp_le_exp.2 this
      _ = Real.exp (r ^ 2) * Real.exp (-(x₀ + r) ^ 2) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (Real.exp_pos _).le) (Real.exp_pos _).le

private lemma pt_env (X X₀ a a₀ r' v s t1 t2 k : ℝ) (m w : ℂ) (hk : 0 ≤ k) (hr0 : 0 < r')
    (hr1 : r' ≤ 1) (hX : |X - X₀| ≤ 1) (ha : |a - a₀| ≤ r') :
    Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2) * ‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k ≤
      Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) * 2 ^ k *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) * ‖m‖ * ‖w‖ *
            (2 + |t1| + |t2| + |a₀ + r'|) ^ k +
         Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) * ‖m‖ * ‖w‖ *
            (2 + |t1| + |t2| + |a₀ - r'|) ^ k) := by
  have ha' := abs_le.1 ha
  have hq : (X + v - 1) ^ 2 ≤ (|X₀| + |v| + 2) ^ 2 := by
    have h1 := abs_le.1 hX
    have h2 := neg_abs_le X₀
    have h3 := le_abs_self X₀
    have h4 := neg_abs_le v
    have h5 := le_abs_self v
    exact sq_le_sq' (by linarith) (by linarith)
  have hshift := exp_shift (a₀ + s) (a - a₀) r' ha
  have e1 : (a₀ + s) + (a - a₀) = a + s := by ring
  rw [e1] at hshift
  have hA : Real.exp (-((a₀ + s) - r') ^ 2) ≤ Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg (X₀ + v - 1)])
  have hB : Real.exp (-((a₀ + s) + r') ^ 2) ≤ Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg (X₀ + v - 1)])
  have hexp_r : Real.exp (r' ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.2 (by nlinarith)
  have h1 : Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2) ≤
      Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
          Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2)) := by
    have hsum : Real.exp (-((a₀ + s) - r') ^ 2) + Real.exp (-((a₀ + s) + r') ^ 2) ≤
        Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
          Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) := by linarith
    calc Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2)
        = Real.exp ((X + v - 1) ^ 2) * Real.exp (-(a + s) ^ 2) := by
          rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp ((|X₀| + |v| + 2) ^ 2) * (Real.exp (r' ^ 2) *
            (Real.exp (-((a₀ + s) - r') ^ 2) + Real.exp (-((a₀ + s) + r') ^ 2))) :=
          mul_le_mul (Real.exp_le_exp.2 hq) hshift (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ Real.exp ((|X₀| + |v| + 2) ^ 2) * (Real.exp (r' ^ 2) *
            (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
              Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ ≤ Real.exp ((|X₀| + |v| + 2) ^ 2) * (Real.exp 1 *
            (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
              Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hexp_r
              (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (Real.exp_pos _).le
      _ = _ := by rw [Real.exp_add]; ring
  have hPP : (2 + |t1| + |t2| + |a|) ^ k ≤ 2 ^ k * (2 + |t1| + |t2| + |a₀ + r'|) ^ k := by
    have hle : 2 + |t1| + |t2| + |a| ≤ 2 * (2 + |t1| + |t2| + |a₀ + r'|) := by
      have : |a| ≤ |a₀ + r'| + 2 :=
        abs_le.2 ⟨by linarith [neg_le_abs (a₀ + r')], by linarith [le_abs_self (a₀ + r')]⟩
      linarith [abs_nonneg t1, abs_nonneg t2, abs_nonneg (a₀ + r')]
    calc (2 + |t1| + |t2| + |a|) ^ k ≤ (2 * (2 + |t1| + |t2| + |a₀ + r'|)) ^ k :=
          Real.rpow_le_rpow (by positivity) hle hk
      _ = 2 ^ k * (2 + |t1| + |t2| + |a₀ + r'|) ^ k := Real.mul_rpow (by norm_num) (by positivity)
  have hPM : (2 + |t1| + |t2| + |a|) ^ k ≤ 2 ^ k * (2 + |t1| + |t2| + |a₀ - r'|) ^ k := by
    have hle : 2 + |t1| + |t2| + |a| ≤ 2 * (2 + |t1| + |t2| + |a₀ - r'|) := by
      have : |a| ≤ |a₀ - r'| + 2 :=
        abs_le.2 ⟨by linarith [neg_le_abs (a₀ - r')], by linarith [le_abs_self (a₀ - r')]⟩
      linarith [abs_nonneg t1, abs_nonneg t2, abs_nonneg (a₀ - r')]
    calc (2 + |t1| + |t2| + |a|) ^ k ≤ (2 * (2 + |t1| + |t2| + |a₀ - r'|)) ^ k :=
          Real.rpow_le_rpow (by positivity) hle hk
      _ = 2 ^ k * (2 + |t1| + |t2| + |a₀ - r'|) ^ k := Real.mul_rpow (by norm_num) (by positivity)
  have hK : 0 ≤ ‖m‖ * ‖w‖ := by positivity
  have heP : 0 ≤ Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) := (Real.exp_pos _).le
  have heM : 0 ≤ Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) := (Real.exp_pos _).le
  have hE : 0 ≤ Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) := (Real.exp_pos _).le
  have a1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPP hK) heP
  have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPM hK) heM
  have hKP : 0 ≤ ‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k := by positivity
  calc Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2) * ‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k
      = Real.exp ((X + v - 1) ^ 2 - (a + s) ^ 2) *
          (‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k) := by ring
    _ ≤ (Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) +
          Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2))) *
          (‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k) := mul_le_mul_of_nonneg_right h1 hKP
    _ = Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) * (‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k) +
         Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) * (‖m‖ * ‖w‖ * (2 + |t1| + |t2| + |a|) ^ k)) := by
          ring
    _ ≤ Real.exp ((|X₀| + |v| + 2) ^ 2 + 1) *
        (Real.exp ((X₀ + v - 1) ^ 2 - (a₀ + r' + s) ^ 2) *
            (‖m‖ * ‖w‖ * (2 ^ k * (2 + |t1| + |t2| + |a₀ + r'|) ^ k)) +
         Real.exp ((X₀ + v - 1) ^ 2 - (a₀ - r' + s) ^ 2) *
            (‖m‖ * ‖w‖ * (2 ^ k * (2 + |t1| + |t2| + |a₀ - r'|) ^ k))) := by
          apply mul_le_mul_of_nonneg_left _ hE
          linarith [a1, a2]
    _ = _ := by ring

private lemma wM_eq (η : ℂ) (v y : ℝ) (p : ℝ × ℝ) :
    WeightConvolution.weightModulus D η v y p =
      Real.exp ((η.re + v - 1) ^ 2 - (η.im + p.1) ^ 2) *
        ‖D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ *
        ‖D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖ := by
  unfold WeightConvolution.weightModulus
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have hre : ((η + ((v : ℂ) + (p.1 : ℂ) * Complex.I) - 1) ^ 2).re =
      (η.re + v - 1) ^ 2 - (η.im + p.1) ^ 2 := by
    simp [pow_two] <;> ring
  rw [hre]

theorem differentiableOn_nested_integral (V : Set ℂ) (hV : IsOpen V) (G : ℂ → ℂ → ℂ → ℂ)
    (y v : ℝ) (hv : 0 < v)
    (hdiff : ∀ ξ ∈ V, ∀ s t : ℝ, DifferentiableAt ℂ
      (fun x : ℂ => G x ((y : ℂ) + (s : ℂ) * Complex.I) ((v : ℂ) + (t : ℂ) * Complex.I)) ξ)
    (hcont : ∀ ξ ∈ V, Continuous (fun p : ℝ × ℝ =>
      G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)))
    (hmaj : ∀ ξ₀ ∈ V, ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ V ∧ ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p : ℝ × ℝ,
        ‖G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤
          C * WeightConvolution.weightModulus D ξ v y p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k) :
    DifferentiableOn ℂ (fun ξ => comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => G ξ w z))) V := by
  classical
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℝ × ℝ → ℂ, ∀ ξ p, H ξ p =
      G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I) :=
    ⟨fun ξ p => G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I),
      fun _ _ => rfl⟩
  have hHf : ∀ ξ, H ξ = fun p : ℝ × ℝ =>
      G ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I) :=
    fun ξ => funext (hH ξ)
  have hdom : ∀ ξ₀ ∈ V, ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ V ∧
      ∃ g : ℝ × ℝ → ℝ, Integrable g ∧ ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p, ‖H ξ p‖ ≤ g p := by
    intro ξ₀ hξ₀
    obtain ⟨r, hr, hball, C, k, hC, hk, hb⟩ := hmaj ξ₀ hξ₀
    obtain ⟨C', -, hC'⟩ := WeightConvolution.weight_kernel_decay D v v y y ξ₀.re ξ₀.re hv
      le_rfl le_rfl le_rfl 1 k one_pos hk
    have hr' : 0 < min r 1 := lt_min hr one_pos
    obtain ⟨ξp, hpre, hpim⟩ : ∃ ξp : ℂ, ξp.re = ξ₀.re ∧ ξp.im = ξ₀.im + min r 1 :=
      ⟨⟨ξ₀.re, ξ₀.im + min r 1⟩, rfl, rfl⟩
    obtain ⟨ξm, hmre, hmim⟩ : ∃ ξm : ℂ, ξm.re = ξ₀.re ∧ ξm.im = ξ₀.im - min r 1 :=
      ⟨⟨ξ₀.re, ξ₀.im - min r 1⟩, rfl, rfl⟩
    have hIp := (hC' ξp hpre.ge hpre.le v y le_rfl le_rfl le_rfl le_rfl).1
    have hIm := (hC' ξm hmre.ge hmre.le v y le_rfl le_rfl le_rfl le_rfl).1
    refine ⟨min r 1, hr', (Metric.ball_subset_ball (min_le_left _ _)).trans hball,
      fun p => C * Real.exp ((|ξ₀.re| + |v| + 2) ^ 2 + 1) * 2 ^ k *
        (WeightConvolution.weightModulus D ξp v y p * (2 + |p.1| + |p.2| + |ξp.im|) ^ k +
         WeightConvolution.weightModulus D ξm v y p * (2 + |p.1| + |p.2| + |ξm.im|) ^ k),
      (hIp.add hIm).const_mul _, ?_⟩
    intro ξ hξ p
    have hd : ‖ξ - ξ₀‖ < min r 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hξ
    have hX : |ξ.re - ξ₀.re| ≤ 1 := by
      have := Complex.abs_re_le_norm (ξ - ξ₀)
      rw [Complex.sub_re] at this
      linarith [min_le_right r 1]
    have ha : |ξ.im - ξ₀.im| ≤ min r 1 := by
      have := Complex.abs_im_le_norm (ξ - ξ₀)
      rw [Complex.sub_im] at this
      linarith
    have hb' := hb ξ (Metric.ball_subset_ball (min_le_left _ _) hξ) p
    have hb'' : ‖H ξ p‖ ≤ C * WeightConvolution.weightModulus D ξ v y p *
        (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by rw [hH]; exact hb'
    refine hb''.trans ?_
    beta_reduce
    have key := pt_env ξ.re ξ₀.re ξ.im ξ₀.im (min r 1) v p.1 p.1 p.2 k
      (D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)) (D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I))
      hk hr' (min_le_right _ _) hX ha
    have key2 := mul_le_mul_of_nonneg_left key hC
    rw [wM_eq D ξ v y p, wM_eq D ξp v y p, wM_eq D ξm v y p, hpre, hpim, hmre, hmim]
    calc C * (Real.exp ((ξ.re + v - 1) ^ 2 - (ξ.im + p.1) ^ 2) *
          ‖D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖) * (2 + |p.1| + |p.2| + |ξ.im|) ^ k
        = C * (Real.exp ((ξ.re + v - 1) ^ 2 - (ξ.im + p.1) ^ 2) *
          ‖D.M ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (p.2 : ℂ) * Complex.I)‖ * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) := by
          ring
      _ ≤ _ := key2
      _ = _ := by ring
  have hmeas : ∀ ξ ∈ V, AEStronglyMeasurable (H ξ) (volume : Measure (ℝ × ℝ)) := by
    intro ξ hξ
    rw [hHf ξ]
    exact (hcont ξ hξ).aestronglyMeasurable
  have hdiffp : ∀ p, DifferentiableOn ℂ (fun ξ => H ξ p) V := by
    intro p ξ hξ
    simp only [hH]
    exact (hdiff ξ hξ p.2 p.1).differentiableWithinAt
  have h2 := HolomorphicDominatedIntegral.differentiableOn_integral_prod_real hV hmeas hdiffp hdom
  have heq : ∀ ξ ∈ V, comparisonVerticalIntegral y (fun w =>
      comparisonVerticalIntegral v (fun z => G ξ w z)) =
        ((2 * (Real.pi : ℂ))⁻¹) ^ 2 * ∫ p, H ξ p := by
    intro ξ hξ
    have hint : Integrable (H ξ) :=
      HolomorphicDominatedIntegral.integrable_of_locally_dominated (μ := volume) hmeas hdom hξ
    have e0 : ∫ p, H ξ p = ∫ s : ℝ, ∫ t : ℝ, H ξ (t, s) := integral_prod_symm (H ξ) hint
    have e1 : ∫ s : ℝ, ∫ t : ℝ, H ξ (t, s) = ∫ s : ℝ, ∫ t : ℝ,
        G ξ ((y : ℂ) + (s : ℂ) * Complex.I) ((v : ℂ) + (t : ℂ) * Complex.I) := by
      simp only [hH]
    show (2 * (Real.pi : ℂ))⁻¹ * ∫ s : ℝ, ((2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
      G ξ ((y : ℂ) + (s : ℂ) * Complex.I) ((v : ℂ) + (t : ℂ) * Complex.I)) = _
    rw [integral_const_mul, e0, e1]
    ring
  exact (h2.const_mul (((2 * (Real.pi : ℂ))⁻¹) ^ 2)).congr (fun ξ hξ => heq ξ hξ)

private lemma zpow_bound (Z : ℝ) (hZ : 0 < Z) (c x x₀ : ℝ) (hx : |x - x₀| ≤ 1) :
    Z ^ (c + x) ≤ Real.exp (|Real.log Z| * (|c| + |x₀| + 1)) := by
  rw [Real.rpow_def_of_pos hZ]
  apply Real.exp_le_exp.2
  calc Real.log Z * (c + x) ≤ |Real.log Z * (c + x)| := le_abs_self _
    _ = |Real.log Z| * |c + x| := abs_mul _ _
    _ ≤ |Real.log Z| * (|c| + |x₀| + 1) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have h1 := abs_add_le c x
        have h2 := abs_sub_abs_le_abs_sub x x₀
        linarith

private lemma K_norm_eq' (u : D.Row) (hq : 0 < D.q u) (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) (Z : ℝ)
    (hZ : 0 < Z) :
    ‖K D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ =
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * v + Scales.yExponent * (y - 1)) * D.q u ^ (-v) *
        WeightConvolution.weightModulus D ξ v y p *
        ‖rowFactor D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
          ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ := by
  unfold K kernelWith
  have hZc : (0 : ℝ) < Z := hZ
  have hqc : (0 : ℝ) < D.q u := hq
  have hre : ∀ A B C X E R : ℂ, A * B * C * X * E * R = A * E * (B * C * X) * R := by
    intro A B C X E R; ring
  have hkey : ∀ A E X R : ℂ, ‖A * E * X * R‖ = ‖A‖ * ‖E‖ * ‖X‖ * ‖R‖ := by
    intro A E X R; simp only [norm_mul]
  rw [hre, hkey]
  unfold WeightConvolution.weightModulus
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZc, Complex.norm_cpow_eq_rpow_re_of_pos hqc]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_natCast]
  simp only [zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_sub]
  try ring_nf

theorem K_local_majorant (A_F : ℝ) (hconv : ConvexityExponent D A_F) (u : D.Row)
    (hu1 : u.toFrequency.u ≠ 1) (hq2 : 2 ≤ D.q u)
    (hent : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s)
    (Z : ℝ) (hZ : 0 < Z) (ξ₀ : ℂ) (h₀ : Scales.goodLine - EulerDomain.pad < ξ₀.re)
    (hL : D.Llam u ξ₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ ξ ∈ Metric.ball ξ₀ r, Scales.goodLine - EulerDomain.pad < ξ.re ∧ D.Llam u ξ ≠ 0) ∧
      ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧ ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p : ℝ × ℝ,
        ‖K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          C * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
  have hq0 : 0 < D.q u := by linarith
  have hxg0 : 0 < Scales.goodLine - EulerDomain.pad := by
    unfold Scales.goodLine EulerDomain.pad; norm_num
  have hy : Scales.wLine = 3 / 25 := by unfold Scales.wLine; norm_num
  have hLc : ContinuousAt (D.Llam u) ξ₀ :=
    (RowAnalyticContinuation.Llam_analyticOnNhd D u hu1 ξ₀ (by
      show 0 < ξ₀.re
      linarith)).continuousAt
  have hnorm : 0 < ‖D.Llam u ξ₀‖ := norm_pos_iff.2 hL
  obtain ⟨r₁, hr₁, hball₁⟩ : ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ ξ : ℂ, dist ξ ξ₀ < r₁ →
      ‖D.Llam u ξ₀‖ / 2 < ‖D.Llam u ξ‖ := by
    have := hLc.norm.eventually (lt_mem_nhds (show ‖D.Llam u ξ₀‖ / 2 < ‖D.Llam u ξ₀‖ by linarith))
    obtain ⟨e, he, h⟩ := Metric.eventually_nhds_iff.1 this
    exact ⟨e, he, fun ξ hξ => h hξ⟩
  have hr : 0 < min (min r₁ 1) (ξ₀.re - (Scales.goodLine - EulerDomain.pad)) :=
    lt_min (lt_min hr₁ one_pos) (by linarith)
  obtain ⟨C1, hC1, h1⟩ := RightHeckeBounds.zetaSCont_norm_le_right D (12 / 5) (by norm_num)
  obtain ⟨C2, hC2, h2⟩ := hconv.1 1 one_pos
  obtain ⟨C3, hC3, h3⟩ := EulerSubpower.Hu_subpower_paddedBoxes D 1 one_pos
  have hLpsi : ∀ w : ℂ, w.re = Scales.wLine →
      ‖D.Lpsi u w‖ ≤ C2 * D.q u ^ ((11 / 25 : ℝ) + 1) * (2 + |w.im|) ^ A_F := by
    intro w hw
    obtain ⟨g, hg, hgeq⟩ := hent
    have hw0 : 0 < w.re := by rw [hw, hy]; norm_num
    have e : D.Lpsi u w = g w :=
      (RowAnalyticContinuation.entire_eq_Lpsi D u hu1 hg hgeq w hw0).symm
    have hwe : w = ((Scales.wLine : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hw]
    have key := h2 u hu1 (D.q u) hq2 le_rfl (by linarith) g hg hgeq w.im
    calc ‖D.Lpsi u w‖ = ‖g (((Scales.wLine : ℝ) : ℂ) + (w.im : ℂ) * Complex.I)‖ := by
          rw [e, ← hwe]
      _ ≤ C2 * D.q u ^ ((11 / 25 : ℝ) + 1) * (2 + |w.im|) ^ A_F := by
          rw [hy]; exact key
  set c0 : ℝ := Scales.xExponent / 2 - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1) with hc0
  set Zbd : ℝ := Real.exp (|Real.log Z| * (|c0| + |ξ₀.re| + 1)) with hZbd
  set Cinv : ℝ := (‖D.Llam u ξ₀‖ / 2)⁻¹ with hCinv
  have hCinv0 : 0 < Cinv := inv_pos.2 (by linarith)
  have hZbd0 : 0 < Zbd := Real.exp_pos _
  refine ⟨min (min r₁ 1) (ξ₀.re - (Scales.goodLine - EulerDomain.pad)), hr, ?_,
    Zbd * D.q u ^ (-Scales.zLine) * (C1 * (C2 * D.q u ^ ((11 / 25 : ℝ) + 1)) * Cinv *
      (C3 * D.q u ^ (1 : ℝ))), max A_F 0, ?_, le_max_right _ _, ?_⟩
  · intro ξ hξ
    have hd : dist ξ ξ₀ < min (min r₁ 1) (ξ₀.re - (Scales.goodLine - EulerDomain.pad)) := hξ
    have h1' : dist ξ ξ₀ < r₁ := hd.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hre : |ξ.re - ξ₀.re| ≤ dist ξ ξ₀ := by
      rw [dist_eq_norm]
      have := Complex.abs_re_le_norm (ξ - ξ₀)
      rwa [Complex.sub_re] at this
    have hr2 := min_le_right (min r₁ 1) (ξ₀.re - (Scales.goodLine - EulerDomain.pad))
    have hlt := (abs_le.1 hre).1
    refine ⟨by linarith, ?_⟩
    intro h0
    have := hball₁ ξ h1'
    rw [h0, norm_zero] at this
    linarith
  · positivity
  · intro ξ hξ p
    have hd : dist ξ ξ₀ < min (min r₁ 1) (ξ₀.re - (Scales.goodLine - EulerDomain.pad)) := hξ
    have h1' : dist ξ ξ₀ < r₁ := hd.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have h1'' : dist ξ ξ₀ < 1 := hd.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hr2 := min_le_right (min r₁ 1) (ξ₀.re - (Scales.goodLine - EulerDomain.pad))
    have hre : |ξ.re - ξ₀.re| ≤ dist ξ ξ₀ := by
      rw [dist_eq_norm]
      have := Complex.abs_re_le_norm (ξ - ξ₀)
      rwa [Complex.sub_re] at this
    have hlt := (abs_le.1 hre).1
    have hxg : Scales.goodLine - EulerDomain.pad ≤ ξ.re := by linarith
    have hLξ : ‖(D.Llam u ξ)⁻¹‖ ≤ Cinv := by
      rw [norm_inv]
      exact inv_anti₀ (by linarith) (hball₁ ξ h1').le
    have hw : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).re = Scales.wLine := by simp
    have hz : (((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I).re = Scales.zLine := by simp
    have him : (((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
    set w : ℂ := ((Scales.wLine : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I with hwdef
    set z : ℂ := ((Scales.zLine : ℝ) : ℂ) + (p.1 : ℂ) * Complex.I with hzdef
    have hz1 : ‖D.zetaSCont (6 * z)‖ ≤ C1 := by
      apply h1
      have h6 : (6 * z).re = 6 * z.re := by simp [Complex.mul_re]
      rw [h6, hz]
      norm_num [Scales.zLine]
    have hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.paddedBoxes := by
      refine Or.inl (Or.inl ?_)
      refine ⟨hxg, ?_, ?_⟩
      · show 3 / 25 - EulerDomain.pad ≤ w.re
        rw [hw, hy]; unfold EulerDomain.pad; norm_num
      · show 2 / 5 - EulerDomain.pad ≤ z.re
        rw [hz]; unfold Scales.zLine EulerDomain.pad; norm_num
    have hHu : ‖EulerDomain.Hu D u ξ w z‖ ≤ C3 * D.q u ^ (1 : ℝ) := (h3 u _ hmem).2
    have hLp := hLpsi w hw
    rw [him] at hLp
    have e : ‖rowFactor D u ξ w z‖ =
        ‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖(D.Llam u ξ)⁻¹‖ * ‖EulerDomain.Hu D u ξ w z‖ := by
      unfold rowFactor
      simp only [div_eq_mul_inv, norm_mul]
    have hP : 0 ≤ (2 + |p.2|) ^ A_F := by positivity
    have hRb : ‖rowFactor D u ξ w z‖ ≤
        C1 * (C2 * D.q u ^ ((11 / 25 : ℝ) + 1) * (2 + |p.2|) ^ A_F) * Cinv *
          (C3 * D.q u ^ (1 : ℝ)) := by
      rw [e]
      have hA : 0 ≤ C1 * (C2 * D.q u ^ ((11 / 25 : ℝ) + 1) * (2 + |p.2|) ^ A_F) := by positivity
      have hB : 0 ≤ C1 * (C2 * D.q u ^ ((11 / 25 : ℝ) + 1) * (2 + |p.2|) ^ A_F) * Cinv := by
        positivity
      exact mul_le_mul (mul_le_mul (mul_le_mul hz1 hLp (norm_nonneg _) hC1.le) hLξ
        (norm_nonneg _) hA) hHu (norm_nonneg _) hB
    have hZe : Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) ≤
        Zbd := by
      have : Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1) =
          c0 + ξ.re := by rw [hc0]; ring
      rw [this]
      exact zpow_bound Z hZ c0 ξ.re ξ₀.re (hre.trans h1''.le)
    have hKn : ‖K D u ξ w z Z‖ =
        Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
          D.q u ^ (-Scales.zLine) * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
          ‖rowFactor D u ξ w z‖ := K_norm_eq' D u hq0 ξ Scales.zLine Scales.wLine p Z hZ
    have hWn : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := by
      unfold WeightConvolution.weightModulus; exact norm_nonneg _
    have hpoly : (2 + |p.2|) ^ A_F ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A_F 0) :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg p.2]) (le_max_left _ _)).trans
        (Real.rpow_le_rpow (by positivity)
          (by linarith [abs_nonneg p.1, abs_nonneg ξ.im]) (le_max_right _ _))
    have hZ0 : 0 ≤ Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
        Scales.yExponent * (Scales.wLine - 1)) := Real.rpow_nonneg hZ.le _
    have hqz0 : 0 ≤ D.q u ^ (-Scales.zLine) := Real.rpow_nonneg hq0.le _
    have hR0 : 0 ≤ ‖rowFactor D u ξ w z‖ := norm_nonneg _
    have hCf : 0 ≤ C1 * (C2 * D.q u ^ ((11 / 25 : ℝ) + 1)) * Cinv * (C3 * D.q u ^ (1 : ℝ)) := by
      positivity
    rw [hKn]
    calc Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)) *
          D.q u ^ (-Scales.zLine) * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
          ‖rowFactor D u ξ w z‖
        ≤ Zbd * D.q u ^ (-Scales.zLine) * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
          (C1 * (C2 * D.q u ^ ((11 / 25 : ℝ) + 1) * (2 + |p.2|) ^ A_F) * Cinv *
            (C3 * D.q u ^ (1 : ℝ))) := by
          apply mul_le_mul _ hRb hR0 (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZe hqz0) hWn
      _ = (Zbd * D.q u ^ (-Scales.zLine) * (C1 * (C2 * D.q u ^ ((11 / 25 : ℝ) + 1)) * Cinv *
            (C3 * D.q u ^ (1 : ℝ)))) *
          WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A_F := by
          ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left hpoly
          positivity

end

end DedekindZetaZeroFree.Quantitative.RowKernelHolomorphy
