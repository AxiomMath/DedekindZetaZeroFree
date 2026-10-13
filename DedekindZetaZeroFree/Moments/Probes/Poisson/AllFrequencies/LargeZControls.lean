module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyRightBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyConvexity
public import DedekindZetaZeroFree.Moments.Probes.Poisson.KernelRegularity
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelGrowth
public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLargeZControls31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem right_bounds :
    ∃ C : ℝ, 0 < C ∧ (∀ (u : Frequency D.recipe) (w : ℂ), 4 ≤ w.re →
        (pkg D).plus u w ≠ 0 ∧ ‖(pkg D).plus u w‖ ≤ C ∧ ‖((pkg D).plus u w)⁻¹‖ ≤ C) ∧
      (∀ (u : Frequency D.recipe) (ξ : ℂ), 4 ≤ ξ.re →
        (pkg D).minus u ξ ≠ 0 ∧ ‖(pkg D).minus u ξ‖ ≤ C ∧ ‖((pkg D).minus u ξ)⁻¹‖ ≤ C) ∧
      (∀ z : ℂ, 2 ≤ z.re →
        D.recipe.L (6 * z) ≠ 0 ∧ ‖D.recipe.L (6 * z)‖ ≤ C ∧ ‖(D.recipe.L (6 * z))⁻¹‖ ≤ C) := by
  obtain ⟨C1, h1, H1⟩ := RawRightHecke31.plus_right D 4 (by norm_num)
  obtain ⟨C2, h2, H2⟩ := RawRightHecke31.minus_right D 4 (by norm_num)
  obtain ⟨C3, h3, H3⟩ := RawRightHecke31.recipe_L_right D 2 (by norm_num)
  refine ⟨max C1 (max C2 C3), lt_max_of_lt_left h1, fun u w hw => ?_, fun u ξ hξ => ?_,
    fun z hz => ?_⟩
  · obtain ⟨a, b, c⟩ := H1 u w hw
    exact ⟨a, b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
  · obtain ⟨a, b, c⟩ := H2 u ξ hξ
    exact ⟨a, b.trans ((le_max_left _ _).trans (le_max_right _ _)),
      c.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  · obtain ⟨a, b, c⟩ := H3 z hz
    exact ⟨a, b.trans ((le_max_right _ _).trans (le_max_right _ _)),
      c.trans ((le_max_right _ _).trans (le_max_right _ _))⟩

private lemma mem_OmegaStar_line (p : EulerDomain.Coordinates) (h1 : p.1.re = 4)
    (h2 : p.2.1.re = 4) (h3 : 1 / 6 < p.2.2.re) : p ∈ EulerDomain.OmegaStar := by
  show 0 < p.1.re ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re ∧ 1 < 6 * p.2.2.re + p.2.1.re ∧
    1 < p.1.re + 6 * p.2.2.re ∧ 1 < p.1.re + p.2.1.re ∧ 2 < p.1.re + p.2.1.re + 6 * p.2.2.re ∧
    5 < 6 * p.1.re + 6 * p.2.2.re ∧ 1 / 2 < p.1.re ∧ 2 < 3 * p.1.re ∧
    5 / 2 < 3 * p.1.re + p.2.1.re
  rw [h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private lemma freq_pos (u : Frequency D.recipe) : 0 < frequencyNorm D.recipe u := by
  rw [← rawFrequency_norm D u]
  exact_mod_cast D.recipe.A.exteriorNorm_pos _

theorem rawEuler_right (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe) (ξ w z : ℂ), ξ.re = 4 → w.re = 4 → 2 ≤ z.re →
      ‖AllRowEuler.InitialSeparation.correctionProduct D.context (rawFrequency D u) ξ w z‖ ≤
        C * frequencyNorm D.recipe u ^ ε := by
  obtain ⟨C, hC, h⟩ := RawEulerProduct31.correctionProduct_subpower_boxes D ε hε
  refine ⟨C, hC, fun u ξ w z hξ hw hz => ?_⟩
  have hp : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.boxes := by
    refine Or.inr ?_
    show Scales.rightLine ≤ ξ.re ∧ (1 : ℝ) ≤ w.re ∧ (1 / 20 : ℝ) ≤ z.re
    rw [hξ, hw]
    refine ⟨?_, by norm_num, by linarith⟩
    norm_num [Scales.rightLine, Scales.contourOffset]
  have h1 := (h (rawFrequency D u) (ξ, w, z) hp).2
  rw [rawFrequency_norm D u] at h1
  exact h1

theorem rawKernel_analytic_z (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) :
    AnalyticOnNhd ℂ (fun z : ℂ => rawKernel D u ξ w z Z) {z : ℂ | 1 / 6 < z.re} := by
  have hopen : IsOpen {z : ℂ | 1 / 6 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro z hz
  have hz' : (1 / 6 : ℝ) < z.re := hz
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨C, hC, -, H2, -⟩ := right_bounds D
  have hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar :=
    mem_OmegaStar_line _ hξ hw hz'
  have hd := RawKernelRegularity31.rawKernel_differentiableAt D u hu Z hZ (ξ, w, z) hmem hz'
    (H2 u ξ hξ.ge).1
  have h3 : DifferentiableAt ℂ (fun z : ℂ => ((ξ, w, z) : ℂ × ℂ × ℂ)) z :=
    (differentiableAt_const ξ).prodMk ((differentiableAt_const w).prodMk differentiableAt_id)
  exact hd.comp z h3

theorem rawKernel_differentiableOn_z (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) :
    DifferentiableOn ℂ (fun z : ℂ => rawKernel D u ξ w z Z) {z : ℂ | 1 / 6 < z.re} :=
  (rawKernel_analytic_z D u hu Z hZ ξ w hξ hw).differentiableOn

private lemma exp_norm_bound (ξ : ℂ) (v s B : ℝ) (hB : (ξ.re + v - 1) ^ 2 ≤ B) :
    ‖Complex.exp ((ξ + ((v : ℂ) + (s : ℂ) * I) - 1) ^ 2)‖ ≤
      Real.exp B * Real.exp (-(ξ.im + s) ^ 2) := by
  rw [Complex.norm_exp]
  have hre : ((ξ + ((v : ℂ) + (s : ℂ) * I) - 1) ^ 2).re =
      (ξ.re + v - 1) ^ 2 - (ξ.im + s) ^ 2 := by
    simp [pow_two] <;> ring
  rw [hre, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

private lemma key_ineq (A B Cc s : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ Cc)
    (hAs : A ≤ (1 + |s|) * Cc) :
    Real.exp (-s ^ 2) * ((Cc ^ 4)⁻¹ * (B ^ 2)⁻¹) ≤
      2 * ((A ^ 2)⁻¹ * ((B ^ 2)⁻¹ * (Cc ^ 2)⁻¹)) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hC0 : 0 < Cc := by linarith
  have he : Real.exp (-s ^ 2) * (1 + |s|) ^ 2 ≤ 2 := by
    have h1 : (1 + |s|) ^ 2 ≤ 2 * Real.exp (s ^ 2) := by
      have := Real.add_one_le_exp (s ^ 2)
      nlinarith [sq_abs s, abs_nonneg s, sq_nonneg (|s| - 1)]
    calc Real.exp (-s ^ 2) * (1 + |s|) ^ 2 ≤ Real.exp (-s ^ 2) * (2 * Real.exp (s ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 2 := by rw [mul_left_comm, ← Real.exp_add]; simp
  have hA2 : A ^ 2 ≤ ((1 + |s|) * Cc) ^ 2 := pow_le_pow_left₀ (by linarith) hAs 2
  have h2 : Real.exp (-s ^ 2) * A ^ 2 ≤ 2 * Cc ^ 2 := by
    calc Real.exp (-s ^ 2) * A ^ 2 ≤ Real.exp (-s ^ 2) * (((1 + |s|) * Cc) ^ 2) :=
          mul_le_mul_of_nonneg_left hA2 (Real.exp_pos _).le
      _ = (Real.exp (-s ^ 2) * (1 + |s|) ^ 2) * Cc ^ 2 := by ring
      _ ≤ 2 * Cc ^ 2 := mul_le_mul_of_nonneg_right he (by positivity)
  have e1 : Real.exp (-s ^ 2) * ((Cc ^ 4)⁻¹ * (B ^ 2)⁻¹) = Real.exp (-s ^ 2) / (Cc ^ 4 * B ^ 2) := by
    rw [div_eq_mul_inv, mul_inv]
  have e2 : 2 * ((A ^ 2)⁻¹ * ((B ^ 2)⁻¹ * (Cc ^ 2)⁻¹)) = 2 / (A ^ 2 * (B ^ 2 * Cc ^ 2)) := by
    rw [div_eq_mul_inv, mul_inv, mul_inv]
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  calc Real.exp (-s ^ 2) * (A ^ 2 * (B ^ 2 * Cc ^ 2))
      = (Real.exp (-s ^ 2) * A ^ 2) * (B ^ 2 * Cc ^ 2) := by ring
    _ ≤ (2 * Cc ^ 2) * (B ^ 2 * Cc ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 2 * (Cc ^ 4 * B ^ 2) := by ring

private lemma hI_inv_sq : Integrable (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) := by
  have h0 : Integrable (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  refine h0.congr (Filter.Eventually.of_forall fun x => ?_)
  show (1 + |x|) ^ (-2 : ℝ) = ((1 + |x|) ^ 2)⁻¹
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

private theorem rawKernel_norm_eq (u : Frequency D.recipe) (hq : 0 < frequencyNorm D.recipe u)
    (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) (Z : ℝ) (hZ : 0 < Z) :
    ‖rawKernel D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ =
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * v + Scales.yExponent * (y - 1)) *
        frequencyNorm D.recipe u ^ (-v) *
        WeightConvolution.weightModulus D ξ v y p *
        ‖rawFactor D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I)
          ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ := by
  unfold rawKernel
  have hZc : (0 : ℝ) < Z := hZ
  have hqc : (0 : ℝ) < frequencyNorm D.recipe u := hq
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

private theorem rawFactor_norm_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe) (ξ w z : ℂ), ξ.re = 4 → w.re = 4 →
      2 ≤ z.re → ‖rawFactor D u ξ w z‖ ≤ C * frequencyNorm D.recipe u ^ ε := by
  obtain ⟨C, hC, hp, hm, hL⟩ := right_bounds D
  obtain ⟨CE, hCE, hE⟩ := rawEuler_right D ε hε
  refine ⟨C * C * CE * C, by positivity, fun u ξ w z hξ hw hz => ?_⟩
  have hq0 := freq_pos D u
  have e : ‖rawFactor D u ξ w z‖ = ‖D.recipe.L (6 * z)‖ * ‖(pkg D).plus u w‖ *
      ‖AllRowEuler.InitialSeparation.correctionProduct D.context (rawFrequency D u) ξ w z‖ *
      ‖((pkg D).minus u ξ)⁻¹‖ := by
    unfold rawFactor
    simp only [div_eq_mul_inv, norm_mul]
  have h6 : 2 ≤ (6 * z).re := by
    have : (6 * z).re = 6 * z.re := by simp
    rw [this]; linarith
  have h1 : ‖D.recipe.L (6 * z)‖ ≤ C := (hL z hz).2.1
  have h2 : ‖(pkg D).plus u w‖ ≤ C := (hp u w hw.ge).2.1
  have h4 : ‖((pkg D).minus u ξ)⁻¹‖ ≤ C := (hm u ξ hξ.ge).2.2
  have h3 := hE u ξ w z hξ hw hz
  rw [e]
  calc _ ≤ C * C * (CE * frequencyNorm D.recipe u ^ ε) * C :=
        mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hC.le) h3 (norm_nonneg _)
          (by positivity)) h4 (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem rawKernel_bound_explicit (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (u : Frequency D.recipe) (Z : ℝ), 2 ≤ Z → ∀ σ ∈ Icc (2 : ℝ) Scales.tailShift,
      ∀ t : ℝ × ℝ × ℝ,
        ‖rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
            ((σ : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
          Z ^ (Scales.kernelExponent 4 4 σ) * frequencyNorm D.recipe u ^ (-σ + ε) *
            (c * (((1 + |t.1|) ^ 2)⁻¹ * (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹))) := by
  obtain ⟨Cf, hCf0, hCf⟩ := rawFactor_norm_le D ε hε
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay 2 Scales.tailShift (by norm_num)
    (by norm_num [Scales.tailShift]) 4
  obtain ⟨CW, hCW⟩ := D.W1Hat_vertical_decay 4 4 le_rfl 2
  refine ⟨2 * Real.exp ((Scales.tailShift + 3) ^ 2) * |CM| * |CW| * Cf, by positivity, ?_⟩
  intro u Z hZ σ hσ t
  have hZ0 : 0 < Z := by linarith
  have hq0 : 0 < frequencyNorm D.recipe u := freq_pos D u
  have hσ1 : 2 ≤ σ := hσ.1
  have hσ2 : σ ≤ Scales.tailShift := hσ.2
  obtain ⟨t1, t2, t3⟩ := t
  dsimp only
  have hK := rawKernel_norm_eq D u hq0 ((4 : ℂ) + (t1 : ℂ) * I) σ 4 (t3, t2) Z hZ0
  dsimp only at hK
  simp only [Complex.ofReal_ofNat] at hK
  have hre1 : ((4 : ℂ) + (t1 : ℂ) * I).re = 4 := by simp
  have him1 : ((4 : ℂ) + (t1 : ℂ) * I).im = t1 := by simp
  have hw : ((4 : ℂ) + (t2 : ℂ) * I).re = 4 := by simp
  have hzre : ((σ : ℂ) + (t3 : ℂ) * I).re = σ := by simp
  have hzim : ((σ : ℂ) + (t3 : ℂ) * I).im = t3 := by simp
  rw [hre1] at hK
  rw [hK]
  have hE : Scales.kernelExponent 4 4 σ = Scales.xExponent / 2 + 4 - 1 + Scales.smoothingExponent * σ + Scales.yExponent * (4 - 1) := rfl
  rw [hE]
  have hrf : ‖rawFactor D u ((4 : ℂ) + (t1 : ℂ) * I) ((4 : ℂ) + (t2 : ℂ) * I)
      ((σ : ℂ) + (t3 : ℂ) * I)‖ ≤ Cf * frequencyNorm D.recipe u ^ ε :=
    hCf u _ _ _ hre1 hw (by rw [hzre]; exact hσ1)
  have hex := exp_norm_bound ((4 : ℂ) + (t1 : ℂ) * I) σ t3 ((Scales.tailShift + 3) ^ 2)
    (by rw [hre1]; nlinarith)
  rw [him1] at hex
  have hMb := hCM ((σ : ℂ) + (t3 : ℂ) * I) (by rw [hzre]; exact hσ1) (by rw [hzre]; exact hσ2)
  rw [hzim] at hMb
  have hWb := hCW ((4 : ℂ) + (t2 : ℂ) * I) (by rw [hw]) (by rw [hw])
  have hwim : ((4 : ℂ) + (t2 : ℂ) * I).im = t2 := by simp
  rw [hwim] at hWb
  have hMn : ‖D.M ((σ : ℂ) + (t3 : ℂ) * I)‖ ≤ |CM| * ((1 + |t3|) ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := mul_comm ‖D.M ((σ : ℂ) + (t3 : ℂ) * I)‖ ((1 + |t3|) ^ 4)
    linarith [le_abs_self CM]
  have hWn : ‖D.W1Hat ((4 : ℂ) + (t2 : ℂ) * I)‖ ≤ |CW| * ((1 + |t2|) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := mul_comm ‖D.W1Hat ((4 : ℂ) + (t2 : ℂ) * I)‖ ((1 + |t2|) ^ 2)
    linarith [le_abs_self CW]
  have hpeet : 1 + |t1| ≤ (1 + |t1 + t3|) * (1 + |t3|) := by
    have h : |t1| ≤ |t1 + t3| + |t3| := by
      rcases abs_cases t1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases abs_cases (t1 + t3) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
      rcases abs_cases t3 with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> linarith
    nlinarith [abs_nonneg (t1 + t3), abs_nonneg t3, mul_nonneg (abs_nonneg (t1 + t3)) (abs_nonneg t3)]
  have hkey := key_ineq (1 + |t1|) (1 + |t2|) (1 + |t3|) (t1 + t3)
    (by linarith [abs_nonneg t1]) (by linarith [abs_nonneg t2]) (by linarith [abs_nonneg t3])
    hpeet
  have hwm : WeightConvolution.weightModulus D ((4 : ℂ) + (t1 : ℂ) * I) σ 4 (t3, t2) ≤
      (2 * Real.exp ((Scales.tailShift + 3) ^ 2) * |CM| * |CW|) *
        (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + |t3|) ^ 2)⁻¹)) := by
    unfold WeightConvolution.weightModulus
    dsimp only
    simp only [Complex.ofReal_ofNat]
    rw [norm_mul, norm_mul]
    calc _ ≤ (Real.exp ((Scales.tailShift + 3) ^ 2) * Real.exp (-(t1 + t3) ^ 2)) *
          (|CM| * ((1 + |t3|) ^ 4)⁻¹) * (|CW| * ((1 + |t2|) ^ 2)⁻¹) :=
          mul_le_mul (mul_le_mul hex hMn (norm_nonneg _) (by positivity)) hWn
            (norm_nonneg _) (by positivity)
      _ = (Real.exp ((Scales.tailShift + 3) ^ 2) * |CM| * |CW|) *
          (Real.exp (-(t1 + t3) ^ 2) * (((1 + |t3|) ^ 4)⁻¹ * ((1 + |t2|) ^ 2)⁻¹)) := by ring
      _ ≤ (Real.exp ((Scales.tailShift + 3) ^ 2) * |CM| * |CW|) *
          (2 * (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + |t3|) ^ 2)⁻¹))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = _ := by ring
  calc _ ≤ Z ^ (Scales.xExponent / 2 + 4 - 1 + Scales.smoothingExponent * σ + Scales.yExponent * (4 - 1)) *
        frequencyNorm D.recipe u ^ (-σ) *
        ((2 * Real.exp ((Scales.tailShift + 3) ^ 2) * |CM| * |CW|) *
          (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + |t3|) ^ 2)⁻¹))) *
        (Cf * frequencyNorm D.recipe u ^ ε) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hwm (by positivity)) hrf (norm_nonneg _)
          (by positivity)
    _ = _ := by rw [Real.rpow_add hq0]; ring

theorem rawKernel_product_majorant (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 2 ≤ Z → ∀ (σ : ℝ), σ ∈ Icc (2 : ℝ) Scales.tailShift → ∀ ξ w z : ℂ,
        ξ.re = 4 → w.re = 4 → z.re = σ →
        ‖rawKernel D u ξ w z Z‖ ≤
          C * Z ^ (Scales.kernelExponent 4 4 σ) * frequencyNorm D.recipe u ^ (-σ + ε) *
            (((1 + |ξ.im|) ^ 2)⁻¹ * ((1 + |w.im|) ^ 2)⁻¹ * ((1 + |z.im|) ^ 2)⁻¹) := by
  obtain ⟨c, hc, h⟩ := rawKernel_bound_explicit D ε hε
  refine ⟨c + 1, by linarith, fun u _ Z hZ σ hσ ξ w z hξ hw hz => ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hq0 := freq_pos D u
  obtain ⟨t1, rfl⟩ : ∃ t1 : ℝ, ξ = (4 : ℂ) + (t1 : ℂ) * I :=
    ⟨ξ.im, by apply Complex.ext <;> simp [hξ]⟩
  obtain ⟨t2, rfl⟩ : ∃ t2 : ℝ, w = (4 : ℂ) + (t2 : ℂ) * I :=
    ⟨w.im, by apply Complex.ext <;> simp [hw]⟩
  obtain ⟨t3, rfl⟩ : ∃ t3 : ℝ, z = (σ : ℂ) + (t3 : ℂ) * I :=
    ⟨z.im, by apply Complex.ext <;> simp [hz]⟩
  have him1 : ((4 : ℂ) + (t1 : ℂ) * I).im = t1 := by simp
  have him2 : ((4 : ℂ) + (t2 : ℂ) * I).im = t2 := by simp
  have him3 : ((σ : ℂ) + (t3 : ℂ) * I).im = t3 := by simp
  rw [him1, him2, him3]
  have h0 := h u Z hZ σ hσ (t1, t2, t3)
  refine h0.trans ?_
  have hg : 0 ≤ ((1 + |t1|) ^ 2)⁻¹ * ((1 + |t2|) ^ 2)⁻¹ * ((1 + |t3|) ^ 2)⁻¹ := by positivity
  have hP : 0 ≤ Z ^ (Scales.kernelExponent 4 4 σ) * frequencyNorm D.recipe u ^ (-σ + ε) := by positivity
  calc Z ^ (Scales.kernelExponent 4 4 σ) * frequencyNorm D.recipe u ^ (-σ + ε) *
        (c * (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + |t3|) ^ 2)⁻¹)))
      = (c * (Z ^ (Scales.kernelExponent 4 4 σ) * frequencyNorm D.recipe u ^ (-σ + ε))) *
        (((1 + |t1|) ^ 2)⁻¹ * ((1 + |t2|) ^ 2)⁻¹ * ((1 + |t3|) ^ 2)⁻¹) := by ring
    _ ≤ ((c + 1) * (Z ^ (Scales.kernelExponent 4 4 σ) * frequencyNorm D.recipe u ^ (-σ + ε))) *
        (((1 + |t1|) ^ 2)⁻¹ * ((1 + |t2|) ^ 2)⁻¹ * ((1 + |t3|) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hg
    _ = _ := by ring

theorem rawKernel_integrable_line (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) (σ : ℝ)
    (hσ : σ ∈ Icc (2 : ℝ) Scales.tailShift) :
    Integrable (fun t : ℝ => rawKernel D u ξ w ((σ : ℂ) + (t : ℂ) * I) Z) := by
  obtain ⟨c, hc, h⟩ := rawKernel_bound_explicit D 1 one_pos
  have hZ0 : 0 < Z := by linarith
  have hσ1 : 2 ≤ σ := hσ.1
  obtain ⟨t1, rfl⟩ : ∃ t1 : ℝ, ξ = (4 : ℂ) + (t1 : ℂ) * I :=
    ⟨ξ.im, by apply Complex.ext <;> simp [hξ]⟩
  obtain ⟨t2, rfl⟩ : ∃ t2 : ℝ, w = (4 : ℂ) + (t2 : ℂ) * I :=
    ⟨w.im, by apply Complex.ext <;> simp [hw]⟩
  have hA := rawKernel_analytic_z D u hu Z hZ0 ((4 : ℂ) + (t1 : ℂ) * I)
    ((4 : ℂ) + (t2 : ℂ) * I) hξ hw
  have hcont : Continuous (fun t : ℝ =>
      rawKernel D u ((4 : ℂ) + (t1 : ℂ) * I) ((4 : ℂ) + (t2 : ℂ) * I)
        ((σ : ℂ) + (t : ℂ) * I) Z) :=
    hA.continuousOn.comp_continuous (by fun_prop) (fun t => by
      show 1 / 6 < ((σ : ℂ) + (t : ℂ) * I).re
      simp
      linarith)
  refine Integrable.mono'
    ((hI_inv_sq.const_mul (Z ^ (Scales.kernelExponent 4 4 σ) * frequencyNorm D.recipe u ^ (-σ + 1) *
      (c * (((1 + |t1|) ^ 2)⁻¹ * ((1 + |t2|) ^ 2)⁻¹))))) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have := h u Z hZ σ hσ (t1, t2, t)
  refine this.trans (le_of_eq ?_)
  simp only []
  ring

theorem rawKernel_horizontal_tendsto_zero (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4)
    (hw : w.re = 4) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (2 : ℝ)..Scales.tailShift,
        rawKernel D u ξ w ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I) Z) atTop (𝓝 0) := by
  obtain ⟨c, hc, h⟩ := rawKernel_bound_explicit D 1 one_pos
  have hZ0 : 0 < Z := by linarith
  have hq0 : 0 < frequencyNorm D.recipe u := freq_pos D u
  obtain ⟨t1, rfl⟩ : ∃ t1 : ℝ, ξ = (4 : ℂ) + (t1 : ℂ) * I :=
    ⟨ξ.im, by apply Complex.ext <;> simp [hξ]⟩
  obtain ⟨t2, rfl⟩ : ∃ t2 : ℝ, w = (4 : ℂ) + (t2 : ℂ) * I :=
    ⟨w.im, by apply Complex.ext <;> simp [hw]⟩
  have hcontf : ContinuousOn
      (fun x : ℝ => Z ^ (Scales.kernelExponent 4 4 x) * frequencyNorm D.recipe u ^ (-x + 1))
      (Icc (2 : ℝ) Scales.tailShift) := by
    apply Continuous.continuousOn
    apply Continuous.mul
    · exact Continuous.rpow continuous_const (by unfold Scales.kernelExponent; fun_prop)
        (fun _ => Or.inl hZ0.ne')
    · exact Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hq0.ne')
  obtain ⟨Mx, hMx⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontf
  set Kc : ℝ := Mx * (c * (((1 + |t1|) ^ 2)⁻¹ * ((1 + |t2|) ^ 2)⁻¹)) with hKc
  have h1 : Tendsto (fun T : ℝ => (1 + T) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have h2 := tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun T : ℝ => Kc * ((1 + T) ^ 2)⁻¹ * |Scales.tailShift - 2|) atTop (𝓝 0) := by
    have := (h2.const_mul Kc).mul_const |Scales.tailShift - 2|
    simpa [Function.comp_def] using this
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have habs : |ε * T| = T := by
    rcases hε with rfl | rfl <;> simp [abs_of_nonneg hT]
  have hle : (2 : ℝ) ≤ Scales.tailShift := by norm_num [Scales.tailShift]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
  rw [Set.uIoc_of_le hle] at hx
  have hxI : x ∈ Icc (2 : ℝ) Scales.tailShift := ⟨hx.1.le, hx.2⟩
  have hb := h u Z hZ x hxI (t1, t2, ε * T)
  simp only [habs] at hb
  have hm := hMx x hxI
  rw [Real.norm_eq_abs] at hm
  have hm2 := le_abs_self (Z ^ (Scales.kernelExponent 4 4 x) * frequencyNorm D.recipe u ^ (-x + 1))
  refine hb.trans ?_
  have hG : 0 ≤ c * (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + T) ^ 2)⁻¹)) := by
    positivity
  calc Z ^ (Scales.kernelExponent 4 4 x) * frequencyNorm D.recipe u ^ (-x + 1) *
        (c * (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + T) ^ 2)⁻¹)))
      ≤ Mx * (c * (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + T) ^ 2)⁻¹))) :=
        mul_le_mul_of_nonneg_right (hm2.trans hm) hG
    _ = Kc * ((1 + T) ^ 2)⁻¹ := by rw [hKc]; ring

theorem Iz_shift_two_R (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) :
    Iz D u ξ w 2 Z = Iz D u ξ w Scales.tailShift Z := by
  show comparisonVerticalIntegral 2 (fun z => rawKernel D u ξ w z Z) =
    comparisonVerticalIntegral Scales.tailShift (fun z => rawKernel D u ξ w z Z)
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hA := rawKernel_analytic_z D u hu Z hZ0 ξ w hξ hw
  have hR : (3 : ℝ) < Scales.tailShift := by norm_num [Scales.tailShift]
  have hcont : ContinuousAt (fun z : ℂ => rawKernel D u ξ w z Z) 3 :=
    (hA 3 (by simp only [Set.mem_setOf_eq]; norm_num)).continuousAt
  have hres : Tendsto (fun z : ℂ => (z - 3) * rawKernel D u ξ w z Z) (𝓝[≠] (3 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => (z - 3) * rawKernel D u ξ w z Z) (𝓝 (3 : ℂ))
        (𝓝 ((3 - 3) * rawKernel D u ξ w 3 Z)) :=
      ((continuous_id.sub continuous_const).continuousAt.mul hcont).tendsto
    simp only [sub_self, zero_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hf : DifferentiableOn ℂ (fun z : ℂ => rawKernel D u ξ w z Z)
      (comparisonClosedStrip 2 Scales.tailShift \ {(3 : ℂ)}) := by
    intro z hz
    have hz1 : z ∈ {z : ℂ | 1 / 6 < z.re} := by
      have h1 : (2 : ℝ) ≤ z.re := hz.1.1
      show 1 / 6 < z.re
      linarith
    exact ((hA z hz1).differentiableAt).differentiableWithinAt
  have hbot0 := rawKernel_horizontal_tendsto_zero D u hu Z hZ ξ w hξ hw (-1) (Or.inr rfl)
  have htop0 := rawKernel_horizontal_tendsto_zero D u hu Z hZ ξ w hξ hw 1 (Or.inl rfl)
  simp only [neg_one_mul] at hbot0
  simp only [one_mul] at htop0
  have key := DedekindZetaZeroFree.Quantitative.SimplePoleVerticalShift.verticalIntegral_sub_eq_residue
    (a := 2) (b := Scales.tailShift) (p := (3 : ℂ)) (f := fun z : ℂ => rawKernel D u ξ w z Z)
    (res := 0)
    (by norm_num) (by norm_num; exact hR) hf hres
    (rawKernel_integrable_line D u hu Z hZ ξ w hξ hw 2 ⟨le_rfl, by linarith⟩)
    (rawKernel_integrable_line D u hu Z hZ ξ w hξ hw Scales.tailShift ⟨by linarith, le_rfl⟩)
    hbot0 htop0
  linear_combination -key

private lemma cvi_congr {σ : ℝ} {f g : ℂ → ℂ}
    (h : ∀ t : ℝ, f ((σ : ℂ) + (t : ℂ) * Complex.I) = g ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    comparisonVerticalIntegral σ f = comparisonVerticalIntegral σ g := by
  unfold comparisonVerticalIntegral
  simp only [h]

theorem initialRowIntegral_eq_triple_R (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 2 ≤ Z) :
    initialRowIntegral D u Z = triple D u 4 4 Scales.tailShift Z := by
  unfold initialRowIntegral triple
  refine cvi_congr (fun t => ?_)
  unfold Iwz
  refine cvi_congr (fun s => ?_)
  exact Iz_shift_two_R D u hu Z hZ _ _ (by simp) (by simp)

theorem triple_norm_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 2 ≤ Z →
      Integrable (fun t : ℝ × ℝ × ℝ =>
        rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z) ∧
      ∫ t : ℝ × ℝ × ℝ, ‖rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
        C * Z ^ (Scales.kernelExponent 4 4 Scales.tailShift) * frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) := by
  obtain ⟨c, hc, h⟩ := rawKernel_bound_explicit D ε hε
  obtain ⟨I0, hI0⟩ : ∃ I0 : ℝ, I0 = ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ := ⟨_, rfl⟩
  have hI0nn : 0 ≤ I0 := by
    rw [hI0]; exact integral_nonneg (fun x => by positivity)
  obtain ⟨Cm, hCm, -, H2, -⟩ := right_bounds D
  refine ⟨c * I0 ^ 3 + 1, by positivity, ?_⟩
  intro u hu Z hZ
  have hZ0 : 0 < Z := by linarith
  have hq0 : 0 < frequencyNorm D.recipe u := freq_pos D u
  have hRmem : Scales.tailShift ∈ Icc (2 : ℝ) Scales.tailShift := ⟨by norm_num [Scales.tailShift], le_rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ,
      B = Z ^ (Scales.kernelExponent 4 4 Scales.tailShift) * frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBd]; positivity
  have hgint : Integrable (fun t : ℝ × ℝ × ℝ => B * (c * (((1 + |t.1|) ^ 2)⁻¹ *
      (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹)))) :=
    ((hI_inv_sq.mul_prod (hI_inv_sq.mul_prod hI_inv_sq)).const_mul c).const_mul B
  have hR6 : (1 / 6 : ℝ) < Scales.tailShift := by norm_num [Scales.tailShift]
  have hd : ∀ t : ℝ × ℝ × ℝ, DifferentiableAt ℂ
      (fun p : ℂ × ℂ × ℂ => rawKernel D u p.1 p.2.1 p.2.2 Z)
      (((4 : ℂ) + (t.1 : ℂ) * I, (4 : ℂ) + (t.2.1 : ℂ) * I,
        ((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) : ℂ × ℂ × ℂ) := by
    intro t
    have h1 : ((4 : ℂ) + (t.1 : ℂ) * I).re = 4 := by simp
    have h2 : ((4 : ℂ) + (t.2.1 : ℂ) * I).re = 4 := by simp
    have h3 : (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I).re = Scales.tailShift := by simp
    have hz : (1 / 6 : ℝ) < (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I).re := by
      rw [h3]; exact hR6
    exact RawKernelRegularity31.rawKernel_differentiableAt D u hu Z hZ0 _
      (mem_OmegaStar_line _ h1 h2 hz) hz (H2 u _ h1.ge).1
  have hmap : Continuous (fun t : ℝ × ℝ × ℝ =>
      (((4 : ℂ) + (t.1 : ℂ) * I, (4 : ℂ) + (t.2.1 : ℂ) * I,
        ((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) : ℂ × ℂ × ℂ)) := by fun_prop
  have hcont : Continuous (fun t : ℝ × ℝ × ℝ =>
      rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z) := by
    refine continuous_iff_continuousAt.2 (fun t => ?_)
    exact ContinuousAt.comp
      (g := fun p : ℂ × ℂ × ℂ => rawKernel D u p.1 p.2.1 p.2.2 Z)
      (f := fun t : ℝ × ℝ × ℝ =>
        (((4 : ℂ) + (t.1 : ℂ) * I, (4 : ℂ) + (t.2.1 : ℂ) * I,
          ((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) : ℂ × ℂ × ℂ))
      (x := t) (hd t).continuousAt hmap.continuousAt
  have hbound : ∀ t : ℝ × ℝ × ℝ,
      ‖rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
      B * (c * (((1 + |t.1|) ^ 2)⁻¹ * (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹))) := by
    intro t
    rw [hBd]
    exact h u Z hZ Scales.tailShift hRmem t
  have hKint : Integrable (fun t : ℝ × ℝ × ℝ =>
      rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z) :=
    Integrable.mono' hgint hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  refine ⟨hKint, ?_⟩
  have e2 : ∫ y : ℝ × ℝ, ((1 + |y.1|) ^ 2)⁻¹ * ((1 + |y.2|) ^ 2)⁻¹ = I0 * I0 := by
    rw [hI0]
    exact integral_prod_mul (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹)
  have e3 : ∫ t : ℝ × ℝ × ℝ, ((1 + |t.1|) ^ 2)⁻¹ *
      (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹) = I0 * (I0 * I0) := by
    have := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
      (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹)
      (fun y : ℝ × ℝ => ((1 + |y.1|) ^ 2)⁻¹ * ((1 + |y.2|) ^ 2)⁻¹)
    rw [e2, ← hI0] at this
    exact this
  calc ∫ t : ℝ × ℝ × ℝ, ‖rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z‖
      ≤ ∫ t : ℝ × ℝ × ℝ, B * (c * (((1 + |t.1|) ^ 2)⁻¹ *
          (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹))) :=
        integral_mono hKint.norm hgint hbound
    _ = B * (c * I0 ^ 3) := by
        rw [integral_const_mul, integral_const_mul, e3]; ring
    _ ≤ B * (c * I0 ^ 3 + 1) := mul_le_mul_of_nonneg_left (by linarith) hB0
    _ = _ := by rw [hBd]; ring

end

end DedekindZetaZeroFree.Quantitative.RawLargeZControls31
