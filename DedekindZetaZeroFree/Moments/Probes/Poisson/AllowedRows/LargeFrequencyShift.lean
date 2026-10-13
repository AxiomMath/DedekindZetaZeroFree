module

public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelGrowth
public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LargeRowShift

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel MeasureTheory Set Filter Complex
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem K_analytic_z (u : D.Row) (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4)
    (hw : w.re = 4) :
    AnalyticOnNhd ℂ (fun z : ℂ => K D u ξ w z Z) {z : ℂ | 1 / 6 < z.re} := by
  have hq0 : 0 < D.q u := PoissonInitialBridge.q_pos D u
  have hopen : IsOpen {z : ℂ | 1 / 6 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro z hz
  have hz' : (1 / 6 : ℝ) < z.re := hz
  apply DifferentiableAt.differentiableWithinAt
  have hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar := by
    show 0 < ξ.re ∧ 0 < w.re ∧ 0 < z.re ∧ 1 < 6 * z.re + w.re ∧ 1 < ξ.re + 6 * z.re ∧
      1 < ξ.re + w.re ∧ 2 < ξ.re + w.re + 6 * z.re ∧ 5 < 6 * ξ.re + 6 * z.re ∧
      1 / 2 < ξ.re ∧ 2 < 3 * ξ.re ∧ 5 / 2 < 3 * ξ.re + w.re
    rw [hξ, hw]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hHu : DifferentiableAt ℂ (fun z : ℂ => EulerDomain.Hu D u ξ w z) z := by
    have h1 := (EulerDomain.Hu_normal_convergence D u).2.2.1
    have h2 : DifferentiableAt ℂ
        (fun p : EulerDomain.Coordinates => EulerDomain.Hu D u p.1 p.2.1 p.2.2) (ξ, w, z) :=
      h1.differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
    have h3 : DifferentiableAt ℂ (fun z : ℂ => ((ξ, w, z) : EulerDomain.Coordinates)) z :=
      (differentiableAt_const ξ).prodMk ((differentiableAt_const w).prodMk differentiableAt_id)
    exact h2.comp z h3
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hqc : (D.q u : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hzeta : DifferentiableAt ℂ (fun z : ℂ => D.zetaSCont (6 * z)) z := by
    have hs : (6 : ℂ) * z ∈ ({s : ℂ | 0 < s.re} \ {1} : Set ℂ) := by
      refine ⟨?_, ?_⟩
      · show 0 < ((6 : ℂ) * z).re
        have : ((6 : ℂ) * z).re = 6 * z.re := by simp
        rw [this]; linarith
      · intro h
        have h' := congrArg Complex.re (show (6 : ℂ) * z = 1 from h)
        have : ((6 : ℂ) * z).re = 6 * z.re := by simp
        rw [this] at h'
        simp at h'
        linarith
    exact ((RightHeckeBounds.zetaSCont_analyticOnNhd D) _ hs).differentiableAt.comp z
      (by fun_prop)
  have hM : DifferentiableAt ℂ D.M z :=
    D.M_differentiableOn.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < z.re by linarith))
  simp only [K, kernelWith, rowFactor]
  refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
    (DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) hM) (differentiableAt_const _)) ?_) ?_
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hZc)
  · fun_prop
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hqc)
  · exact DifferentiableAt.mul (DifferentiableAt.div_const
      (DifferentiableAt.mul hzeta (differentiableAt_const _)) _) hHu

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

private theorem K_bound_explicit (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (u : D.Row) (Z : ℝ), 2 ≤ Z → ∀ σ ∈ Icc (2 : ℝ) Scales.tailShift,
      ∀ t : ℝ × ℝ × ℝ,
        ‖K D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
            ((σ : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
          Z ^ (Scales.kernelExponent 4 4 σ) * D.q u ^ (-σ + ε) *
            (c * (((1 + |t.1|) ^ 2)⁻¹ * (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹))) := by
  obtain ⟨Cz, hCz0, hCz⟩ := RightHeckeBounds.zetaSCont_norm_le_right D 2 (by norm_num)
  obtain ⟨Cp, hCp0, hCp⟩ := RightHeckeBounds.Lpsi_norm_le_right D 2 (by norm_num)
  obtain ⟨Cl, hCl0, hCl⟩ := RightHeckeBounds.Llam_inv_norm_le_right D 2 (by norm_num)
  obtain ⟨CH, hCH0, hCH⟩ := EulerSubpower.Hu_subpower_boxes D ε hε
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay 2 Scales.tailShift (by norm_num)
    (by norm_num [Scales.tailShift]) 4
  obtain ⟨CW, hCW⟩ := D.W1Hat_vertical_decay 4 4 le_rfl 2
  refine ⟨2 * Real.exp ((Scales.tailShift + 3) ^ 2) * |CM| * |CW| * Cz * Cp * Cl * CH,
    by positivity, ?_⟩
  intro u Z hZ σ hσ t
  have hZ0 : 0 < Z := by linarith
  have hq0 : 0 < D.q u := PoissonInitialBridge.q_pos D u
  have hσ1 : 2 ≤ σ := hσ.1
  have hσ2 : σ ≤ Scales.tailShift := hσ.2
  obtain ⟨t1, t2, t3⟩ := t
  dsimp only
  have hK := RowKernelGrowth.K_norm_eq D u hq0 ((4 : ℂ) + (t1 : ℂ) * I) σ 4 (t3, t2) Z hZ0
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

  have hrf : ‖rowFactor D u ((4 : ℂ) + (t1 : ℂ) * I) ((4 : ℂ) + (t2 : ℂ) * I)
      ((σ : ℂ) + (t3 : ℂ) * I)‖ ≤ Cz * Cp * Cl * (CH * D.q u ^ ε) := by
    have e : ‖rowFactor D u ((4 : ℂ) + (t1 : ℂ) * I) ((4 : ℂ) + (t2 : ℂ) * I)
        ((σ : ℂ) + (t3 : ℂ) * I)‖ =
        ‖D.zetaSCont (6 * ((σ : ℂ) + (t3 : ℂ) * I))‖ * ‖D.Lpsi u ((4 : ℂ) + (t2 : ℂ) * I)‖ *
          ‖(D.Llam u ((4 : ℂ) + (t1 : ℂ) * I))⁻¹‖ *
          ‖EulerDomain.Hu D u ((4 : ℂ) + (t1 : ℂ) * I) ((4 : ℂ) + (t2 : ℂ) * I)
            ((σ : ℂ) + (t3 : ℂ) * I)‖ := by
      unfold rowFactor
      simp only [div_eq_mul_inv, norm_mul]
    have h6 : (6 * ((σ : ℂ) + (t3 : ℂ) * I)).re = 6 * σ := by simp
    have hz1 := hCz (6 * ((σ : ℂ) + (t3 : ℂ) * I)) (by rw [h6]; linarith)
    have hp1 := hCp u ((4 : ℂ) + (t2 : ℂ) * I) (by rw [hw]; norm_num)
    have hl1 := hCl u ((4 : ℂ) + (t1 : ℂ) * I) (by rw [hre1]; norm_num)
    have hp : (((4 : ℂ) + (t1 : ℂ) * I, (4 : ℂ) + (t2 : ℂ) * I, (σ : ℂ) + (t3 : ℂ) * I) :
        EulerDomain.Coordinates) ∈ EulerDomain.boxes := by
      refine Or.inr ?_
      show Scales.rightLine ≤ ((4 : ℂ) + (t1 : ℂ) * I).re ∧ (1 : ℝ) ≤ ((4 : ℂ) + (t2 : ℂ) * I).re ∧
        (1 / 20 : ℝ) ≤ ((σ : ℂ) + (t3 : ℂ) * I).re
      rw [hre1, hw, hzre]
      refine ⟨?_, by norm_num, by linarith⟩
      norm_num [Scales.rightLine, Scales.contourOffset]
    have hH := (hCH u _ hp).2
    rw [e]
    have hB : 0 ≤ Cz * Cp * Cl := by positivity
    calc _ ≤ Cz * Cp * Cl * (CH * D.q u ^ ε) :=
          mul_le_mul (mul_le_mul (mul_le_mul hz1 hp1 (norm_nonneg _) hCz0.le) hl1
            (norm_nonneg _) (by positivity)) hH (norm_nonneg _) hB
      _ = _ := rfl

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
  calc _ ≤ Z ^ (Scales.xExponent / 2 + 4 - 1 + Scales.smoothingExponent * σ + Scales.yExponent * (4 - 1)) * D.q u ^ (-σ) *
        ((2 * Real.exp ((Scales.tailShift + 3) ^ 2) * |CM| * |CW|) *
          (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + |t3|) ^ 2)⁻¹))) *
        (Cz * Cp * Cl * (CH * D.q u ^ ε)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hwm (by positivity)) hrf (norm_nonneg _)
          (by positivity)
    _ = _ := by rw [Real.rpow_add hq0]; ring

private lemma mem_OmegaStar_line (p : EulerDomain.Coordinates) (h1 : p.1.re = 4)
    (h2 : p.2.1.re = 4) (h3 : 1 / 6 < p.2.2.re) : p ∈ EulerDomain.OmegaStar := by
  show 0 < p.1.re ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re ∧ 1 < 6 * p.2.2.re + p.2.1.re ∧
    1 < p.1.re + 6 * p.2.2.re ∧ 1 < p.1.re + p.2.1.re ∧ 2 < p.1.re + p.2.1.re + 6 * p.2.2.re ∧
    5 < 6 * p.1.re + 6 * p.2.2.re ∧ 1 / 2 < p.1.re ∧ 2 < 3 * p.1.re ∧
    5 / 2 < 3 * p.1.re + p.2.1.re
  rw [h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem re_facts (t : ℝ × ℝ × ℝ) :
    ((4 : ℂ) + (t.1 : ℂ) * I).re = 4 ∧ ((4 : ℂ) + (t.2.1 : ℂ) * I).re = 4 ∧
    (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I).re = Scales.tailShift ∧
    (6 * (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I)).re = 6 * Scales.tailShift := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

private theorem cont_M (u : D.Row) :
    Continuous fun t : ℝ × ℝ × ℝ => D.M (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) := by
  have hR0 : (0 : ℝ) < Scales.tailShift := by norm_num [Scales.tailShift]
  refine D.M_differentiableOn.continuousOn.comp_continuous (by fun_prop) (fun t => ?_)
  have := (re_facts t).2.2.1
  show 0 < (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I).re
  rw [this]; exact hR0

private theorem meas_W :
    Measurable fun t : ℝ × ℝ × ℝ => D.W1Hat ((4 : ℂ) + (t.2.1 : ℂ) * I) :=
  (PrincipalMellinComparison.principal_real_weight_measurable D.recipe).comp
    (Continuous.measurable (by fun_prop))

private theorem cont_zeta :
    Continuous fun t : ℝ × ℝ × ℝ =>
      D.zetaSCont (6 * (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I)) := by
  refine (RightHeckeBounds.zetaSCont_analyticOnNhd D).continuousOn.comp_continuous
      (by fun_prop) (fun t => ?_)
  have h6 := (re_facts t).2.2.2
  refine ⟨?_, ?_⟩
  · show 0 < (6 * (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I)).re
    rw [h6]; norm_num [Scales.tailShift]
  · intro h
    have h1 : (6 * (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I)) = 1 := h
    have h2 := congrArg Complex.re h1
    rw [h6] at h2
    norm_num [Scales.tailShift] at h2

private theorem cont_Lpsi (u : D.Row) :
    Continuous fun t : ℝ × ℝ × ℝ => D.Lpsi u ((4 : ℂ) + (t.2.1 : ℂ) * I) := by
  refine (D.Lpsi_analyticOnNhd u).continuousOn.comp_continuous (by fun_prop) (fun t => ?_)
  have h4 := (re_facts t).2.1
  refine ⟨?_, ?_⟩
  · show 0 < ((4 : ℂ) + (t.2.1 : ℂ) * I).re
    rw [h4]; norm_num
  · intro h
    have h1 : ((4 : ℂ) + (t.2.1 : ℂ) * I) = 1 := h
    have h2 := congrArg Complex.re h1
    rw [h4] at h2
    norm_num at h2

private theorem cont_Llam (u : D.Row) :
    Continuous fun t : ℝ × ℝ × ℝ => D.Llam u ((4 : ℂ) + (t.1 : ℂ) * I) := by
  refine (D.Llam_analyticOnNhd u).continuousOn.comp_continuous (by fun_prop) (fun t => ?_)
  have h4 := (re_facts t).1
  refine ⟨?_, ?_⟩
  · show 0 < ((4 : ℂ) + (t.1 : ℂ) * I).re
    rw [h4]; norm_num
  · intro h
    have h1 : ((4 : ℂ) + (t.1 : ℂ) * I) = 1 := h
    have h2 := congrArg Complex.re h1
    rw [h4] at h2
    norm_num at h2

private theorem cont_Hu (u : D.Row) :
    Continuous fun t : ℝ × ℝ × ℝ =>
      EulerDomain.Hu D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) := by
  have hc : Continuous fun t : ℝ × ℝ × ℝ =>
      (((4 : ℂ) + (t.1 : ℂ) * I, (4 : ℂ) + (t.2.1 : ℂ) * I,
        ((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) : EulerDomain.Coordinates) := by fun_prop
  have hHu := (EulerDomain.Hu_normal_convergence D u).2.2.1.continuousOn
  have hmem : ∀ t : ℝ × ℝ × ℝ, (((4 : ℂ) + (t.1 : ℂ) * I, (4 : ℂ) + (t.2.1 : ℂ) * I,
        ((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) : EulerDomain.Coordinates) ∈
        EulerDomain.OmegaStar := by
    intro t
    obtain ⟨h1, h2, h3, -⟩ := re_facts t
    refine mem_OmegaStar_line _ h1 h2 ?_
    show 1 / 6 < (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I).re
    rw [h3]; norm_num [Scales.tailShift]
  have hcomp : Continuous ((fun p : EulerDomain.Coordinates =>
      EulerDomain.Hu D u p.1 p.2.1 p.2.2) ∘ fun t : ℝ × ℝ × ℝ =>
      (((4 : ℂ) + (t.1 : ℂ) * I, (4 : ℂ) + (t.2.1 : ℂ) * I,
        ((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) : EulerDomain.Coordinates)) :=
    hHu.comp_continuous hc hmem
  exact hcomp

private theorem K_measurable_R (u : D.Row) (Z : ℝ) (hZ : 0 < Z) :
    Measurable (fun t : ℝ × ℝ × ℝ =>
      K D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z) := by
  have hq0 : 0 < D.q u := PoissonInitialBridge.q_pos D u
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hqc : (D.q u : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have f1 : Measurable fun t : ℝ × ℝ × ℝ => (Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) +
      ((4 : ℂ) + (t.1 : ℂ) * I) - 1 + (Scales.smoothingExponent : ℂ) * (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) +
      (Scales.yExponent : ℂ) * (((4 : ℂ) + (t.2.1 : ℂ) * I) - 1)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl hZc)).measurable
  have f2 : Measurable fun t : ℝ × ℝ × ℝ => Complex.exp
      ((((4 : ℂ) + (t.1 : ℂ) * I) + (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) - 1) ^ 2) :=
    Continuous.measurable (by fun_prop)
  have f3 : Measurable fun t : ℝ × ℝ × ℝ =>
      (D.q u : ℂ) ^ (-(((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl hqc)).measurable
  have f4 : Measurable fun t : ℝ × ℝ × ℝ =>
      D.zetaSCont (6 * (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I)) * D.Lpsi u ((4 : ℂ) + (t.2.1 : ℂ) * I) /
        D.Llam u ((4 : ℂ) + (t.1 : ℂ) * I) *
      EulerDomain.Hu D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) :=
    Measurable.mul (Measurable.div (Measurable.mul (cont_zeta D).measurable
      (cont_Lpsi D u).measurable) (cont_Llam D u).measurable) (cont_Hu D u).measurable
  exact ((((f1.mul f2).mul (cont_M D u).measurable).mul (meas_W D)).mul f3).mul f4

theorem K_majorant_right (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ × ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧
      ∀ (u : D.Row) (Z : ℝ), 2 ≤ Z → ∀ σ ∈ Icc (2 : ℝ) Scales.tailShift, ∀ t : ℝ × ℝ × ℝ,
        ‖K D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
            ((σ : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
          Z ^ (Scales.kernelExponent 4 4 σ) * D.q u ^ (-σ + ε) * g t := by
  obtain ⟨c, hc, h⟩ := K_bound_explicit D ε hε
  refine ⟨fun t => c * (((1 + |t.1|) ^ 2)⁻¹ * (((1 + |t.2.1|) ^ 2)⁻¹ *
    ((1 + |t.2.2|) ^ 2)⁻¹)), ?_, fun p => by positivity, ?_⟩
  · exact (hI_inv_sq.mul_prod (hI_inv_sq.mul_prod hI_inv_sq)).const_mul c
  · intro u Z hZ σ hσ t
    exact h u Z hZ σ hσ t

theorem K_integrable_line (u : D.Row) (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4)
    (hw : w.re = 4) (σ : ℝ) (hσ : σ ∈ Icc (2 : ℝ) Scales.tailShift) :
    Integrable (fun t : ℝ => K D u ξ w ((σ : ℂ) + (t : ℂ) * I) Z) := by
  obtain ⟨c, hc, h⟩ := K_bound_explicit D 1 one_pos
  have hZ0 : 0 < Z := by linarith
  have hσ1 : 2 ≤ σ := hσ.1
  obtain ⟨t1, rfl⟩ : ∃ t1 : ℝ, ξ = (4 : ℂ) + (t1 : ℂ) * I :=
    ⟨ξ.im, by apply Complex.ext <;> simp [hξ]⟩
  obtain ⟨t2, rfl⟩ : ∃ t2 : ℝ, w = (4 : ℂ) + (t2 : ℂ) * I :=
    ⟨w.im, by apply Complex.ext <;> simp [hw]⟩
  have hA := K_analytic_z D u Z hZ0 ((4 : ℂ) + (t1 : ℂ) * I) ((4 : ℂ) + (t2 : ℂ) * I) hξ hw
  have hcont : Continuous (fun t : ℝ =>
      K D u ((4 : ℂ) + (t1 : ℂ) * I) ((4 : ℂ) + (t2 : ℂ) * I) ((σ : ℂ) + (t : ℂ) * I) Z) :=
    hA.continuousOn.comp_continuous (by fun_prop) (fun t => by
      show 1 / 6 < ((σ : ℂ) + (t : ℂ) * I).re
      simp
      linarith)
  refine Integrable.mono'
    ((hI_inv_sq.const_mul (Z ^ (Scales.kernelExponent 4 4 σ) * D.q u ^ (-σ + 1) *
      (c * (((1 + |t1|) ^ 2)⁻¹ * ((1 + |t2|) ^ 2)⁻¹))))) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have := h u Z hZ σ hσ (t1, t2, t)
  refine this.trans (le_of_eq ?_)
  simp only []
  ring

theorem K_horizontal_tendsto_zero (u : D.Row) (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4)
    (hw : w.re = 4) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (2 : ℝ)..Scales.tailShift,
        K D u ξ w ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I) Z) atTop (𝓝 0) := by
  obtain ⟨c, hc, h⟩ := K_bound_explicit D 1 one_pos
  have hZ0 : 0 < Z := by linarith
  have hq0 : 0 < D.q u := PoissonInitialBridge.q_pos D u
  obtain ⟨t1, rfl⟩ : ∃ t1 : ℝ, ξ = (4 : ℂ) + (t1 : ℂ) * I :=
    ⟨ξ.im, by apply Complex.ext <;> simp [hξ]⟩
  obtain ⟨t2, rfl⟩ : ∃ t2 : ℝ, w = (4 : ℂ) + (t2 : ℂ) * I :=
    ⟨w.im, by apply Complex.ext <;> simp [hw]⟩
  have hcontf : ContinuousOn (fun x : ℝ => Z ^ (Scales.kernelExponent 4 4 x) * D.q u ^ (-x + 1))
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
  have hm2 := le_abs_self (Z ^ (Scales.kernelExponent 4 4 x) * D.q u ^ (-x + 1))
  refine hb.trans ?_
  have hG : 0 ≤ c * (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + T) ^ 2)⁻¹)) := by
    positivity
  calc Z ^ (Scales.kernelExponent 4 4 x) * D.q u ^ (-x + 1) *
        (c * (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + T) ^ 2)⁻¹)))
      ≤ Mx * (c * (((1 + |t1|) ^ 2)⁻¹ * (((1 + |t2|) ^ 2)⁻¹ * ((1 + T) ^ 2)⁻¹))) :=
        mul_le_mul_of_nonneg_right (hm2.trans hm) hG
    _ = Kc * ((1 + T) ^ 2)⁻¹ := by rw [hKc]; ring

theorem large_row_z_shift (u : D.Row) (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4)
    (hw : w.re = 4) :
    comparisonVerticalIntegral 2 (fun z => K D u ξ w z Z) =
      comparisonVerticalIntegral Scales.tailShift (fun z => K D u ξ w z Z) := by
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hA := K_analytic_z D u Z hZ0 ξ w hξ hw
  have hR : (3 : ℝ) < Scales.tailShift := by norm_num [Scales.tailShift]
  have h2 : (2 : ℝ) < 3 := by norm_num
  have hcont : ContinuousAt (fun z : ℂ => K D u ξ w z Z) 3 :=
    (hA 3 (by simp only [Set.mem_setOf_eq]; norm_num)).continuousAt
  have hres : Tendsto (fun z : ℂ => (z - 3) * K D u ξ w z Z) (𝓝[≠] (3 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => (z - 3) * K D u ξ w z Z) (𝓝 (3 : ℂ))
        (𝓝 ((3 - 3) * K D u ξ w 3 Z)) :=
      ((continuous_id.sub continuous_const).continuousAt.mul hcont).tendsto
    simp only [sub_self, zero_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hf : DifferentiableOn ℂ (fun z : ℂ => K D u ξ w z Z)
      (comparisonClosedStrip 2 Scales.tailShift \ {(3 : ℂ)}) := by
    intro z hz
    have hz1 : z ∈ {z : ℂ | 1 / 6 < z.re} := by
      have h1 : (2 : ℝ) ≤ z.re := hz.1.1
      show 1 / 6 < z.re
      linarith
    exact ((hA z hz1).differentiableAt).differentiableWithinAt
  have hbot0 := K_horizontal_tendsto_zero D u Z hZ ξ w hξ hw (-1) (Or.inr rfl)
  have htop0 := K_horizontal_tendsto_zero D u Z hZ ξ w hξ hw 1 (Or.inl rfl)
  simp only [neg_one_mul] at hbot0
  simp only [one_mul] at htop0
  have key := DedekindZetaZeroFree.Quantitative.SimplePoleVerticalShift.verticalIntegral_sub_eq_residue
    (a := 2) (b := Scales.tailShift) (p := (3 : ℂ)) (f := fun z : ℂ => K D u ξ w z Z) (res := 0)
    (by norm_num) (by norm_num; exact hR) hf hres
    (K_integrable_line D u Z hZ ξ w hξ hw 2 ⟨le_rfl, by linarith⟩)
    (K_integrable_line D u Z hZ ξ w hξ hw Scales.tailShift ⟨by linarith, le_rfl⟩)
    hbot0 htop0
  linear_combination -key

theorem large_row_triple_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : D.Row) (Z : ℝ), 2 ≤ Z →
      Integrable (fun t : ℝ × ℝ × ℝ =>
        K D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z) ∧
      ∫ t : ℝ × ℝ × ℝ, ‖K D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
        C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * D.q u ^ (-Scales.tailShift + ε) := by
  obtain ⟨c, hc, h⟩ := K_bound_explicit D ε hε
  obtain ⟨I0, hI0⟩ : ∃ I0 : ℝ, I0 = ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ := ⟨_, rfl⟩
  have hI0nn : 0 ≤ I0 := by
    rw [hI0]; exact integral_nonneg (fun x => by positivity)
  refine ⟨c * I0 ^ 3 + 1, by positivity, ?_⟩
  intro u Z hZ
  have hZ0 : 0 < Z := by linarith
  have hq0 : 0 < D.q u := PoissonInitialBridge.q_pos D u
  have hRmem : Scales.tailShift ∈ Icc (2 : ℝ) Scales.tailShift := ⟨by norm_num [Scales.tailShift], le_rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = Z ^ (Scales.kernelExponent 4 4 Scales.tailShift) * D.q u ^ (-Scales.tailShift + ε) :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBd]; positivity
  have hgint : Integrable (fun t : ℝ × ℝ × ℝ => B * (c * (((1 + |t.1|) ^ 2)⁻¹ *
      (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹)))) :=
    ((hI_inv_sq.mul_prod (hI_inv_sq.mul_prod hI_inv_sq)).const_mul c).const_mul B
  have hmeas := K_measurable_R D u Z hZ0
  have hbound : ∀ t : ℝ × ℝ × ℝ,
      ‖K D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
      B * (c * (((1 + |t.1|) ^ 2)⁻¹ * (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹))) := by
    intro t
    rw [hBd]
    exact h u Z hZ Scales.tailShift hRmem t
  have hKint : Integrable (fun t : ℝ × ℝ × ℝ =>
      K D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
        (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z) :=
    Integrable.mono' hgint hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
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
  have hE : Scales.kernelExponent 4 4 Scales.tailShift = (44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift := by
    norm_num [Scales.kernelExponent, Scales.xExponent, Scales.yExponent, Scales.smoothingExponent, Scales.tailShift]
  calc ∫ t : ℝ × ℝ × ℝ, ‖K D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z‖
      ≤ ∫ t : ℝ × ℝ × ℝ, B * (c * (((1 + |t.1|) ^ 2)⁻¹ *
          (((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹))) :=
        integral_mono hKint.norm hgint hbound
    _ = B * (c * I0 ^ 3) := by
        rw [integral_const_mul, integral_const_mul, e3]; ring
    _ ≤ (Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) * D.q u ^ (-Scales.tailShift + ε)) *
          (c * I0 ^ 3 + 1) := by
        rw [hBd, hE]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end

end DedekindZetaZeroFree.Quantitative.LargeRowShift
