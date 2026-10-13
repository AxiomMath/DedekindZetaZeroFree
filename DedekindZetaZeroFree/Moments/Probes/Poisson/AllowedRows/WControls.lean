module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LowKernel
public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.StripBounds
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelGrowth
public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LowRowWControls

noncomputable section

open DedekindZetaZeroFree DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions Set Filter Complex
open scoped Classical Topology
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private theorem comb_aux {X1 X2 E M W ζ L Li H bX bE bζ bH bM bWL : ℝ}
    (hX1 : X1 ≤ bX) (hE : E ≤ bE) (hζ : ζ ≤ bζ) (hH : H ≤ bH) (hM : M ≤ bM)
    (hWL : W * L ≤ bWL)
    (X1_0 : 0 ≤ X1) (X2_0 : 0 ≤ X2) (E_0 : 0 ≤ E) (ζ0 : 0 ≤ ζ) (M0 : 0 ≤ M)
    (Li0 : 0 ≤ Li) (H0 : 0 ≤ H) (W0 : 0 ≤ W) (L0 : 0 ≤ L)
    (bX0 : 0 ≤ bX) (bE0 : 0 ≤ bE) (bζ0 : 0 ≤ bζ) (bH0 : 0 ≤ bH) (bM0 : 0 ≤ bM)
    (bWL0 : 0 ≤ bWL) :
    X1 * X2 * (E * M * W) * (ζ * L * Li * H) ≤ (bX * X2 * bE * bζ * Li * bH) * bM * bWL := by
  have h1 : X1 * X2 * E * ζ * Li * H ≤ bX * X2 * bE * bζ * Li * bH :=
    mul_le_mul
      (mul_le_mul
        (mul_le_mul (mul_le_mul (mul_le_mul hX1 le_rfl X2_0 bX0) hE E_0
          (mul_nonneg bX0 X2_0)) hζ ζ0 (mul_nonneg (mul_nonneg bX0 X2_0) bE0))
        le_rfl Li0 (mul_nonneg (mul_nonneg (mul_nonneg bX0 X2_0) bE0) bζ0))
      hH H0 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg bX0 X2_0) bE0) bζ0) Li0)
  have hb1 : 0 ≤ bX * X2 * bE * bζ * Li * bH :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg bX0 X2_0) bE0) bζ0) Li0) bH0
  have heq : X1 * X2 * (E * M * W) * (ζ * L * Li * H) =
      (X1 * X2 * E * ζ * Li * H) * M * (W * L) := by ring
  rw [heq]
  exact mul_le_mul (mul_le_mul h1 hM M0 hb1) hWL (mul_nonneg W0 L0) (mul_nonneg hb1 bM0)

theorem WL_bound (u : D.Row) (hu : u.u ≠ 1) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y t : ℝ, Scales.wLine - EulerDomain.pad / 2 ≤ y →
      y ≤ 4 + EulerDomain.pad / 2 →
      ‖D.W1Hat ((y : ℂ) + (t : ℂ) * I)‖ * ‖D.Lpsi u ((y : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ (-B) := by
  obtain ⟨A, CL, hA, hCL, hL⟩ := FixedRowStripBound.Lpsi_strip_bound D u hu
  set k : ℕ := ⌈A + B⌉₊ with hk
  obtain ⟨CW, hW⟩ := D.W1Hat_vertical_decay (Scales.wLine - EulerDomain.pad / 2)
    (4 + EulerDomain.pad / 2) (by unfold EulerDomain.pad Scales.wLine; norm_num) k
  refine ⟨CL * 2 ^ A * |CW|, by positivity, fun y t h1 h2 => ?_⟩
  have hw1 : Scales.wLine - EulerDomain.pad / 2 ≤ ((y : ℂ) + (t : ℂ) * I).re := by simpa using h1
  have hw2 : ((y : ℂ) + (t : ℂ) * I).re ≤ 4 + EulerDomain.pad / 2 := by simpa using h2
  have hL' := hL _ hw1 hw2
  have hW' := hW _ hw1 hw2
  have him : ((y : ℂ) + (t : ℂ) * I).im = t := by simp
  rw [him] at hL' hW'
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  have h2t : (2 + |t|) ^ A ≤ 2 ^ A * (1 + |t|) ^ A := by
    rw [← Real.mul_rpow (by norm_num) hpos.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hA
  have hkA : A + B ≤ k := Nat.le_ceil _
  have hexp : (1 + |t|) ^ (A - k) ≤ (1 + |t|) ^ (-B) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]); linarith
  have hsplit : (1 + |t|) ^ A * ((1 + |t|) ^ (-(k : ℝ))) = (1 + |t|) ^ (A - k) := by
    rw [← Real.rpow_add hpos]; ring_nf
  have hkk : ((1 + |t|) ^ k : ℝ) = (1 + |t|) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
  have ha0 : 0 ≤ ‖D.W1Hat ((y : ℂ) + (t : ℂ) * I)‖ := norm_nonneg _
  have ha : ‖D.W1Hat ((y : ℂ) + (t : ℂ) * I)‖ ≤ |CW| * (1 + |t|) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg hpos.le, ← hkk, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos k)]
    nlinarith [le_abs_self CW]
  have hLn : ‖D.Lpsi u ((y : ℂ) + (t : ℂ) * I)‖ ≤ CL * (2 ^ A * (1 + |t|) ^ A) :=
    hL'.trans (mul_le_mul_of_nonneg_left h2t hCL.le)
  have hp1 : 0 ≤ (1 + |t|) ^ A := Real.rpow_nonneg hpos.le _
  calc ‖D.W1Hat ((y : ℂ) + (t : ℂ) * I)‖ * ‖D.Lpsi u ((y : ℂ) + (t : ℂ) * I)‖
      ≤ (|CW| * (1 + |t|) ^ (-(k : ℝ))) * (CL * (2 ^ A * (1 + |t|) ^ A)) :=
        mul_le_mul ha hLn (norm_nonneg _) (by positivity)
    _ = (CL * 2 ^ A * |CW|) * ((1 + |t|) ^ A * (1 + |t|) ^ (-(k : ℝ))) := by ring
    _ = (CL * 2 ^ A * |CW|) * (1 + |t|) ^ (A - k) := by rw [hsplit]
    _ ≤ (CL * 2 ^ A * |CW|) * (1 + |t|) ^ (-B) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

theorem K_bound (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4)
    (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y s t : ℝ, Scales.wLine - EulerDomain.pad / 2 ≤ y →
      y ≤ 4 + EulerDomain.pad / 2 →
      ‖PoissonKernel.K D u ξ ((y : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖ ≤
        C * (1 + |s|) ^ (-(2 : ℝ)) * (1 + |t|) ^ (-B) := by
  have hq : 0 < D.q u := PoissonInitialBridge.q_pos D u
  have hp : (0 : ℝ) < EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  obtain ⟨CWL, hCWL0, hWL⟩ := WL_bound D u hu B
  obtain ⟨C1, hC1, hz⟩ := RowKernelGrowth.zetaSCont_line_bound D
  obtain ⟨CH, hCH, hHu⟩ := EulerSubpower.Hu_subpower_paddedBoxes D 1 one_pos
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay Scales.zLine Scales.zLine
    (by unfold Scales.zLine; norm_num) le_rfl 2
  have hcont : Continuous (fun y : ℝ =>
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (y - 1))) :=
    continuous_const.rpow (by fun_prop) (fun _ => Or.inl hZ.ne')
  obtain ⟨CZ, hCZ⟩ := (isCompact_Icc (a := Scales.wLine - EulerDomain.pad / 2)
    (b := 4 + EulerDomain.pad / 2)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨(|CZ| * D.q u ^ (-Scales.zLine) * Real.exp ((4 + Scales.zLine - 1) ^ 2) * C1 *
    ‖(D.Llam u ξ)⁻¹‖ * (CH * D.q u ^ (1 : ℝ))) * |CM| * CWL, by positivity, ?_⟩
  intro y s t h1y h2y
  have hwre : (((y : ℂ) + (t : ℂ) * I)).re = y := by simp
  have hzre : (((Scales.zLine : ℂ) + (s : ℂ) * I)).re = Scales.zLine := by simp
  have e : ‖PoissonKernel.K D u ξ ((y : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖ =
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (y - 1)) *
        D.q u ^ (-Scales.zLine) *
        ‖Complex.exp ((ξ + ((Scales.zLine : ℂ) + (s : ℂ) * I) - 1) ^ 2) *
          D.M ((Scales.zLine : ℂ) + (s : ℂ) * I) * D.W1Hat ((y : ℂ) + (t : ℂ) * I)‖ *
        ‖PoissonKernel.rowFactor D u ξ ((y : ℂ) + (t : ℂ) * I)
          ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ :=
    RowKernelGrowth.K_norm_eq D u hq ξ Scales.zLine y (s, t) Z hZ
  have eR : ‖PoissonKernel.rowFactor D u ξ ((y : ℂ) + (t : ℂ) * I)
          ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ =
      ‖D.zetaSCont (6 * ((Scales.zLine : ℂ) + (s : ℂ) * I))‖ *
        ‖D.Lpsi u ((y : ℂ) + (t : ℂ) * I)‖ * ‖(D.Llam u ξ)⁻¹‖ *
        ‖EulerDomain.Hu D u ξ ((y : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ := by
    unfold PoissonKernel.rowFactor
    simp only [div_eq_mul_inv, norm_mul]
  rw [e, eR, norm_mul, norm_mul]

  have hZb : Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (y - 1)) ≤ |CZ| := by
    have := hCZ y ⟨h1y, h2y⟩
    simp only [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  have hEb : ‖Complex.exp ((ξ + ((Scales.zLine : ℂ) + (s : ℂ) * I) - 1) ^ 2)‖ ≤
      Real.exp ((4 + Scales.zLine - 1) ^ 2) := by
    rw [Complex.norm_exp]
    have hre : ((ξ + ((Scales.zLine : ℂ) + (s : ℂ) * I) - 1) ^ 2).re =
        (ξ.re + Scales.zLine - 1) ^ 2 - (ξ.im + s) ^ 2 := by
      simp [pow_two] <;> ring
    rw [hre, hξ]
    apply Real.exp_le_exp.mpr
    linarith [sq_nonneg (ξ.im + s)]
  have hpos : (0 : ℝ) < 1 + |s| := by positivity
  have hMb : ‖D.M ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ ≤ |CM| * (1 + |s|) ^ (-(2 : ℝ)) := by
    have h := hCM ((Scales.zLine : ℂ) + (s : ℂ) * I) (by rw [hzre]) (by rw [hzre])
    have him : (((Scales.zLine : ℂ) + (s : ℂ) * I)).im = s := by simp
    rw [him] at h
    have h' : (1 + |s|) ^ 2 * ‖D.M ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ ≤ |CM| :=
      h.trans (le_abs_self _)
    rw [Real.rpow_neg hpos.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos 2),
      mul_comm]
    exact h'
  have hmem : ((ξ, ((y : ℂ) + (t : ℂ) * I), ((Scales.zLine : ℂ) + (s : ℂ) * I)) :
      EulerDomain.Coordinates) ∈ EulerDomain.paddedBoxes := by
    have h1 : Scales.goodLine - EulerDomain.pad ≤ ξ.re := by
      rw [hξ]; unfold Scales.goodLine; linarith
    have h2 : (3 / 25 : ℝ) - EulerDomain.pad ≤ ((y : ℂ) + (t : ℂ) * I).re := by
      rw [hwre]; unfold Scales.wLine at h1y; linarith
    have h3 : (2 / 5 : ℝ) - EulerDomain.pad ≤ ((Scales.zLine : ℂ) + (s : ℂ) * I).re := by
      rw [hzre]; unfold Scales.zLine; linarith
    exact Or.inl (Or.inl ⟨h1, h2, h3⟩)
  have hHb : ‖EulerDomain.Hu D u ξ ((y : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ ≤
      CH * D.q u ^ (1 : ℝ) := (hHu u _ hmem).2
  have hzb : ‖D.zetaSCont (6 * ((Scales.zLine : ℂ) + (s : ℂ) * I))‖ ≤ C1 :=
    hz _ hzre
  have hWL' := hWL y t h1y h2y
  have hq1 : 0 ≤ D.q u ^ (-Scales.zLine) := Real.rpow_nonneg hq.le _
  have hfin := comb_aux hZb hEb hzb hHb hMb hWL'
    (Real.rpow_nonneg hZ.le _) hq1 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg ((D.Llam u ξ)⁻¹)) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (abs_nonneg _) (Real.exp_pos _).le hC1.le
    (mul_nonneg hCH.le (Real.rpow_nonneg hq.le _))
    (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hpos.le _))
    (mul_nonneg hCWL0 (Real.rpow_nonneg (by positivity) _))
  calc _ ≤ _ := hfin
    _ = _ := by ring

def DecayOn (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C T0 : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ, T0 ≤ |y| →
    ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-B)

theorem verticalIntegral_eq_of_decayOn {a b : ℝ} {f : ℂ → ℂ} (hab : a < b)
    (hf : DifferentiableOn ℂ f (comparisonClosedStrip a b)) (hdec : DecayOn f a b) :
    comparisonVerticalIntegral b f = comparisonVerticalIntegral a f := by
  obtain ⟨C, T0, hbound⟩ := hdec 2 (by norm_num)
  set m : ℝ := (a + b) / 2 with hm
  have ham : a < ((m : ℂ)).re := by simp [hm]; linarith
  have hmb : ((m : ℂ)).re < b := by simp [hm]; linarith
  have hnb : comparisonClosedStrip a b ∈ 𝓝 (m : ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a < (m : ℂ).re ∧ (m : ℂ).re < b from ⟨ham, hmb⟩))
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hcont : ContinuousAt f (m : ℂ) := (hf.differentiableAt hnb).continuousAt
  have hres : Tendsto (fun z : ℂ => (z - (m : ℂ)) * f z) (𝓝[≠] (m : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => (z - (m : ℂ)) * f z) (𝓝 (m : ℂ)) (𝓝 ((m - m : ℂ) * f m)) :=
      ((continuous_id.sub continuous_const).continuousAt.mul hcont).tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have := SimplePoleVerticalShift.verticalIntegral_sub_eq_residue_of_decay ham hmb
    (hf.mono diff_subset) hres C T0
    (fun x hx y hy => by simpa [Real.rpow_neg_natCast] using hbound x hx y hy)
  linear_combination this

theorem K_diffAt (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4)
    (w z : ℂ) (hw : Scales.wLine - EulerDomain.pad / 2 ≤ w.re) (hz : z.re = Scales.zLine) :
    DifferentiableAt ℂ (fun w' : ℂ => PoissonKernel.K D u ξ w' z Z) w ∧
      DifferentiableAt ℂ (fun z' : ℂ => PoissonKernel.K D u ξ w z' Z) z := by
  have hq : 0 < D.q u := PoissonInitialBridge.q_pos D u
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hqc : (D.q u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hw' : (1 / 10 : ℝ) ≤ w.re := by
    unfold Scales.wLine EulerDomain.pad at hw; linarith
  have hz' : z.re = 2 / 5 := by unfold Scales.zLine at hz; exact hz
  have hmem : ((ξ, w, z) : EulerDomain.Coordinates) ∈ EulerDomain.OmegaStar := by
    show 0 < ξ.re ∧ 0 < w.re ∧ 0 < z.re ∧ 1 < 6 * z.re + w.re ∧ 1 < ξ.re + 6 * z.re ∧
      1 < ξ.re + w.re ∧ 2 < ξ.re + w.re + 6 * z.re ∧ 5 < 6 * ξ.re + 6 * z.re ∧ 1 / 2 < ξ.re ∧
      2 < 3 * ξ.re ∧ 5 / 2 < 3 * ξ.re + w.re
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hz6 : 6 * z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [Complex.mul_re] at this
    linarith
  have hLlam : D.Llam u ξ ≠ 0 :=
    RightHeckeBounds.Llam_ne_zero_of_one_lt D u ξ (by rw [hξ]; norm_num)
  have hRF := RowAnalyticContinuation.rowFactor_differentiableAt D u hu ξ w z hmem hz6 hLlam
  have hRFw : DifferentiableAt ℂ (fun w' : ℂ => PoissonKernel.rowFactor D u ξ w' z) w := by
    have h2 : DifferentiableAt ℂ (fun w' : ℂ => ((ξ, w', z) : ℂ × ℂ × ℂ)) w :=
      (differentiableAt_const _).prodMk (differentiableAt_id.prodMk (differentiableAt_const _))
    have h3 : DifferentiableAt ℂ ((fun p : ℂ × ℂ × ℂ => PoissonKernel.rowFactor D u p.1 p.2.1 p.2.2) ∘
        (fun w' : ℂ => ((ξ, w', z) : ℂ × ℂ × ℂ))) w := DifferentiableAt.comp w hRF h2
    exact h3
  have hRFz : DifferentiableAt ℂ (fun z' : ℂ => PoissonKernel.rowFactor D u ξ w z') z := by
    have h2 : DifferentiableAt ℂ (fun z' : ℂ => ((ξ, w, z') : ℂ × ℂ × ℂ)) z :=
      (differentiableAt_const _).prodMk ((differentiableAt_const _).prodMk differentiableAt_id)
    have h3 : DifferentiableAt ℂ ((fun p : ℂ × ℂ × ℂ => PoissonKernel.rowFactor D u p.1 p.2.1 p.2.2) ∘
        (fun z' : ℂ => ((ξ, w, z') : ℂ × ℂ × ℂ))) z := DifferentiableAt.comp z hRF h2
    exact h3
  have hW : Differentiable ℂ D.W1Hat := RowAnalyticContinuation.W1Hat_differentiable D
  have hMopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hM : DifferentiableAt ℂ D.M z :=
    D.M_differentiableOn.differentiableAt (hMopen.mem_nhds (by show 0 < z.re; linarith))
  constructor
  · have hpow : DifferentiableAt ℂ (fun w' : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
        (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w' - 1))) w :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl hZc)
    unfold PoissonKernel.K PoissonKernel.kernelWith
    exact ((((hpow.mul (differentiableAt_const _)).mul (differentiableAt_const _)).mul
      (hW w)).mul (differentiableAt_const _)).mul hRFw
  · have hpow : DifferentiableAt ℂ (fun z' : ℂ => (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 +
        (Scales.smoothingExponent : ℂ) * z' + (Scales.yExponent : ℂ) * (w - 1))) z :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl hZc)
    have hexp : DifferentiableAt ℂ (fun z' : ℂ => Complex.exp ((ξ + z' - 1) ^ 2)) z :=
      DifferentiableAt.cexp (by fun_prop)
    have hqp : DifferentiableAt ℂ (fun z' : ℂ => (D.q u : ℂ) ^ (-z')) z :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl hqc)
    unfold PoissonKernel.K PoissonKernel.kernelWith
    exact ((((hpow.mul hexp).mul hM).mul (differentiableAt_const _)).mul hqp).mul hRFz

theorem Iz_w_holo (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    DifferentiableOn ℂ (fun w => Iz D u ξ w Scales.zLine Z)
      (comparisonClosedStrip Scales.wLine 4) := by
  have hp : (0 : ℝ) < EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  set lo : ℝ := Scales.wLine - EulerDomain.pad / 2 with hlo
  set hi : ℝ := 4 + EulerDomain.pad / 2 with hhi
  set U : Set ℂ := {w : ℂ | lo < w.re} ∩ {w : ℂ | w.re < hi} with hUdef
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hwU : ∀ w ∈ U, lo < w.re ∧ w.re < hi := fun w hw => hw
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℝ → ℂ, ∀ w s, G w s = (2 * (Real.pi : ℂ))⁻¹ *
      PoissonKernel.K D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := ⟨_, fun _ _ => rfl⟩
  have hcont : ∀ w ∈ U, Continuous (G w) := by
    intro w hw
    have hfun : G w = fun s : ℝ => (2 * (Real.pi : ℂ))⁻¹ *
        PoissonKernel.K D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := funext (hG w)
    rw [hfun]
    refine continuous_const.mul ?_
    refine continuous_iff_continuousAt.mpr (fun s => ?_)
    have hd := (K_diffAt D u hu Z hZ ξ hξ w ((Scales.zLine : ℂ) + (s : ℂ) * I)
      (hwU w hw).1.le (by simp)).2
    have hc : ContinuousAt (fun s : ℝ => ((Scales.zLine : ℂ) + (s : ℂ) * I)) s :=
      Continuous.continuousAt (by fun_prop)
    exact ContinuousAt.comp (g := fun z : ℂ => PoissonKernel.K D u ξ w z Z)
      (f := fun s : ℝ => ((Scales.zLine : ℂ) + (s : ℂ) * I)) hd.continuousAt hc
  have hmeas : ∀ w ∈ U, AEStronglyMeasurable (G w) volume :=
    fun w hw => (hcont w hw).aestronglyMeasurable
  have hdiff : ∀ s : ℝ, DifferentiableOn ℂ (fun w => G w s) U := by
    intro s w hw
    have hfun : (fun w => G w s) = fun w : ℂ => (2 * (Real.pi : ℂ))⁻¹ *
        PoissonKernel.K D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := funext fun w => hG w s
    rw [hfun]
    exact (((K_diffAt D u hu Z hZ ξ hξ w ((Scales.zLine : ℂ) + (s : ℂ) * I)
      (hwU w hw).1.le (by simp)).1).const_mul _).differentiableWithinAt
  obtain ⟨C, hC0, hCb⟩ := K_bound D u hu Z hZ ξ hξ 0
  have hdom : ∀ w0 ∈ U, ∃ r > (0 : ℝ), Metric.ball w0 r ⊆ U ∧
      ∃ g : ℝ → ℝ, Integrable g volume ∧ ∀ w ∈ Metric.ball w0 r, ∀ s, ‖G w s‖ ≤ g s := by
    intro w0 hw0
    obtain ⟨h1, h2⟩ := hwU w0 hw0
    obtain ⟨r, hr, hr1, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ w0.re - lo ∧ r ≤ hi - w0.re :=
      ⟨min (w0.re - lo) (hi - w0.re), lt_min (by linarith) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    have hball : ∀ w ∈ Metric.ball w0 r, lo < w.re ∧ w.re < hi := by
      intro w hw
      have hd : |w.re - w0.re| < r := by
        have := Complex.abs_re_le_norm (w - w0)
        rw [Complex.sub_re] at this
        exact this.trans_lt (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw)
      have := abs_lt.mp hd
      constructor <;> linarith [this.1, this.2]
    refine ⟨r, hr, fun w hw => hball w hw, fun s => ‖(2 * (Real.pi : ℂ))⁻¹‖ * C *
      (1 + |s|) ^ (-(2 : ℝ)), ?_, ?_⟩
    · exact (KernelWeightIntegration.one_add_abs_rpow_integrable 2 (by norm_num)).const_mul _
    · intro w hw s
      obtain ⟨hw1, hw2⟩ := hball w hw
      have h := hCb w.re s w.im hw1.le hw2.le
      rw [Complex.re_add_im] at h
      simp only [neg_zero, Real.rpow_zero, mul_one] at h
      rw [hG, norm_mul]
      calc ‖(2 * (Real.pi : ℂ))⁻¹‖ *
            ‖PoissonKernel.K D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖
          ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * (C * (1 + |s|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = ‖(2 * (Real.pi : ℂ))⁻¹‖ * C * (1 + |s|) ^ (-(2 : ℝ)) := by ring
  have key := HolomorphicDominatedIntegral.differentiableOn_integral_of_locally_dominated
    (μ := volume) hU hmeas hdiff hdom
  have hEq : (fun w => Iz D u ξ w Scales.zLine Z) = fun w => ∫ s : ℝ, G w s := by
    funext w
    have : Iz D u ξ w Scales.zLine Z = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ s : ℝ, PoissonKernel.K D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := rfl
    rw [this]
    simp only [hG]
    rw [integral_const_mul]
  rw [hEq]
  refine key.mono ?_
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  show lo < w.re ∧ w.re < hi
  constructor
  · rw [hlo]; linarith
  · rw [hhi]; linarith

theorem Iz_w_decay (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    DecayOn (fun w => Iz D u ξ w Scales.zLine Z) Scales.wLine 4 := by
  intro B hB
  have hp : (0 : ℝ) < EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  obtain ⟨C, hC0, hCb⟩ := K_bound D u hu Z hZ ξ hξ B
  refine ⟨‖(2 * (Real.pi : ℂ))⁻¹‖ * (C * ∫ s : ℝ, (1 + |s|) ^ (-(2 : ℝ))), 0, ?_⟩
  intro x hx y _
  obtain ⟨hx1, hx2⟩ := hx
  have hx1' : Scales.wLine - EulerDomain.pad / 2 ≤ x := by linarith
  have hx2' : x ≤ 4 + EulerDomain.pad / 2 := by linarith
  have hint : Integrable (fun s : ℝ => C * (1 + |s|) ^ (-(2 : ℝ)) * (1 + |y|) ^ (-B)) volume :=
    ((KernelWeightIntegration.one_add_abs_rpow_integrable 2 (by norm_num)).const_mul C).mul_const _
  have hI : Iz D u ξ ((x : ℂ) + (y : ℂ) * I) Scales.zLine Z = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ s : ℝ, PoissonKernel.K D u ξ ((x : ℂ) + (y : ℂ) * I)
          ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := rfl
  have hle : ‖∫ s : ℝ, PoissonKernel.K D u ξ ((x : ℂ) + (y : ℂ) * I)
          ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖ ≤
      ∫ s : ℝ, C * (1 + |s|) ^ (-(2 : ℝ)) * (1 + |y|) ^ (-B) :=
    norm_integral_le_of_norm_le hint
      (Filter.Eventually.of_forall fun s => hCb x s y hx1' hx2')
  rw [integral_mul_const, integral_const_mul] at hle
  show ‖Iz D u ξ ((x : ℂ) + (y : ℂ) * I) Scales.zLine Z‖ ≤ _
  rw [hI, norm_mul]
  calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖∫ s : ℝ, PoissonKernel.K D u ξ ((x : ℂ) + (y : ℂ) * I)
          ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖
      ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * ((C * ∫ s : ℝ, (1 + |s|) ^ (-(2 : ℝ))) * (1 + |y|) ^ (-B)) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = ‖(2 * (Real.pi : ℂ))⁻¹‖ * (C * ∫ s : ℝ, (1 + |s|) ^ (-(2 : ℝ))) * (1 + |y|) ^ (-B) := by
        ring

theorem Iwz_shift (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    Iwz D u ξ 4 Scales.zLine Z = Iwz D u ξ Scales.wLine Scales.zLine Z := by
  unfold Iwz
  exact verticalIntegral_eq_of_decayOn (by norm_num [Scales.wLine])
    (Iz_w_holo D u hu Z hZ ξ hξ) (Iz_w_decay D u hu Z hZ ξ hξ)

end

end DedekindZetaZeroFree.Quantitative.LowRowWControls
