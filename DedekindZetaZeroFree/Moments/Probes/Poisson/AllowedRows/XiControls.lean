module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LowKernel
public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelGrowth
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.StripBounds
public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LowRowXiControls

noncomputable section

open DedekindZetaZeroFree DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions Set Filter Complex
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

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

private theorem z₀_pos' : 0 < Scales.zLine := by unfold Scales.zLine; norm_num

private theorem xg_pad_lt_x1 : Scales.goodLine - EulerDomain.pad < Scales.rightLine := by
  rw [Scales.rightLine_eq]; unfold Scales.goodLine EulerDomain.pad; norm_num

private theorem Llam_ne_of_x1 (u : D.Row) (ξ : ℂ) (h : Scales.rightLine ≤ ξ.re) : D.Llam u ξ ≠ 0 :=
  RightHeckeBounds.Llam_ne_zero_of_one_lt D u ξ (by
    have : (1 : ℝ) < Scales.rightLine := by rw [Scales.rightLine_eq]; norm_num
    linarith)

private theorem K_strip_bound (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    ∃ Cc k : ℝ, 0 ≤ Cc ∧ 0 ≤ k ∧ ∀ ξ : ℂ, 1 + 1 / 20000000 ≤ ξ.re → ξ.re ≤ 5 →
      ∀ p : ℝ × ℝ,
      ‖PoissonKernel.K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
      Cc * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
        (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
  have hq0 : 0 < D.q u := PoissonInitialBridge.q_pos D u
  have hpad0 : EulerDomain.pad = 1 / 1000000 := rfl
  have hy0 : Scales.wLine = 3 / 25 := rfl
  obtain ⟨A, C2, hA, hC2, h2⟩ := FixedRowStripBound.Lpsi_strip_bound D u hu
  obtain ⟨C1, hC1, h1⟩ := RowKernelGrowth.zetaSCont_line_bound D
  obtain ⟨C3, hC3, h3⟩ := RowKernelGrowth.Hu_box_bound D 1 one_pos
  have hσ : (1 : ℝ) < 1 + 1 / 20000000 := by norm_num
  obtain ⟨C4, hC4, h4⟩ := RightHeckeBounds.Llam_inv_norm_le_right D (1 + 1 / 20000000) hσ
  set R : ℝ := C1 * C2 * C4 * (C3 * D.q u ^ (1 : ℝ)) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set M : ℝ := |Scales.xExponent / 2| + 5 + |Scales.smoothingExponent * Scales.zLine| + |Scales.yExponent * (Scales.wLine - 1)| + 1
    with hM
  set Zm : ℝ := Real.exp (|Real.log Z| * M) with hZm
  set Cc : ℝ := Zm * D.q u ^ (-Scales.zLine) * R with hCc
  have hCc0 : 0 ≤ Cc := mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hq0.le _)) hR0
  refine ⟨Cc, max A 0, hCc0, le_max_right _ _, ?_⟩
  intro ξ hx1' hx4 p
  rw [RowKernelGrowth.K_norm_eq D u hq0 ξ Scales.zLine Scales.wLine p Z hZ]
  set w : ℂ := (Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I with hw
  set z : ℂ := (Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I with hz
  have hwre : w.re = Scales.wLine := by simp [hw]
  have hzre : z.re = Scales.zLine := by simp [hz]
  have hwim : w.im = p.2 := by simp [hw]
  have hnw : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := norm_nonneg _
  have hrow : ‖PoissonKernel.rowFactor D u ξ w z‖ ≤ R * (2 + |p.2|) ^ A := by
    have e : ‖PoissonKernel.rowFactor D u ξ w z‖ =
        ‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖(D.Llam u ξ)⁻¹‖ * ‖EulerDomain.Hu D u ξ w z‖ := by
      unfold PoissonKernel.rowFactor
      simp only [div_eq_mul_inv, norm_mul]
    have a1 := h1 z hzre
    have a2 := h2 w (by rw [hwre, hy0, hpad0]; norm_num) (by rw [hwre, hy0, hpad0]; norm_num)
    rw [hwim] at a2
    have a3 := h3 u ξ w z (by
      unfold Scales.goodLine; linarith) hwre.ge hzre.ge
    have a4 := h4 u ξ hx1'
    rw [Real.rpow_one] at a3
    rw [e]
    have hp : 0 ≤ (2 + |p.2|) ^ A := by positivity
    calc _ ≤ C1 * (C2 * (2 + |p.2|) ^ A) * C4 * (C3 * D.q u) := by
          gcongr
      _ = _ := by rw [hR, Real.rpow_one]; ring
  have hZe : Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1))
      ≤ Zm := by
    rw [Real.rpow_def_of_pos hZ, hZm]
    apply Real.exp_le_exp.mpr
    have habs := le_abs_self (Real.log Z)
    have hnn := abs_nonneg (Real.log Z)
    have b1 := le_abs_self (Scales.xExponent / 2)
    have b2 := neg_abs_le (Scales.xExponent / 2)
    have b3 := le_abs_self (Scales.smoothingExponent * Scales.zLine)
    have b4 := neg_abs_le (Scales.smoothingExponent * Scales.zLine)
    have b5 := le_abs_self (Scales.yExponent * (Scales.wLine - 1))
    have b6 := neg_abs_le (Scales.yExponent * (Scales.wLine - 1))
    have hx0 : 0 ≤ ξ.re := by linarith
    have hxm : -1 ≤ ξ.re - 1 := by linarith
    have hE : |Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)| ≤ M := by
      rw [abs_le]; constructor <;> (rw [hM]; linarith)
    calc Real.log Z * _ ≤ |Real.log Z * (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
            Scales.yExponent * (Scales.wLine - 1))| := le_abs_self _
      _ = |Real.log Z| * |_| := abs_mul _ _
      _ ≤ |Real.log Z| * M := mul_le_mul_of_nonneg_left hE hnn
  have hqz : 0 ≤ D.q u ^ (-Scales.zLine) := by positivity
  have hpow1 : (2 + |p.2|) ^ A ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A 0) := by
    calc (2 + |p.2|) ^ A ≤ (2 + |p.2|) ^ (max A 0) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg p.2]) (le_max_left _ _)
      _ ≤ _ := Real.rpow_le_rpow (by linarith [abs_nonneg p.2]) (by
            linarith [abs_nonneg p.1, abs_nonneg ξ.im]) (le_max_right _ _)
  have hpos : 0 ≤ (2 + |p.2|) ^ A := by positivity
  calc _ ≤ Zm * D.q u ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (R * (2 + |p.2|) ^ A) := by
        gcongr
    _ ≤ Zm * D.q u ^ (-Scales.zLine) *
        WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
          (R * (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A 0)) := by
        gcongr
    _ = _ := by rw [hCc]; ring

private def stripV : Set ℂ := {ξ : ℂ | 1 + 1 / 20000000 < ξ.re ∧ ξ.re < 5}

private theorem mem_stripV {ξ : ℂ} : ξ ∈ stripV ↔ 1 + 1 / 20000000 < ξ.re ∧ ξ.re < 5 := Iff.rfl

private theorem stripV_open : IsOpen stripV := by
  unfold stripV
  exact IsOpen.and (isOpen_lt continuous_const Complex.continuous_re)
    (isOpen_lt Complex.continuous_re continuous_const)

private theorem stripV_ne (u : D.Row) (ξ : ℂ) (hξ : ξ ∈ stripV) : D.Llam u ξ ≠ 0 := by
  have := (mem_stripV.1 hξ).1
  exact RightHeckeBounds.Llam_ne_zero_of_one_lt D u ξ (by linarith)

private theorem stripV_g (ξ : ℂ) (hξ : ξ ∈ stripV) : Scales.goodLine - EulerDomain.pad ≤ ξ.re := by
  have := (mem_stripV.1 hξ).1
  unfold Scales.goodLine EulerDomain.pad; linarith

private theorem K_strip_diff (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    ∀ ξ ∈ stripV, ∀ s t : ℝ, DifferentiableAt ℂ
      (fun x : ℂ => PoissonKernel.K D u x ((Scales.wLine : ℂ) + (s : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I) Z) ξ := by
  have hq0 : 0 < D.q u := PoissonInitialBridge.q_pos D u
  intro ξ hξ s t
  have hw : ((Scales.wLine : ℂ) + (s : ℂ) * Complex.I).re = Scales.wLine := by simp
  have hz : ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I).re = Scales.zLine := by simp
  refine RowAnalyticContinuation.K_differentiableAt_xi D u hu hq0 Z hZ ξ _ _
    (RowAnalyticContinuation.mem_OmegaStar_of_re ξ _ _ (stripV_g ξ hξ) hw hz) ?_
    (stripV_ne D u ξ hξ)
  intro h
  have := congrArg Complex.re h
  have h6 : (6 * ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I)).re = 6 * Scales.zLine := by simp
  rw [h6] at this
  unfold Scales.zLine at this
  norm_num at this

private theorem K_strip_cont (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    ∀ ξ ∈ stripV, Continuous (fun p : ℝ × ℝ => PoissonKernel.K D u ξ
      ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I) ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) :=
  by
  intro ξ hξ
  have h := RowAnalyticContinuation.K_continuous_heights D u hu
    (PoissonInitialBridge.q_pos D u) Z hZ ξ (stripV_g ξ hξ) (stripV_ne D u ξ hξ)
  have h2 := h.comp (continuous_swap (X := ℝ) (Y := ℝ))
  exact h2

private theorem K_strip_maj (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    ∀ ξ₀ ∈ stripV, ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ stripV ∧ ∃ C k : ℝ,
      0 ≤ C ∧ 0 ≤ k ∧ ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p : ℝ × ℝ,
        ‖PoissonKernel.K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          C * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
  obtain ⟨Cc, k, hCc, hk, hbd⟩ := K_strip_bound D u hu Z hZ
  intro ξ₀ hξ₀
  have hξ₀' := mem_stripV.1 hξ₀
  have hr : 0 < min (ξ₀.re - (1 + 1 / 20000000)) (5 - ξ₀.re) :=
    lt_min (by linarith [hξ₀'.1]) (by linarith [hξ₀'.2])
  have hball : Metric.ball ξ₀ (min (ξ₀.re - (1 + 1 / 20000000)) (5 - ξ₀.re)) ⊆ stripV := by
    intro ξ hξ
    have hd : dist ξ ξ₀ < min (ξ₀.re - (1 + 1 / 20000000)) (5 - ξ₀.re) := hξ
    have hre : |ξ.re - ξ₀.re| ≤ dist ξ ξ₀ := by
      rw [dist_eq_norm]
      have := Complex.abs_re_le_norm (ξ - ξ₀)
      rwa [Complex.sub_re] at this
    have h1 := (abs_le.1 hre)
    have h2 := min_le_left (ξ₀.re - (1 + 1 / 20000000)) (5 - ξ₀.re)
    have h3 := min_le_right (ξ₀.re - (1 + 1 / 20000000)) (5 - ξ₀.re)
    exact mem_stripV.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
  refine ⟨min (ξ₀.re - (1 + 1 / 20000000)) (5 - ξ₀.re), hr, hball, Cc, k, hCc, hk,
    fun ξ hξ p => ?_⟩
  have := mem_stripV.1 (hball hξ)
  exact hbd ξ this.1.le this.2.le p

private theorem Iwz_xi_holo_gen (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    DifferentiableOn ℂ (fun ξ => Iwz D u ξ Scales.wLine Scales.zLine Z)
      (comparisonClosedStrip Scales.rightLine 4) := by
  have hI : DifferentiableOn ℂ (fun ξ => comparisonVerticalIntegral Scales.wLine (fun w =>
      comparisonVerticalIntegral Scales.zLine (fun z => PoissonKernel.K D u ξ w z Z))) stripV :=
    RowKernelHolomorphy.differentiableOn_nested_integral D stripV stripV_open
      (fun ξ w z => PoissonKernel.K D u ξ w z Z) Scales.wLine Scales.zLine z₀_pos'
      (K_strip_diff D u hu Z hZ) (K_strip_cont D u hu Z hZ) (K_strip_maj D u hu Z hZ)
  have hsub : comparisonClosedStrip Scales.rightLine 4 ⊆ stripV := by
    intro ξ hξ
    have h1 : Scales.rightLine ≤ ξ.re := hξ.1
    have h2 : ξ.re ≤ 4 := hξ.2
    rw [Scales.rightLine_eq] at h1
    exact mem_stripV.2 ⟨by linarith, by linarith⟩
  exact hI.mono hsub

theorem Iwz_xi_holo_small (u : D.Row) (hu : u.u ≠ 1) (hq : D.q u < 2) (Z : ℝ) (hZ : 0 < Z) :
    DifferentiableOn ℂ (fun ξ => Iwz D u ξ Scales.wLine Scales.zLine Z)
      (comparisonClosedStrip Scales.rightLine 4) := Iwz_xi_holo_gen D u hu Z hZ

private theorem Iwz_xi_decay_gen (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    DecayOn (fun ξ => Iwz D u ξ Scales.wLine Scales.zLine Z) Scales.rightLine 4 := by
  have hq0 : 0 < D.q u := PoissonInitialBridge.q_pos D u
  have hpad0 : EulerDomain.pad = 1 / 1000000 := rfl
  have hy0 : Scales.wLine = 3 / 25 := rfl
  obtain ⟨A, C2, hA, hC2, h2⟩ := FixedRowStripBound.Lpsi_strip_bound D u hu
  intro B hB
  obtain ⟨C1, hC1, h1⟩ := RowKernelGrowth.zetaSCont_line_bound D
  obtain ⟨C3, hC3, h3⟩ := RowKernelGrowth.Hu_box_bound D 1 one_pos
  have hx1 : (1 : ℝ) < Scales.rightLine := by rw [Scales.rightLine_eq]; norm_num
  obtain ⟨C4, hC4, h4⟩ := RightHeckeBounds.Llam_inv_norm_le_right D Scales.rightLine hx1
  obtain ⟨Cw, hCw0, hCw⟩ := KernelWeightIntegration.nested_integral_bound D Scales.zLine Scales.zLine
    Scales.wLine Scales.wLine Scales.rightLine 4 z₀_pos' le_rfl le_rfl
    (by rw [Scales.rightLine_eq]; norm_num) B (max A 0) hB (le_max_right _ _)
  set R : ℝ := C1 * C2 * C4 * (C3 * D.q u ^ (1 : ℝ)) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set M : ℝ := |Scales.xExponent / 2| + 4 + |Scales.smoothingExponent * Scales.zLine| + |Scales.yExponent * (Scales.wLine - 1)| + 1
    with hM
  set Zm : ℝ := Real.exp (|Real.log Z| * M) with hZm
  set Cc : ℝ := Zm * D.q u ^ (-Scales.zLine) * R with hCc
  have hCc0 : 0 ≤ Cc := mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hq0.le _)) hR0
  refine ⟨((2 * Real.pi)⁻¹) ^ 2 * (Cc * Cw), 0, ?_⟩
  intro x hx y _
  set ξ : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hξ
  have hre : ξ.re = x := by simp [hξ]
  have him : ξ.im = y := by simp [hξ]
  have hx1' : Scales.rightLine ≤ ξ.re := by rw [hre]; exact hx.1
  have hx4 : ξ.re ≤ 4 := by rw [hre]; exact hx.2
  have hne := Llam_ne_of_x1 D u ξ hx1'
  have hcont := RowAnalyticContinuation.K_continuous_heights D u hu hq0 Z hZ ξ
    (by have := xg_pad_lt_x1; linarith) hne
  have hcont' := hcont.comp (continuous_swap (X := ℝ) (Y := ℝ))
  have hbd : ∀ p : ℝ × ℝ,
      ‖PoissonKernel.K D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
      Cc * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
        (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A 0) := by
    intro p
    rw [RowKernelGrowth.K_norm_eq D u hq0 ξ Scales.zLine Scales.wLine p Z hZ]
    set w : ℂ := (Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I with hw
    set z : ℂ := (Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I with hz
    have hwre : w.re = Scales.wLine := by simp [hw]
    have hzre : z.re = Scales.zLine := by simp [hz]
    have hwim : w.im = p.2 := by simp [hw]
    have hnw : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := norm_nonneg _

    have hrow : ‖PoissonKernel.rowFactor D u ξ w z‖ ≤ R * (2 + |p.2|) ^ A := by
      have e : ‖PoissonKernel.rowFactor D u ξ w z‖ =
          ‖D.zetaSCont (6 * z)‖ * ‖D.Lpsi u w‖ * ‖(D.Llam u ξ)⁻¹‖ * ‖EulerDomain.Hu D u ξ w z‖ := by
        unfold PoissonKernel.rowFactor
        simp only [div_eq_mul_inv, norm_mul]
      have a1 := h1 z hzre
      have a2 := h2 w (by rw [hwre, hy0, hpad0]; norm_num) (by rw [hwre, hy0, hpad0]; norm_num)
      rw [hwim] at a2
      have a3 := h3 u ξ w z (by
        unfold Scales.goodLine; have := hx1'; rw [Scales.rightLine_eq] at this; linarith)
        hwre.ge hzre.ge
      have a4 := h4 u ξ hx1'
      rw [Real.rpow_one] at a3
      rw [e]
      have hp : 0 ≤ (2 + |p.2|) ^ A := by positivity
      calc _ ≤ C1 * (C2 * (2 + |p.2|) ^ A) * C4 * (C3 * D.q u) := by
            gcongr
        _ = _ := by rw [hR, Real.rpow_one]; ring
    have hZe : Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1))
        ≤ Zm := by
      rw [Real.rpow_def_of_pos hZ, hZm]
      apply Real.exp_le_exp.mpr
      have habs := le_abs_self (Real.log Z)
      have hnn := abs_nonneg (Real.log Z)
      have b1 := le_abs_self (Scales.xExponent / 2)
      have b2 := neg_abs_le (Scales.xExponent / 2)
      have b3 := le_abs_self (Scales.smoothingExponent * Scales.zLine)
      have b4 := neg_abs_le (Scales.smoothingExponent * Scales.zLine)
      have b5 := le_abs_self (Scales.yExponent * (Scales.wLine - 1))
      have b6 := neg_abs_le (Scales.yExponent * (Scales.wLine - 1))
      have hx0 : 0 ≤ ξ.re := by
        have := hx1'; rw [Scales.rightLine_eq] at this; linarith
      have hxm : -1 ≤ ξ.re - 1 := by linarith
      have hE : |Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)| ≤ M := by
        rw [abs_le]; constructor <;> (rw [hM]; linarith)
      calc Real.log Z * _ ≤ |Real.log Z * (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
              Scales.yExponent * (Scales.wLine - 1))| := le_abs_self _
        _ = |Real.log Z| * |_| := abs_mul _ _
        _ ≤ |Real.log Z| * M := mul_le_mul_of_nonneg_left hE hnn
    have hqz : 0 ≤ D.q u ^ (-Scales.zLine) := by positivity
    have hpow1 : (2 + |p.2|) ^ A ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A 0) := by
      calc (2 + |p.2|) ^ A ≤ (2 + |p.2|) ^ (max A 0) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg p.2]) (le_max_left _ _)
        _ ≤ _ := Real.rpow_le_rpow (by linarith [abs_nonneg p.2]) (by
              linarith [abs_nonneg p.1, abs_nonneg ξ.im]) (le_max_right _ _)
    have hpos : 0 ≤ (2 + |p.2|) ^ A := by positivity
    calc _ ≤ Zm * D.q u ^ (-Scales.zLine) *
          WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (R * (2 + |p.2|) ^ A) := by
          gcongr
      _ ≤ Zm * D.q u ^ (-Scales.zLine) *
          WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            (R * (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A 0)) := by
          gcongr
      _ = _ := by rw [hCc]; ring
  have hle := (hCw ξ hx1' hx4 Scales.zLine Scales.wLine le_rfl le_rfl le_rfl le_rfl Cc hCc0
    (fun w z => PoissonKernel.K D u ξ w z Z) hcont'.aestronglyMeasurable hbd).2.2.2
  have hI : Iwz D u ξ Scales.wLine Scales.zLine Z =
      comparisonVerticalIntegral Scales.wLine (fun w =>
        comparisonVerticalIntegral Scales.zLine (fun z => PoissonKernel.K D u ξ w z Z)) := rfl
  show ‖Iwz D u ξ Scales.wLine Scales.zLine Z‖ ≤ _
  rw [hI]
  rw [him] at hle
  calc _ ≤ _ := hle
    _ = _ := by ring

theorem Iwz_xi_decay_small (u : D.Row) (hu : u.u ≠ 1) (hq : D.q u < 2) (Z : ℝ) (hZ : 0 < Z) :
    DecayOn (fun ξ => Iwz D u ξ Scales.wLine Scales.zLine Z) Scales.rightLine 4 :=
  Iwz_xi_decay_gen D u hu Z hZ

theorem Iwz_xi_holo (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    DifferentiableOn ℂ (fun ξ => Iwz D u ξ Scales.wLine Scales.zLine Z)
      (comparisonClosedStrip Scales.rightLine 4) :=
  Iwz_xi_holo_gen D u hu Z hZ

theorem Iwz_xi_decay (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    DecayOn (fun ξ => Iwz D u ξ Scales.wLine Scales.zLine Z) Scales.rightLine 4 :=
  Iwz_xi_decay_gen D u hu Z hZ

theorem triple_xi_shift (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    triple D u 4 Scales.wLine Scales.zLine Z = triple D u Scales.rightLine Scales.wLine Scales.zLine Z := by
  unfold triple
  exact verticalIntegral_eq_of_decayOn (by norm_num [Scales.rightLine, Scales.contourOffset])
    (Iwz_xi_holo D u hu Z hZ) (Iwz_xi_decay D u hu Z hZ)

end

end DedekindZetaZeroFree.Quantitative.LowRowXiControls
