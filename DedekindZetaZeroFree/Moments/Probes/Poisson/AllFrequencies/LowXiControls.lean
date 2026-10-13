module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyRightBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyConvexity
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.XiControls
public import DedekindZetaZeroFree.Moments.Probes.Poisson.KernelRegularity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLowXiControls31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

private theorem z₀_pos' : 0 < Scales.zLine := by unfold Scales.zLine; norm_num

private theorem xg_pad_le (ξ : ℂ) (hξ : 1 + Scales.contourOffset / 2 ≤ ξ.re) :
    Scales.goodLine - EulerDomain.pad ≤ ξ.re := by
  have e1 : Scales.goodLine = 8801 / 10000 := rfl
  have e2 : EulerDomain.pad = 1 / 1000000 := rfl
  have e3 : Scales.contourOffset = 1 / 10000000 := rfl
  linarith

private theorem x1_ge (ξ : ℂ) (h : Scales.rightLine ≤ ξ.re) : 1 + Scales.contourOffset / 2 ≤ ξ.re := by
  have e1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have e3 : Scales.contourOffset = 1 / 10000000 := rfl
  linarith

private theorem minus_ne (u : Frequency D.recipe) (ξ : ℂ) (hξ : 1 + Scales.contourOffset / 2 ≤ ξ.re) :
    (pkg D).minus u ξ ≠ 0 := by
  obtain ⟨C, hC, h⟩ := RawRightHecke31.minus_right D (1 + Scales.contourOffset / 2)
    (by unfold Scales.contourOffset; norm_num)
  exact (h u ξ hξ).1

private theorem rawKernel_norm_eq_gen (u : Frequency D.recipe)
    (hq : 0 < frequencyNorm D.recipe u) (ξ w z : ℂ) (Z : ℝ) (hZ : 0 < Z) :
    ‖rawKernel D u ξ w z Z‖ =
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (w.re - 1)) *
        frequencyNorm D.recipe u ^ (-z.re) *
        ‖Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w‖ * ‖rawFactor D u ξ w z‖ := by
  have hfac : ‖rawKernel D u ξ w z Z‖ =
      ‖(Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
          (Scales.yExponent : ℂ) * (w - 1))‖ *
        ‖Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w‖ *
        ‖(frequencyNorm D.recipe u : ℂ) ^ (-z)‖ * ‖rawFactor D u ξ w z‖ := by
    unfold rawKernel
    simp only [norm_mul]
    first | done | ring
  have e1 : ((((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
      (Scales.yExponent : ℂ) * (w - 1))).re =
      Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (w.re - 1) := by
    first
      | (simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.one_im]; done)
      | (simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.one_im]; ring)
      | (simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.one_im, zero_mul,
          mul_zero, sub_zero, add_zero, zero_add]; done)
      | (simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.one_im, zero_mul,
          mul_zero, sub_zero, add_zero, zero_add]; ring)
      | (simp; done)
      | (simp; ring)
  rw [hfac, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_cpow_eq_rpow_re_of_pos hq, e1,
    Complex.neg_re]
  ring

private theorem rawKernel_norm_eq (u : Frequency D.recipe) (hq : 0 < frequencyNorm D.recipe u)
    (ξ : ℂ) (v y : ℝ) (p : ℝ × ℝ) (Z : ℝ) (hZ : 0 < Z) :
    ‖rawKernel D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ =
      Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * v + Scales.yExponent * (y - 1)) *
        frequencyNorm D.recipe u ^ (-v) * WeightConvolution.weightModulus D ξ v y p *
        ‖rawFactor D u ξ ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ := by
  have hwre : ((y : ℂ) + (p.2 : ℂ) * Complex.I).re = y := by simp
  have hzre : ((v : ℂ) + (p.1 : ℂ) * Complex.I).re = v := by simp
  rw [rawKernel_norm_eq_gen D u hq ξ _ _ Z hZ, hwre, hzre]
  first | done | rfl

theorem rawKernel_weight_bound (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) :
    ∃ (C k : ℝ), 0 ≤ C ∧ 0 ≤ k ∧ ∀ ξ : ℂ, 1 + Scales.contourOffset / 2 ≤ ξ.re → ξ.re ≤ 5 →
      ∀ s t : ℝ,
        ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖ ≤
          C * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine (s, t) *
            (2 + |s| + |t| + |ξ.im|) ^ k := by
  have hq : 0 < frequencyNorm D.recipe u := by
    rw [← rawFrequency_norm D u]
    exact_mod_cast D.recipe.A.exteriorNorm_pos _
  have hy0 : Scales.wLine = 3 / 25 := rfl
  have hpad0 : EulerDomain.pad = 1 / 1000000 := rfl
  have hδ : Scales.contourOffset = 1 / 10000000 := rfl
  have hxg : Scales.goodLine = 8801 / 10000 := rfl
  have hz0 : Scales.zLine = 2 / 5 := rfl
  obtain ⟨A, C2, hA, hC2, h2⟩ := RawSharpConvexity31.plus_strip_growth D u hu
  obtain ⟨C1, hC1, h1⟩ := RawRightHecke31.recipe_L_right D Scales.zLine (by rw [hz0]; norm_num)
  obtain ⟨C3, hC3, h3⟩ := RawEulerProduct31.correctionProduct_subpower_boxes D 1 one_pos
  obtain ⟨C4, hC4, h4⟩ := RawRightHecke31.minus_right D (1 + Scales.contourOffset / 2)
    (by rw [hδ]; norm_num)
  have hb : ∀ ξ w z : ℂ, Scales.goodLine ≤ ξ.re → Scales.wLine ≤ w.re → Scales.zLine ≤ z.re →
      ((ξ, w, z) : ℂ × ℂ × ℂ) ∈ EulerDomain.boxes := by
    intro ξ w z a b c
    refine Or.inl (Or.inl ?_)
    exact ⟨a, b, c⟩
  obtain ⟨R3, hR3pos, hR3⟩ : ∃ R3 : ℝ, 0 ≤ R3 ∧ ∀ ξ w z : ℂ, Scales.goodLine ≤ ξ.re →
      Scales.wLine ≤ w.re → Scales.zLine ≤ z.re →
      ‖AllRowEuler.InitialSeparation.correctionProduct D.context (rawFrequency D u) ξ w z‖ ≤ R3 :=
    ⟨max _ 0, le_max_right _ _, fun ξ w z a b c =>
      le_trans (h3 (rawFrequency D u) (ξ, w, z) (hb ξ w z a b c)).2 (le_max_left _ _)⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |Scales.xExponent / 2| + 5 + |Scales.smoothingExponent * Scales.zLine| +
      |Scales.yExponent * (Scales.wLine - 1)| + 1 := ⟨_, rfl⟩
  obtain ⟨Zm, hZm⟩ : ∃ Zm : ℝ, Zm = Real.exp (|Real.log Z| * M) := ⟨_, rfl⟩
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ,
      Cc = Zm * frequencyNorm D.recipe u ^ (-Scales.zLine) * (C1 * C2 * R3 * C4) := ⟨_, rfl⟩
  have hZm0 : 0 ≤ Zm := by rw [hZm]; exact (Real.exp_pos _).le
  have hqz : 0 ≤ frequencyNorm D.recipe u ^ (-Scales.zLine) := Real.rpow_nonneg hq.le _
  have hK0 : 0 ≤ C1 * C2 * R3 * C4 := by positivity
  have hCc0 : 0 ≤ Cc := by
    rw [hCc]
    exact mul_nonneg (mul_nonneg hZm0 hqz) hK0
  have hrow : ∀ ξ w z : ℂ, 1 + Scales.contourOffset / 2 ≤ ξ.re → w.re = Scales.wLine → z.re = Scales.zLine →
      ‖rawFactor D u ξ w z‖ ≤ (C1 * C2 * R3 * C4) * (2 + |w.im|) ^ A := by
    intro ξ w z hξ hw hz
    have a1 := (h1 z hz.ge).2.1
    have a2 := h2 w (by rw [hw, hy0, hpad0]; norm_num) (by rw [hw, hy0, hpad0]; norm_num)
    have a3 := hR3 ξ w z (by linarith) hw.ge hz.ge
    have a4 := (h4 u ξ hξ).2.2
    have hp : 0 ≤ (2 + |w.im|) ^ A := by positivity
    unfold rawFactor
    simp only [div_eq_mul_inv, norm_mul]
    calc _ ≤ C1 * (C2 * (2 + |w.im|) ^ A) * R3 * C4 := by gcongr
      _ = _ := by ring
  have hbd : ∀ ξ : ℂ, 1 + Scales.contourOffset / 2 ≤ ξ.re → ξ.re ≤ 5 → ∀ p : ℝ × ℝ,
      ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
        Cc * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
          (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A 0) := by
    intro ξ hξ hξ5 p
    have hwre : ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I).re = Scales.wLine := by simp
    have hzre : ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I).re = Scales.zLine := by simp
    have hwim : ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
    have hnw : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := norm_nonneg _
    have hrow' := hrow ξ _ _ hξ hwre hzre
    rw [hwim] at hrow'
    rw [rawKernel_norm_eq D u hq ξ Scales.zLine Scales.wLine p Z hZ]
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
      have hE : |Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1)|
          ≤ M := by
        rw [abs_le]; constructor <;> (rw [hM]; linarith)
      calc Real.log Z * _ ≤ |Real.log Z * (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine +
              Scales.yExponent * (Scales.wLine - 1))| := le_abs_self _
        _ = |Real.log Z| * |_| := abs_mul _ _
        _ ≤ |Real.log Z| * M := mul_le_mul_of_nonneg_left hE hnn
    have hpow1 : (2 + |p.2|) ^ A ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A 0) := by
      calc (2 + |p.2|) ^ A ≤ (2 + |p.2|) ^ (max A 0) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg p.2]) (le_max_left _ _)
        _ ≤ _ := Real.rpow_le_rpow (by linarith [abs_nonneg p.2]) (by
              linarith [abs_nonneg p.1, abs_nonneg ξ.im]) (le_max_right _ _)
    have hpos : 0 ≤ (2 + |p.2|) ^ A := by positivity
    calc _ ≤ Zm * frequencyNorm D.recipe u ^ (-Scales.zLine) *
          WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            ((C1 * C2 * R3 * C4) * (2 + |p.2|) ^ A) := by
          gcongr
      _ ≤ Zm * frequencyNorm D.recipe u ^ (-Scales.zLine) *
          WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            ((C1 * C2 * R3 * C4) * (2 + |p.1| + |p.2| + |ξ.im|) ^ (max A 0)) := by
          gcongr
      _ = _ := by rw [hCc]; ring
  exact ⟨Cc, max A 0, hCc0, le_max_right _ _, fun ξ h1 h5 s t => hbd ξ h1 h5 (s, t)⟩

private theorem rawKernel_diffAt_xi (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : 1 + Scales.contourOffset / 2 ≤ ξ.re) (w z : ℂ)
    (hw : w.re = Scales.wLine) (hz : z.re = Scales.zLine) :
    DifferentiableAt ℂ (fun x : ℂ => rawKernel D u x w z Z) ξ := by
  have h := RawKernelRegularity31.rawKernel_differentiableAt D u hu Z hZ (ξ, w, z)
    (RowAnalyticContinuation.mem_OmegaStar_of_re ξ w z (xg_pad_le ξ hξ) hw hz)
    (by
      show (1 / 6 : ℝ) < z.re
      rw [hz]; unfold Scales.zLine; norm_num)
    (minus_ne D u ξ hξ)
  have hc : DifferentiableAt ℂ (fun x : ℂ => ((x, w, z) : ℂ × ℂ × ℂ)) ξ := by fun_prop
  exact h.comp ξ hc

private theorem rawKernel_continuous_heights (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ)
    (hξ : 1 + Scales.contourOffset / 2 ≤ ξ.re) :
    Continuous (fun p : ℝ × ℝ => rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
      ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) := by
  have hdiff : ∀ s t : ℝ, DifferentiableAt ℂ
      (fun p : ℂ × ℂ × ℂ => rawKernel D u p.1 p.2.1 p.2.2 Z)
      (ξ, (Scales.wLine : ℂ) + (s : ℂ) * Complex.I, (Scales.zLine : ℂ) + (t : ℂ) * Complex.I) := by
    intro s t
    have hw : ((Scales.wLine : ℂ) + (s : ℂ) * Complex.I).re = Scales.wLine := by simp
    have hz : ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I).re = Scales.zLine := by simp
    exact RawKernelRegularity31.rawKernel_differentiableAt D u hu Z hZ _
      (RowAnalyticContinuation.mem_OmegaStar_of_re ξ _ _ (xg_pad_le ξ hξ) hw hz)
      (by
        show (1 / 6 : ℝ) < ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I).re
        rw [hz]; unfold Scales.zLine; norm_num)
      (minus_ne D u ξ hξ)
  have hcont : Continuous (fun q : ℝ × ℝ => ((ξ, (Scales.wLine : ℂ) + (q.2 : ℂ) * Complex.I,
      (Scales.zLine : ℂ) + (q.1 : ℂ) * Complex.I) : ℂ × ℂ × ℂ)) := by fun_prop
  refine continuous_iff_continuousAt.2 fun q => ?_
  exact ContinuousAt.comp
    (f := fun q : ℝ × ℝ => ((ξ, (Scales.wLine : ℂ) + (q.2 : ℂ) * Complex.I,
      (Scales.zLine : ℂ) + (q.1 : ℂ) * Complex.I) : ℂ × ℂ × ℂ)) (x := q)
    (hdiff q.2 q.1).continuousAt hcont.continuousAt

theorem rawKernel_differentiableOn_xi (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 0 < Z) (w z : ℂ)
    (hw : w.re = Scales.wLine) (hz : z.re = Scales.zLine) :
    DifferentiableOn ℂ (fun ξ : ℂ => rawKernel D u ξ w z Z)
      {ξ : ℂ | 1 + Scales.contourOffset / 2 < ξ.re ∧ ξ.re < 5} := by
  intro ξ hξ
  have h : 1 + Scales.contourOffset / 2 < ξ.re := hξ.1
  exact (rawKernel_diffAt_xi D u hu Z hZ ξ h.le w z hw hz).differentiableWithinAt

private def stripV : Set ℂ := {ξ : ℂ | 1 + Scales.contourOffset / 2 < ξ.re ∧ ξ.re < 5}

private theorem mem_stripV {ξ : ℂ} : ξ ∈ stripV ↔ 1 + Scales.contourOffset / 2 < ξ.re ∧ ξ.re < 5 := Iff.rfl

private theorem stripV_open : IsOpen stripV := by
  unfold stripV
  exact IsOpen.and (isOpen_lt continuous_const Complex.continuous_re)
    (isOpen_lt Complex.continuous_re continuous_const)

theorem Iwz_differentiableOn_xi (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) :
    DifferentiableOn ℂ (fun ξ : ℂ => Iwz D u ξ Scales.wLine Scales.zLine Z)
      (comparisonClosedStrip Scales.rightLine 4) := by
  have hdiff : ∀ ξ ∈ stripV, ∀ s t : ℝ, DifferentiableAt ℂ
      (fun x : ℂ => rawKernel D u x ((Scales.wLine : ℂ) + (s : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I) Z) ξ := by
    intro ξ hξ s t
    have hw : ((Scales.wLine : ℂ) + (s : ℂ) * Complex.I).re = Scales.wLine := by simp
    have hz : ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I).re = Scales.zLine := by simp
    exact rawKernel_diffAt_xi D u hu Z hZ ξ (mem_stripV.1 hξ).1.le _ _ hw hz
  have hcont : ∀ ξ ∈ stripV, Continuous (fun p : ℝ × ℝ => rawKernel D u ξ
      ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I) ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z) :=
    fun ξ hξ => rawKernel_continuous_heights D u hu Z hZ ξ (mem_stripV.1 hξ).1.le
  have hmaj : ∀ ξ₀ ∈ stripV, ∃ r : ℝ, 0 < r ∧ Metric.ball ξ₀ r ⊆ stripV ∧ ∃ C k : ℝ,
      0 ≤ C ∧ 0 ≤ k ∧ ∀ ξ ∈ Metric.ball ξ₀ r, ∀ p : ℝ × ℝ,
        ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
            ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          C * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k := by
    obtain ⟨Cc, k, hCc, hk, hbd⟩ := rawKernel_weight_bound D u hu Z hZ
    intro ξ₀ hξ₀
    have hξ₀' := mem_stripV.1 hξ₀
    have hr : 0 < min (ξ₀.re - (1 + Scales.contourOffset / 2)) (5 - ξ₀.re) :=
      lt_min (by linarith [hξ₀'.1]) (by linarith [hξ₀'.2])
    have hball : Metric.ball ξ₀ (min (ξ₀.re - (1 + Scales.contourOffset / 2)) (5 - ξ₀.re)) ⊆ stripV := by
      intro ξ hξ
      have hd : dist ξ ξ₀ < min (ξ₀.re - (1 + Scales.contourOffset / 2)) (5 - ξ₀.re) := hξ
      have hre : |ξ.re - ξ₀.re| ≤ dist ξ ξ₀ := by
        rw [dist_eq_norm]
        have := Complex.abs_re_le_norm (ξ - ξ₀)
        rwa [Complex.sub_re] at this
      have h1 := (abs_le.1 hre)
      have h2 := min_le_left (ξ₀.re - (1 + Scales.contourOffset / 2)) (5 - ξ₀.re)
      have h3 := min_le_right (ξ₀.re - (1 + Scales.contourOffset / 2)) (5 - ξ₀.re)
      exact mem_stripV.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
    refine ⟨min (ξ₀.re - (1 + Scales.contourOffset / 2)) (5 - ξ₀.re), hr, hball, Cc, k, hCc, hk,
      fun ξ hξ p => ?_⟩
    have := mem_stripV.1 (hball hξ)
    exact hbd ξ this.1.le this.2.le p.1 p.2
  have hI : DifferentiableOn ℂ (fun ξ : ℂ => comparisonVerticalIntegral Scales.wLine (fun w =>
      comparisonVerticalIntegral Scales.zLine (fun z => rawKernel D u ξ w z Z))) stripV :=
    RowKernelHolomorphy.differentiableOn_nested_integral D stripV stripV_open
      (fun ξ w z => rawKernel D u ξ w z Z) Scales.wLine Scales.zLine z₀_pos' hdiff hcont hmaj
  have hsub : comparisonClosedStrip Scales.rightLine 4 ⊆ stripV := by
    intro ξ hξ
    have h1 : Scales.rightLine ≤ ξ.re := hξ.1
    have h2 : ξ.re ≤ 4 := hξ.2
    have h3 := x1_ge ξ h1
    have e1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
    have e3 : Scales.contourOffset = 1 / 10000000 := rfl
    exact mem_stripV.2 ⟨by linarith, by linarith⟩
  exact hI.mono hsub

theorem Iwz_decayOn_xi (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) :
    LowRowXiControls.DecayOn (fun ξ : ℂ => Iwz D u ξ Scales.wLine Scales.zLine Z) Scales.rightLine 4 := by
  obtain ⟨Cc, k, hCc0, hk, hbd⟩ := rawKernel_weight_bound D u hu Z hZ
  intro B hB
  obtain ⟨Cw, hCw0, hCw⟩ := KernelWeightIntegration.nested_integral_bound D Scales.zLine Scales.zLine
    Scales.wLine Scales.wLine Scales.rightLine 4 z₀_pos' le_rfl le_rfl
    (by rw [Scales.rightLine_eq]; norm_num) B k hB hk
  have key : ∀ ξ : ℂ, Scales.rightLine ≤ ξ.re → ξ.re ≤ 4 →
      ‖Iwz D u ξ Scales.wLine Scales.zLine Z‖ ≤
        ((2 * Real.pi)⁻¹) ^ 2 * (Cc * Cw * (1 + |ξ.im|) ^ (-B)) := by
    intro ξ h1 h4
    have h1' := x1_ge ξ h1
    have hcont := rawKernel_continuous_heights D u hu Z hZ ξ h1'
    have hbd' : ∀ p : ℝ × ℝ, ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
        ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
        Cc * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
          (2 + |p.1| + |p.2| + |ξ.im|) ^ k :=
      fun p => hbd ξ h1' (by linarith) p.1 p.2
    have hle := (hCw ξ h1 h4 Scales.zLine Scales.wLine le_rfl le_rfl le_rfl le_rfl Cc hCc0
      (fun w z => rawKernel D u ξ w z Z) hcont.aestronglyMeasurable hbd').2.2.2
    exact hle
  refine ⟨((2 * Real.pi)⁻¹) ^ 2 * (Cc * Cw), 0, ?_⟩
  intro x hx y _
  have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have h := key ((x : ℂ) + (y : ℂ) * Complex.I) (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2)
  rw [him] at h
  show ‖Iwz D u ((x : ℂ) + (y : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤ _
  refine h.trans (le_of_eq ?_)
  ring

theorem triple_xi_shift (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) :
    triple D u 4 Scales.wLine Scales.zLine Z = triple D u Scales.rightLine Scales.wLine Scales.zLine Z := by
  unfold triple
  exact LowRowXiControls.verticalIntegral_eq_of_decayOn (by norm_num [Scales.rightLine, Scales.contourOffset])
    (Iwz_differentiableOn_xi D u hu Z hZ) (Iwz_decayOn_xi D u hu Z hZ)

end

end DedekindZetaZeroFree.Quantitative.RawLowXiControls31
