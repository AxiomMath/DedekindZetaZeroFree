module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.LowKernel
public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelGrowth

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.LowRowZControls

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

theorem q_pos_aux (u : D.Row) : 0 < D.q u :=
  lt_of_lt_of_le one_pos (ActualRowCount.one_le_q D u)

theorem mem_OmegaStar_strip (ξ w z : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4)
    (hz : z ∈ comparisonClosedStrip Scales.zLine 2) :
    (ξ, w, z) ∈ EulerDomain.OmegaStar := by
  obtain ⟨h3, _⟩ := hz
  unfold Scales.zLine at h3
  have hz0 : 2 / 5 ≤ z.re := h3
  show 0 < ξ.re ∧ 0 < w.re ∧ 0 < z.re ∧ 1 < 6 * z.re + w.re ∧ 1 < ξ.re + 6 * z.re ∧
    1 < ξ.re + w.re ∧ 2 < ξ.re + w.re + 6 * z.re ∧ 5 < 6 * ξ.re + 6 * z.re ∧ 1 / 2 < ξ.re ∧
    2 < 3 * ξ.re ∧ 5 / 2 < 3 * ξ.re + w.re
  rw [hξ, hw]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem kernel_z_holo (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) :
    DifferentiableOn ℂ (fun z => PoissonKernel.K D u ξ w z Z)
      (comparisonClosedStrip Scales.zLine 2) := by
  intro z hz
  have hmem := mem_OmegaStar_strip ξ w z hξ hw hz
  have hz6 : 6 * z ≠ 1 := by
    intro h
    have h1 := congrArg Complex.re h
    simp at h1
    have h3 : 2 / 5 ≤ z.re := by
      have := hz.1
      unfold Scales.zLine at this
      exact this
    linarith
  have hL : D.Llam u ξ ≠ 0 :=
    RightHeckeBounds.Llam_ne_zero_of_one_lt D u ξ (by rw [hξ]; norm_num)
  have hK := RowAnalyticContinuation.K_differentiableAt D u hu (q_pos_aux D u) Z hZ ξ w z
    hmem hz6 hL
  have hc : DifferentiableAt ℂ (fun z : ℂ => (ξ, w, z)) z := by fun_prop
  exact (hK.comp z hc).differentiableWithinAt

theorem kernel_z_norm_bound (u : D.Row) (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (2 / 5 : ℝ) 2 →
      ‖PoissonKernel.K D u ξ w z Z‖ ≤ C * ‖D.M z‖ := by
  obtain ⟨Cz, hCz0, hCz⟩ := RightHeckeBounds.zetaSCont_norm_le_right D (12 / 5) (by norm_num)
  obtain ⟨CH, hCH0, hCH⟩ := RowKernelGrowth.Hu_box_bound D 1 one_pos
  have hq1 : 1 ≤ D.q u := ActualRowCount.one_le_q D u
  have hq0 : 0 < D.q u := lt_of_lt_of_le one_pos hq1
  obtain ⟨Cq, hCq0, hCq⟩ : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ z : ℂ, z.re ∈ Icc (2 / 5 : ℝ) 2 →
      ‖EulerDomain.Hu D u ξ w z‖ ≤ Cq :=
    ⟨CH * D.q u ^ (1 : ℝ), mul_nonneg hCH0.le (Real.rpow_nonneg hq0.le _), fun z hz =>
      hCH u ξ w z (by rw [hξ]; unfold Scales.goodLine; norm_num)
        (by rw [hw]; unfold Scales.wLine; norm_num) hz.1⟩
  refine ⟨Real.exp (6 * |Real.log Z|) * Real.exp 25 * ‖D.W1Hat w‖ *
    (Cz * ‖D.Lpsi u w‖ / ‖D.Llam u ξ‖ * Cq), by positivity, ?_⟩
  intro z hz
  have h1 : ‖(Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
      (Scales.yExponent : ℂ) * (w - 1))‖ ≤ Real.exp (6 * |Real.log Z|) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ, Real.rpow_def_of_pos hZ]
    apply Real.exp_le_exp.mpr
    have hre : (((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
        (Scales.yExponent : ℂ) * (w - 1)).re =
        Scales.xExponent / 2 + 4 - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (4 - 1) := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, hξ, hw]
      ring
    rw [hre]
    have hr0 : 0 ≤ Scales.xExponent / 2 + 4 - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (4 - 1) := by
      unfold Scales.xExponent Scales.smoothingExponent Scales.yExponent
      nlinarith [hz.1, hz.2]
    have hr5 : Scales.xExponent / 2 + 4 - 1 + Scales.smoothingExponent * z.re + Scales.yExponent * (4 - 1) ≤ 6 := by
      unfold Scales.xExponent Scales.smoothingExponent Scales.yExponent
      nlinarith [hz.1, hz.2]
    have hl := abs_nonneg (Real.log Z)
    have := le_abs_self (Real.log Z)
    nlinarith [mul_nonneg hr0 (sub_nonneg.2 this), mul_le_mul_of_nonneg_right hr5 hl]
  have h2 : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ ≤ Real.exp 25 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have e : ((ξ + z - 1) ^ 2).re = (ξ.re + z.re - 1) * (ξ.re + z.re - 1) -
        (ξ.im + z.im) * (ξ.im + z.im) := by
      simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.add_im,
        Complex.sub_im, Complex.one_re, Complex.one_im] <;> ring
    rw [e, hξ]
    nlinarith [mul_self_nonneg (ξ.im + z.im), mul_nonneg (sub_nonneg.2 hz.2)
      (by linarith [hz.1] : (0 : ℝ) ≤ 8 + z.re)]
  have h4 : ‖(D.q u : ℂ) ^ (-z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hq1
    rw [Complex.neg_re]
    linarith [hz.1]
  have h5 : ‖D.zetaSCont (6 * z)‖ ≤ Cz := by
    apply hCz
    have : (6 * z).re = 6 * z.re := by simp
    rw [this]
    linarith [hz.1]
  have h7 := hCq z hz
  unfold PoissonKernel.K PoissonKernel.kernelWith PoissonKernel.rowFactor
  simp only [norm_mul, norm_div]
  calc _ ≤ Real.exp (6 * |Real.log Z|) * Real.exp 25 * ‖D.M z‖ * ‖D.W1Hat w‖ * 1 *
        (Cz * ‖D.Lpsi u w‖ / ‖D.Llam u ξ‖ * Cq) := by gcongr
    _ = _ := by ring

theorem kernel_z_decay (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) :
    DecayOn (fun z => PoissonKernel.K D u ξ w z Z) Scales.zLine 2 := by
  intro B hB
  obtain ⟨C0, hC0, hK⟩ := kernel_z_norm_bound D u Z hZ ξ w hξ hw
  obtain ⟨n, hn⟩ : ∃ n : ℕ, B ≤ n := ⟨⌈B⌉₊, Nat.le_ceil B⟩
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay Scales.zLine 2 (by unfold Scales.zLine; norm_num)
    (by unfold Scales.zLine; norm_num) n
  refine ⟨C0 * |CM|, 0, ?_⟩
  intro x hx y _
  have hre : (((x : ℂ) + (y : ℂ) * I)).re = x := by simp
  have him : (((x : ℂ) + (y : ℂ) * I)).im = y := by simp
  have hx' : x ∈ Icc (2 / 5 : ℝ) 2 := by
    have := hx.1
    unfold Scales.zLine at this
    exact ⟨this, hx.2⟩
  have hKz := hK _ (by rw [hre]; exact hx')
  have hM := hCM ((x : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2)
  rw [him] at hM
  set t : ℝ := 1 + |y| with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith [abs_nonneg y]
  have ht0 : 0 < t := by linarith
  have htn : 0 < t ^ n := pow_pos ht0 n
  have h1 : ‖D.M ((x : ℂ) + (y : ℂ) * I)‖ ≤ |CM| * (t ^ n)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ htn]
    nlinarith [le_abs_self CM]
  have h2 : (t ^ n)⁻¹ ≤ t ^ (-B) := by
    rw [Real.rpow_neg ht0.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos ht0 B)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht1 hn
  calc _ ≤ C0 * ‖D.M ((x : ℂ) + (y : ℂ) * I)‖ := hKz
    _ ≤ C0 * (|CM| * (t ^ n)⁻¹) := by gcongr
    _ ≤ C0 * (|CM| * t ^ (-B)) := by gcongr
    _ = _ := by ring

theorem Iz_shift (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) :
    Iz D u ξ w 2 Z = Iz D u ξ w Scales.zLine Z := by
  unfold Iz
  exact verticalIntegral_eq_of_decayOn (by norm_num [Scales.zLine])
    (kernel_z_holo D u hu Z hZ ξ w hξ hw) (kernel_z_decay D u hu Z hZ ξ w hξ hw)

end

end DedekindZetaZeroFree.Quantitative.LowRowZControls
