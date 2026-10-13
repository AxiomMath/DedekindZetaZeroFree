module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.FrequencyLocalBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyRightBounds
public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyCount
public import DedekindZetaZeroFree.Moments.Probes.Poisson.KernelRegularity
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.XiControls

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLowZControls31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem z₀_eq' : Scales.zLine = 2 / 5 := rfl

theorem y₀_eq' : Scales.wLine = 3 / 25 := rfl

theorem pad_eq' : EulerDomain.pad = 1 / 1000000 := rfl

theorem mem_margin_z (ξ w z : ℂ) (hξ : ξ.re = 4) (hw : Scales.wLine ≤ w.re ∧ w.re ≤ 4)
    (hz : 2 / 5 ≤ z.re ∧ z.re ≤ 2) :
    (ξ, w, z) ∈ EulerDomain.OmegaStarMargin (1 / 20) := by
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨hz1, hz2⟩ := hz
  rw [y₀_eq'] at hw1
  simp only [EulerDomain.OmegaStarMargin, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_omega_strip (ξ w z : ℂ) (hξ : ξ.re = 4) (hw : Scales.wLine ≤ w.re ∧ w.re ≤ 4)
    (hz : Scales.zLine - EulerDomain.pad / 2 < z.re ∧ z.re < 3) :
    (ξ, w, z) ∈ EulerDomain.OmegaStar := by
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨hz1, hz2⟩ := hz
  rw [y₀_eq'] at hw1
  rw [z₀_eq', pad_eq'] at hz1
  simp only [EulerDomain.OmegaStar, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem rawKernel_differentiableOn_z (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4)
    (hw : Scales.wLine ≤ w.re ∧ w.re ≤ 4) :
    DifferentiableOn ℂ (fun z : ℂ => rawKernel D u ξ w z Z)
      {z : ℂ | Scales.zLine - EulerDomain.pad / 2 < z.re ∧ z.re < 3} := by
  intro z hz
  by_cases hm : (pkg D).minus u ξ = 0
  · have : (fun z : ℂ => rawKernel D u ξ w z Z) = fun _ => 0 := by
      funext z
      simp [rawKernel, rawFactor, hm]
    rw [this]
    exact differentiableWithinAt_const 0
  · have hmem := mem_omega_strip ξ w z hξ hw hz
    have hz6 : 1 / 6 < (ξ, w, z).2.2.re := by
      have h1 : Scales.zLine - EulerDomain.pad / 2 < z.re := hz.1
      rw [z₀_eq', pad_eq'] at h1
      show 1 / 6 < z.re
      linarith
    have h := RawKernelRegularity31.rawKernel_differentiableAt D u hu Z hZ (ξ, w, z) hmem hz6 hm
    have hc : DifferentiableAt ℂ (fun z : ℂ => ((ξ, w, z) : ℂ × ℂ × ℂ)) z := by fun_prop
    exact (h.comp z hc).differentiableWithinAt

theorem norm_cpow_Z_le (Z : ℝ) (hZ : 0 < Z) (c : ℂ) (A : ℝ) (hA : |c.re| ≤ A) :
    ‖(Z : ℂ) ^ c‖ ≤ Real.exp (|Real.log Z| * A) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ, Real.rpow_def_of_pos hZ]
  apply Real.exp_le_exp.mpr
  have h1 := le_abs_self (Real.log Z * c.re)
  rw [abs_mul] at h1
  have h2 : |Real.log Z| * |c.re| ≤ |Real.log Z| * A :=
    mul_le_mul_of_nonneg_left hA (abs_nonneg _)
  linarith

theorem norm_exp_sq_le (ξ z : ℂ) (hξ : ξ.re = 4) (hz : 2 / 5 ≤ z.re ∧ z.re ≤ 2) :
    ‖Complex.exp ((ξ + z - 1) ^ 2)‖ ≤ Real.exp 25 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have e : ((ξ + z - 1) ^ 2).re = (ξ.re + z.re - 1) * (ξ.re + z.re - 1) -
      (ξ.im + z.im) * (ξ.im + z.im) := by
    simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.add_im,
      Complex.sub_im, Complex.one_re, Complex.one_im] <;> ring
  rw [e, hξ]
  nlinarith [mul_self_nonneg (ξ.im + z.im), mul_nonneg (sub_nonneg.2 hz.2)
    (by linarith [hz.1] : (0 : ℝ) ≤ 8 + z.re)]

theorem kernel_norm_le_M (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : Scales.wLine ≤ w.re ∧ w.re ≤ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 2 / 5 ≤ z.re → z.re ≤ 2 →
      ‖rawKernel D u ξ w z Z‖ ≤ K * ‖D.M z‖ := by
  obtain ⟨CL, hCL0, hCL⟩ := RawRightHecke31.recipe_L_right D (2 / 5) (by norm_num)
  obtain ⟨CP, hCP0, hCP⟩ := RawEulerLocal31.correctionProduct_subpower D (1 / 20) (by norm_num)
    (1 / 2) (by norm_num)
  obtain ⟨X, hX0, hX⟩ : ∃ X : ℝ, 0 ≤ X ∧ ∀ z : ℂ, 2 / 5 ≤ z.re → z.re ≤ 2 →
      ‖AllRowEuler.InitialSeparation.correctionProduct D.context (rawFrequency D u) ξ w z‖ ≤ X :=
    ⟨|CP * RawEulerLocal31.rawQ D (rawFrequency D u) ^ (1 / 2 : ℝ)|, abs_nonneg _,
      fun z hz1 hz2 => le_trans (hCP _ _ (mem_margin_z ξ w z hξ hw ⟨hz1, hz2⟩)).2 (le_abs_self _)⟩

  obtain ⟨E1, hE10, hE1⟩ : ∃ E1 : ℝ, 0 ≤ E1 ∧ ∀ z : ℂ, 2 / 5 ≤ z.re → z.re ≤ 2 →
      ‖(Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
        (Scales.yExponent : ℂ) * (w - 1))‖ ≤ E1 := by
    refine ⟨Real.exp (|Real.log Z| * (|Scales.xExponent / 2 + ξ.re - 1 + Scales.yExponent * (w.re - 1)| +
      |Scales.smoothingExponent| * 2)), Real.exp_nonneg _, fun z hz1 hz2 => ?_⟩
    apply norm_cpow_Z_le Z hZ
    have hre : (((Scales.xExponent / 2 : ℝ) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
        (Scales.yExponent : ℂ) * (w - 1)).re =
        (Scales.xExponent / 2 + ξ.re - 1 + Scales.yExponent * (w.re - 1)) + Scales.smoothingExponent * z.re := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im]
      ring
    rw [hre]
    have hhz : |Scales.smoothingExponent * z.re| ≤ |Scales.smoothingExponent| * 2 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith) (abs_nonneg _)
    have hk := abs_le.mp hhz
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Scales.xExponent / 2 + ξ.re - 1 + Scales.yExponent * (w.re - 1))]
    · linarith [le_abs_self (Scales.xExponent / 2 + ξ.re - 1 + Scales.yExponent * (w.re - 1))]
  have hqb : ∀ z : ℂ, 0 ≤ z.re → ‖((frequencyNorm D.recipe u : ℝ) : ℂ) ^ (-z)‖ ≤ 1 := by
    intro z hz
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le one_pos (RawFrequencyCount.one_le_frequencyNorm D.recipe u))]
    apply Real.rpow_le_one_of_one_le_of_nonpos
      (RawFrequencyCount.one_le_frequencyNorm D.recipe u)
    rw [Complex.neg_re]
    linarith
  have hE2 : 0 ≤ Real.exp 25 := Real.exp_nonneg _
  refine ⟨E1 * Real.exp 25 * ‖D.W1Hat w‖ * (CL * ‖(pkg D).plus u w‖ * X / ‖(pkg D).minus u ξ‖),
    ?_, ?_⟩
  · apply mul_nonneg (mul_nonneg (mul_nonneg hE10 hE2) (norm_nonneg _))
    exact div_nonneg (mul_nonneg (mul_nonneg hCL0.le (norm_nonneg _)) hX0) (norm_nonneg _)
  · intro z hz1 hz2
    have hmain : ‖rawKernel D u ξ w z Z‖ ≤ E1 * Real.exp 25 * ‖D.M z‖ * ‖D.W1Hat w‖ * 1 *
        (CL * ‖(pkg D).plus u w‖ * X / ‖(pkg D).minus u ξ‖) := by
      have hL := (hCL z (by linarith)).2.1
      have hA := hE1 z hz1 hz2
      have hB := norm_exp_sq_le ξ z hξ ⟨hz1, hz2⟩
      have hQ := hqb z (by linarith)
      have hXz := hX z hz1 hz2
      unfold rawKernel rawFactor
      simp only [norm_mul, norm_div]
      gcongr
    calc _ ≤ _ := hmain
      _ = _ := by ring

theorem M_decay_all (B : ℝ) (hB : 0 < B) :
    ∃ CM : ℝ, ∀ x : ℝ, 2 / 5 ≤ x → x ≤ 2 → ∀ y : ℝ,
      ‖D.M ((x : ℂ) + (y : ℂ) * I)‖ ≤ CM * (1 + |y|) ^ (-B) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, B ≤ n := ⟨⌈B⌉₊, Nat.le_ceil B⟩
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay (2 / 5) 2 (by norm_num) (by norm_num) n
  refine ⟨|CM|, fun x hx1 hx2 y => ?_⟩
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hM := hCM ((x : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hx1) (by rw [hre]; exact hx2)
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
  calc _ ≤ |CM| * (t ^ n)⁻¹ := h1
    _ ≤ |CM| * t ^ (-B) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

theorem kernel_decay_all (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : Scales.wLine ≤ w.re ∧ w.re ≤ 4)
    (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ x : ℝ, 2 / 5 ≤ x → x ≤ 2 → ∀ y : ℝ,
      ‖rawKernel D u ξ w ((x : ℂ) + (y : ℂ) * I) Z‖ ≤ C * (1 + |y|) ^ (-B) := by
  obtain ⟨K, hK0, hK⟩ := kernel_norm_le_M D u hu Z hZ ξ w hξ hw
  obtain ⟨CM, hCM⟩ := M_decay_all D B hB
  refine ⟨K * CM, fun x hx1 hx2 y => ?_⟩
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have h1 := hK ((x : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hx1) (by rw [hre]; exact hx2)
  calc _ ≤ K * ‖D.M ((x : ℂ) + (y : ℂ) * I)‖ := h1
    _ ≤ K * (CM * (1 + |y|) ^ (-B)) := mul_le_mul_of_nonneg_left (hCM x hx1 hx2 y) hK0
    _ = _ := by ring

theorem rawKernel_decayOn_z (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : Scales.wLine ≤ w.re ∧ w.re ≤ 4) :
    LowRowXiControls.DecayOn (fun z : ℂ => rawKernel D u ξ w z Z) Scales.zLine 2 := by
  intro B hB
  obtain ⟨C, hC⟩ := kernel_decay_all D u hu Z hZ ξ w hξ hw B hB
  refine ⟨C, 0, fun x hx y _ => ?_⟩
  have hx1 : 2 / 5 ≤ x := by
    have := hx.1
    rw [z₀_eq'] at this
    exact this
  exact hC x hx1 hx.2 y

theorem rawKernel_integrable_zline (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4)
    (hw : Scales.wLine ≤ w.re ∧ w.re ≤ 4) (v : ℝ) (hv : v ∈ Icc Scales.zLine 2) :
    Integrable (fun t : ℝ => rawKernel D u ξ w ((v : ℂ) + (t : ℂ) * I) Z) := by
  have hdiff := rawKernel_differentiableOn_z D u hu Z hZ ξ w hξ hw
  have hcont : Continuous (fun t : ℝ => ((v : ℂ) + (t : ℂ) * I)) := by fun_prop
  have hv1 : 2 / 5 ≤ v := by
    have := hv.1
    rw [z₀_eq'] at this
    exact this
  have hv2 : v ≤ 2 := hv.2
  have hmaps : ∀ t : ℝ, ((v : ℂ) + (t : ℂ) * I) ∈
      {z : ℂ | Scales.zLine - EulerDomain.pad / 2 < z.re ∧ z.re < 3} := by
    intro t
    have hre : ((v : ℂ) + (t : ℂ) * I).re = v := by simp
    show Scales.zLine - EulerDomain.pad / 2 < ((v : ℂ) + (t : ℂ) * I).re ∧
      ((v : ℂ) + (t : ℂ) * I).re < 3
    rw [hre, z₀_eq', pad_eq']
    constructor <;> linarith
  have hcontf : Continuous (fun t : ℝ => rawKernel D u ξ w ((v : ℂ) + (t : ℂ) * I) Z) :=
    hdiff.continuousOn.comp_continuous hcont hmaps
  have hint : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ))) := by
    have := integrable_one_add_norm (μ := MeasureTheory.volume) (E := ℝ) (r := 2)
      (by norm_num)
    simpa [Real.norm_eq_abs] using this
  obtain ⟨C, hC⟩ := kernel_decay_all D u hu Z hZ ξ w hξ hw 2 (by norm_num)
  refine Integrable.mono' (hint.const_mul C) hcontf.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  exact hC v hv1 hv2 t

theorem Iz_z_shift (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : Scales.wLine ≤ w.re ∧ w.re ≤ 4) :
    Iz D u ξ w 2 Z = Iz D u ξ w Scales.zLine Z := by
  unfold Iz
  refine LowRowXiControls.verticalIntegral_eq_of_decayOn (by norm_num [Scales.zLine]) ?_
    (rawKernel_decayOn_z D u hu Z hZ ξ w hξ hw)
  refine (rawKernel_differentiableOn_z D u hu Z hZ ξ w hξ hw).mono ?_
  intro z hz
  refine ⟨?_, ?_⟩
  · have := hz.1
    unfold EulerDomain.pad
    linarith
  · have := hz.2
    linarith

end

end DedekindZetaZeroFree.Quantitative.RawLowZControls31
