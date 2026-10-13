module

public import DedekindZetaZeroFree.Moments.Principal.Contour.RightKernelBound
public import DedekindZetaZeroFree.Analysis.Integration.HolomorphicDominatedIntegral

@[expose] public section

set_option maxHeartbeats 1000000

namespace DedekindZetaZeroFree.Quantitative.PrincipalIntegratedWControls

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions DedekindZetaZeroFree.Quantitative.PrincipalStripBasicDefinitions
  DedekindZetaZeroFree.Quantitative.PrincipalRightKernelBound31 DedekindZetaZeroFree.Quantitative.EulerDomain
  Set Filter Complex MeasureTheory Metric
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma dom_mem (ξ w z : ℂ) (hξ : Scales.rightLine ≤ ξ.re) (hw : 1 < w.re)
    (hz : z.re = 1 / 6 + Scales.contourOffset) :
    ((ξ, w, z) : Coordinates) ∈ (paddedBox₂ ∩ {p : Coordinates | Scales.rightLine - Scales.contourOffset / 2 < p.1.re} ∩
        {p : Coordinates | 1 / 6 + Scales.contourOffset / 2 < p.2.2.re}) \ {p : Coordinates | p.2.1 = 1} := by
  have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
  have hδ : Scales.contourOffset = 1 / 10000000 := rfl
  have hδp : (0 : ℝ) < Scales.contourOffset := by rw [hδ]; norm_num
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show Scales.rightLine - pad ≤ ξ.re
    unfold pad; linarith
  · show 9 / 10 - pad ≤ w.re
    unfold pad; linarith
  · show 1 / 6 + Scales.contourOffset - pad ≤ z.re
    unfold pad; rw [hz]; linarith
  · show Scales.rightLine - Scales.contourOffset / 2 < ξ.re
    linarith
  · show 1 / 6 + Scales.contourOffset / 2 < z.re
    rw [hz]; linarith
  · exact hw1

set_option maxHeartbeats 4000000 in

private lemma kern_w_diff (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) (ξ z : ℂ)
    (hξ : Scales.rightLine ≤ ξ.re) (hz : z.re = 1 / 6 + Scales.contourOffset) :
    DifferentiableOn ℂ (fun w => kern D u Z ξ w z) {w : ℂ | 1 < w.re} := by
  have hk := kern_differentiableOn D u hu Z hZ
  have hmaps : MapsTo (fun w : ℂ => ((ξ, w, z) : Coordinates)) {w : ℂ | 1 < w.re}
      ((paddedBox₂ ∩ {p : Coordinates | Scales.rightLine - Scales.contourOffset / 2 < p.1.re} ∩
        {p : Coordinates | 1 / 6 + Scales.contourOffset / 2 < p.2.2.re}) \ {p : Coordinates | p.2.1 = 1}) :=
    fun w hw => dom_mem ξ w z hξ hw hz
  have hf : DifferentiableOn ℂ (fun w : ℂ => ((ξ, w, z) : Coordinates)) {w : ℂ | 1 < w.re} :=
    (differentiableOn_const ξ).prodMk (differentiableOn_id.prodMk (differentiableOn_const z))
  have key := DifferentiableOn.comp
    (g := fun p : Coordinates => kern D u Z p.1 p.2.1 p.2.2)
    (f := fun w : ℂ => ((ξ, w, z) : Coordinates)) (s := {w : ℂ | 1 < w.re}) hk hf hmaps
  exact key

set_option maxHeartbeats 4000000 in

private lemma kern_t_cont (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) (ξ w a : ℂ)
    (hξ : Scales.rightLine ≤ ξ.re) (hw : 1 < w.re) (ha : a.re = 1 / 6 + Scales.contourOffset) :
    Continuous (fun t : ℝ => kern D u Z ξ w (a + (t : ℂ) * I)) := by
  have hk := kern_differentiableOn D u hu Z hZ
  have hc : Continuous (fun t : ℝ => ((ξ, w, a + (t : ℂ) * I) : Coordinates)) :=
    continuous_const.prodMk (continuous_const.prodMk
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)))
  have hmem : ∀ t : ℝ, ((ξ, w, a + (t : ℂ) * I) : Coordinates) ∈
      ((paddedBox₂ ∩ {p : Coordinates | Scales.rightLine - Scales.contourOffset / 2 < p.1.re} ∩
        {p : Coordinates | 1 / 6 + Scales.contourOffset / 2 < p.2.2.re}) \ {p : Coordinates | p.2.1 = 1}) :=
    fun t => dom_mem ξ w (a + (t : ℂ) * I) hξ hw (by rw [Complex.add_re, ha]; simp)
  have key := ContinuousOn.comp_continuous
    (g := fun p : Coordinates => kern D u Z p.1 p.2.1 p.2.2)
    (f := fun t : ℝ => ((ξ, w, a + (t : ℂ) * I) : Coordinates)) hk.continuousOn hc hmem
  exact key

private lemma hgauss (c : ℝ) : Integrable (fun t : ℝ => Real.exp (-(c + t) ^ 2)) := by
  have := (integrable_exp_neg_mul_sq one_pos).comp_add_right c
  refine this.congr (Eventually.of_forall fun t => ?_)
  show Real.exp _ = Real.exp _
  congr 1
  ring

theorem Iz_w_holo (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) :
    DifferentiableOn ℂ (fun w => Iz D u Z (1 / 6 + Scales.contourOffset) ξ w)
      (comparisonClosedStrip Scales.rightLine 4) := by
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hδ : Scales.contourOffset = 1 / 10000000 := rfl
  have hξ1 : Scales.rightLine ≤ ξ.re := hξ.1
  obtain ⟨Ck, hCk, hk⟩ := kernel_factor_bound D u hu Z hZ
  obtain ⟨KW, hKW⟩ := D.W1Hat_vertical_decay (Scales.rightLine - Scales.contourOffset / 2) 5
    (by rw [hx1, hδ]; norm_num) 0
  have hv : (0 : ℝ) < 1 / 6 + Scales.contourOffset := by rw [hδ]; norm_num
  obtain ⟨KM, hKM⟩ := D.M_vertical_decay (1 / 6 + Scales.contourOffset) (1 / 6 + Scales.contourOffset) hv le_rfl 0
  have hMb : ∀ z : ℂ, z.re = 1 / 6 + Scales.contourOffset → ‖D.M z‖ ≤ KM := fun z hz => by
    have := hKM z (by rw [hz]) (by rw [hz])
    simpa using this
  have hKM0 : 0 ≤ KM := le_trans (norm_nonneg _) (hMb ((1 / 6 + Scales.contourOffset : ℝ) : ℂ) (by simp))
  have hKW' : ∀ w : ℂ, Scales.rightLine - Scales.contourOffset / 2 ≤ w.re → w.re ≤ 5 → ‖D.W1Hat w‖ ≤ KW :=
    fun w h1 h2 => by
      have := hKW w h1 h2
      simpa using this
  set U : Set ℂ := {w : ℂ | Scales.rightLine - Scales.contourOffset / 4 < w.re} ∩ {w : ℂ | w.re < 5} with hUdef
  have hUmem : ∀ w : ℂ, w ∈ U ↔ Scales.rightLine - Scales.contourOffset / 4 < w.re ∧ w.re < 5 := fun w => Iff.rfl
  have hδp : (0 : ℝ) < Scales.contourOffset := by rw [hδ]; norm_num
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have h1U : (1 : ℝ) < Scales.rightLine - Scales.contourOffset / 4 := by rw [hx1, hδ]; norm_num
  have hUsub : U ⊆ {w : ℂ | 1 < w.re} := fun w hw => lt_trans h1U hw.1
  have hdiff : ∀ t : ℝ, DifferentiableOn ℂ
      (fun w => kern D u Z ξ w (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)) U :=
    fun t => (kern_w_diff D u hu Z hZ0 ξ (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I) hξ1
      (by rw [Complex.add_re, Complex.ofReal_re]; simp)).mono hUsub
  have hmeas : ∀ w ∈ U, AEStronglyMeasurable
      (fun t : ℝ => kern D u Z ξ w (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)) volume :=
    fun w hw => (kern_t_cont D u hu Z hZ0 ξ w (((1 / 6 + Scales.contourOffset : ℝ) : ℂ)) hξ1 (hUsub hw)
      (Complex.ofReal_re _)).aestronglyMeasurable
  have hdom : ∀ z0 ∈ U, ∃ r > 0, Metric.ball z0 r ⊆ U ∧
      ∃ g : ℝ → ℝ, Integrable g volume ∧ ∀ z ∈ Metric.ball z0 r, ∀ p : ℝ,
        ‖kern D u Z ξ z (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I)‖ ≤ g p := by
    intro z0 hz0
    have hz1 : Scales.rightLine - Scales.contourOffset / 4 < z0.re := hz0.1
    have hz2 : z0.re < 5 := hz0.2
    have hr : 0 < min ((z0.re - (Scales.rightLine - Scales.contourOffset / 4)) / 2) ((5 - z0.re) / 2) :=
      lt_min (by linarith) (by linarith)
    refine ⟨min ((z0.re - (Scales.rightLine - Scales.contourOffset / 4)) / 2) ((5 - z0.re) / 2), hr, ?_, ?_⟩
    · intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hre := Complex.abs_re_le_norm (w - z0)
      rw [Complex.sub_re] at hre
      have hab := abs_sub_lt_iff.1 (lt_of_le_of_lt hre hw)
      have m1 := min_le_left ((z0.re - (Scales.rightLine - Scales.contourOffset / 4)) / 2) ((5 - z0.re) / 2)
      have m2 := min_le_right ((z0.re - (Scales.rightLine - Scales.contourOffset / 4)) / 2) ((5 - z0.re) / 2)
      exact (hUmem w).2 ⟨by linarith [lt_of_lt_of_le hab.2 m1, hz1], by linarith [lt_of_lt_of_le hab.1 m2, hz2]⟩
    · refine ⟨fun t => (Ck * KW * KM) * Real.exp (-(ξ.im + t) ^ 2),
        (hgauss ξ.im).const_mul _, ?_⟩
      intro z hz p
      have hzU : z ∈ U := by
        have m1 := min_le_left ((z0.re - (Scales.rightLine - Scales.contourOffset / 4)) / 2) ((5 - z0.re) / 2)
        have m2 := min_le_right ((z0.re - (Scales.rightLine - Scales.contourOffset / 4)) / 2) ((5 - z0.re) / 2)
        rw [Metric.mem_ball, dist_eq_norm] at hz
        have hre := Complex.abs_re_le_norm (z - z0)
        rw [Complex.sub_re] at hre
        have hab := abs_sub_lt_iff.1 (lt_of_le_of_lt hre hz)
        exact (hUmem z).2 ⟨by linarith [lt_of_lt_of_le hab.2 m1, hz1], by linarith [lt_of_lt_of_le hab.1 m2, hz2]⟩
      have hzre1 : Scales.rightLine - Scales.contourOffset / 2 ≤ z.re := by linarith [((hUmem z).1 hzU).1]
      have hzre2 : z.re ≤ 5 := le_of_lt ((hUmem z).1 hzU).2
      have hz' : ‖kern D u Z ξ z (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I)‖ ≤
          Ck * ‖D.W1Hat z‖ * ‖D.M (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I)‖ *
            Real.exp (-(ξ.im + p) ^ 2) := by
        have hz : (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I).re = 1 / 6 + Scales.contourOffset := by simp
        have hzi : (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I).im = p := by simp
        have h := hk ξ z _ hξ1 hξ.2 hzre1 hzre2 hz
        rw [hzi] at h
        exact h
      have hW := hKW' z hzre1 hzre2
      have hM := hMb (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I) (by simp)
      have hE := Real.exp_pos (-(ξ.im + p) ^ 2)
      have hW0 := norm_nonneg (D.W1Hat z)
      have hM0 := norm_nonneg (D.M (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I))
      refine le_trans hz' ?_
      have hCW : 0 ≤ Ck * ‖D.W1Hat z‖ := mul_nonneg hCk hW0
      have h2 : Ck * ‖D.W1Hat z‖ * ‖D.M (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I)‖ ≤
          Ck * KW * KM := by
        calc Ck * ‖D.W1Hat z‖ * ‖D.M (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (p : ℂ) * I)‖
            ≤ Ck * ‖D.W1Hat z‖ * KM := mul_le_mul_of_nonneg_left hM hCW
          _ ≤ Ck * KW * KM := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW hKM0) hCk
      exact mul_le_mul_of_nonneg_right h2 hE.le
  have hint := HolomorphicDominatedIntegral.differentiableOn_integral_of_locally_dominated
    (μ := volume) hUo hmeas hdiff hdom
  have hfull : DifferentiableOn ℂ (fun w => (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
      kern D u Z ξ w (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)) U :=
    hint.const_mul _
  have hsub : comparisonClosedStrip Scales.rightLine 4 ⊆ U := by
    intro w hw
    have hw' : Scales.rightLine ≤ w.re ∧ w.re ≤ 4 := hw
    exact (hUmem w).2 ⟨by linarith [hw'.1, hδp], by linarith [hw'.2]⟩
  exact hfull.mono hsub

theorem Iz_w_decay (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ)
    (hξ : ξ.re ∈ Icc Scales.rightLine 4) :
    DecayOn (fun w => Iz D u Z (1 / 6 + Scales.contourOffset) ξ w) Scales.rightLine 4 := by
  intro B hB
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hδ : Scales.contourOffset = 1 / 10000000 := rfl
  have hξ1 : Scales.rightLine ≤ ξ.re := hξ.1
  obtain ⟨Ck, hCk, hk⟩ := kernel_factor_bound D u hu Z hZ
  have hv : (0 : ℝ) < 1 / 6 + Scales.contourOffset := by rw [hδ]; norm_num
  obtain ⟨KM, hKM⟩ := D.M_vertical_decay (1 / 6 + Scales.contourOffset) (1 / 6 + Scales.contourOffset) hv le_rfl 0
  have hMb : ∀ z : ℂ, z.re = 1 / 6 + Scales.contourOffset → ‖D.M z‖ ≤ KM := fun z hz => by
    have := hKM z (by rw [hz]) (by rw [hz])
    simpa using this
  have hKM0 : 0 ≤ KM := le_trans (norm_nonneg _) (hMb ((1 / 6 + Scales.contourOffset : ℝ) : ℂ) (by simp))
  set I0 : ℝ := ∫ t : ℝ, Real.exp (-(ξ.im + t) ^ 2) with hI0def
  have hI0 : 0 ≤ I0 := integral_nonneg fun t => (Real.exp_pos _).le
  set A : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖ * Ck * KM * I0 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    have := norm_nonneg ((2 * (Real.pi : ℂ))⁻¹)
    exact mul_nonneg (mul_nonneg (mul_nonneg this hCk) hKM0) hI0
  obtain ⟨Cw, hCw⟩ := D.W1Hat_vertical_decay Scales.rightLine 4 (by rw [hx1, hδ]; norm_num) ⌈B⌉₊
  refine ⟨A * Cw, 0, fun x hx y _ => ?_⟩
  show ‖Iz D u Z (1 / 6 + Scales.contourOffset) ξ ((x : ℂ) + (y : ℂ) * I)‖ ≤ (A * Cw) * (1 + |y|) ^ (-B)
  have hwre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have hwim : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hxa : Scales.rightLine - Scales.contourOffset / 2 ≤ ((x : ℂ) + (y : ℂ) * I).re := by
    rw [hwre]; linarith [hx.1]
  have hxb : ((x : ℂ) + (y : ℂ) * I).re ≤ 5 := by rw [hwre]; linarith [hx.2]
  have hxb4 : ((x : ℂ) + (y : ℂ) * I).re ≤ 4 := by rw [hwre]; exact hx.2
  have hxa' : Scales.rightLine ≤ ((x : ℂ) + (y : ℂ) * I).re := by rw [hwre]; exact hx.1
  have hIz : ‖Iz D u Z (1 / 6 + Scales.contourOffset) ξ ((x : ℂ) + (y : ℂ) * I)‖ ≤
      A * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ := by
    show ‖(2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
      kern D u Z ξ ((x : ℂ) + (y : ℂ) * I) (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ _
    rw [norm_mul]
    have hpt : ∀ t : ℝ, ‖kern D u Z ξ ((x : ℂ) + (y : ℂ) * I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        (Ck * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ * KM) * Real.exp (-(ξ.im + t) ^ 2) := by
      intro t
      have hz : (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I).re = 1 / 6 + Scales.contourOffset := by simp
      have hzi : (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
      have h := hk ξ ((x : ℂ) + (y : ℂ) * I) _ hξ1 hξ.2 hxa hxb hz
      rw [hzi] at h
      have hM := hMb (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I) hz
      have hE := Real.exp_pos (-(ξ.im + t) ^ 2)
      have hCW : 0 ≤ Ck * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ :=
        mul_nonneg hCk (norm_nonneg _)
      refine le_trans h ?_
      apply mul_le_mul_of_nonneg_right _ hE.le
      exact mul_le_mul_of_nonneg_left hM hCW
    have hint : ‖∫ t : ℝ, kern D u Z ξ ((x : ℂ) + (y : ℂ) * I)
        (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ, (Ck * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ * KM) * Real.exp (-(ξ.im + t) ^ 2) :=
      norm_integral_le_of_norm_le ((hgauss ξ.im).const_mul _) (Eventually.of_forall hpt)
    rw [integral_const_mul] at hint
    calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖∫ t : ℝ, kern D u Z ξ ((x : ℂ) + (y : ℂ) * I)
          (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * ((Ck * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ * KM) * I0) :=
          mul_le_mul_of_nonneg_left hint (norm_nonneg _)
      _ = A * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ := by rw [hA]; ring
  have hs : 0 < (1 + |y|) ^ ⌈B⌉₊ := by positivity
  have hW : ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ ≤ Cw * ((1 + |y|) ^ ⌈B⌉₊)⁻¹ := by
    have h := hCw _ hxa' hxb4
    rw [hwim] at h
    rw [← div_eq_mul_inv, le_div_iff₀ hs, mul_comm]
    exact h
  have hCw0 : 0 ≤ Cw := le_trans (mul_nonneg (by positivity) (norm_nonneg _))
    (hCw _ hxa' hxb4)
  have hb : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hpow : ((1 + |y|) ^ ⌈B⌉₊)⁻¹ ≤ (1 + |y|) ^ (-B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith [abs_nonneg y])]
    exact Real.rpow_le_rpow_of_exponent_le hb (by linarith [Nat.le_ceil B])
  calc ‖Iz D u Z (1 / 6 + Scales.contourOffset) ξ ((x : ℂ) + (y : ℂ) * I)‖
      ≤ A * ‖D.W1Hat ((x : ℂ) + (y : ℂ) * I)‖ := hIz
    _ ≤ A * (Cw * ((1 + |y|) ^ ⌈B⌉₊)⁻¹) := mul_le_mul_of_nonneg_left hW hA0
    _ ≤ A * (Cw * (1 + |y|) ^ (-B)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCw0) hA0
    _ = (A * Cw) * (1 + |y|) ^ (-B) := by ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalIntegratedWControls
