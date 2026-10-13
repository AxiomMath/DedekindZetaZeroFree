module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.SubpowerBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.RightBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalBox2Majorant

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions DedekindZetaZeroFree.Quantitative.EulerDomain MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private def hh (t : ℝ) : ℝ := (1 + |t|) ^ (-2 : ℝ)

private lemma hh_pos (t : ℝ) : 0 < hh t := Real.rpow_pos_of_pos (by positivity) _

private lemma hh_integrable : Integrable hh := by
  have := integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ)) (r := 2) (by norm_num)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [hh, Real.norm_eq_abs]

private lemma le_hh {f C t : ℝ} (h : (1 + |t|) ^ 2 * f ≤ C) : f ≤ |C| * hh t := by
  have hp : 0 < (1 + |t|) ^ 2 := by positivity
  have h1 : hh t = ((1 + |t|) ^ 2)⁻¹ := by
    unfold hh
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [h1, ← div_eq_mul_inv, le_div_iff₀ hp]
  linarith [le_abs_self C, mul_comm f ((1 + |t|) ^ 2)]

private def gaussShear (p : ℝ × ℝ) : ℝ := Real.exp (-(p.1 + p.2) ^ 2) * hh p.2

private lemma gaussShear_nonneg (p : ℝ × ℝ) : 0 ≤ gaussShear p :=
  mul_nonneg (Real.exp_pos _).le (hh_pos _).le

private lemma gaussShear_integrable : Integrable gaussShear := by
  have hg : Integrable (fun x : ℝ => Real.exp (-(x) ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
  have h1 : Integrable (fun p : ℝ × ℝ => hh p.1 * Real.exp (-(p.2) ^ 2)) :=
    hh_integrable.mul_prod hg
  have h2 := (measurePreserving_prod_add_swap (volume : Measure ℝ)
    (volume : Measure ℝ)).integrable_comp_of_integrable h1
  refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp, gaussShear]
  rw [add_comm p.2 p.1, mul_comm]

private def tripleG (p : ℝ × ℝ × ℝ) : ℝ := gaussShear (p.1, p.2.2) * hh p.2.1

private lemma tripleG_nonneg (p : ℝ × ℝ × ℝ) : 0 ≤ tripleG p :=
  mul_nonneg (gaussShear_nonneg _) (hh_pos _).le

private lemma tripleG_integrable : Integrable tripleG := by
  have h : Integrable (fun q : (ℝ × ℝ) × ℝ => gaussShear q.1 * hh q.2) :=
    gaussShear_integrable.mul_prod hh_integrable
  have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.swap : ℝ × ℝ → ℝ × ℝ))
      (volume : Measure (ℝ × ℝ × ℝ)) (volume : Measure (ℝ × ℝ × ℝ)) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod MeasureTheory.Measure.measurePreserving_swap
  have h2 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ))
  have h3 := (h2.comp h1).integrable_comp_of_integrable h
  exact h3.congr (Filter.Eventually.of_forall fun p => rfl)

private lemma norm_kernel_principal (u : D.Row) (hq : D.q u = 1) (x y v Z : ℝ) (hZ : 0 < Z)
    (t : ℝ × ℝ × ℝ) :
    ‖kernelWith D (rowContLocal D) u ((x : ℂ) + (t.1 : ℂ) * Complex.I)
        ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ =
      Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) *
        ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ *
        ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
        (‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
          ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
          ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
            ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ *
          ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹) := by
  have hqc : ((D.q u : ℝ) : ℂ) = 1 := by rw [hq]; simp
  have hZn : ‖(Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) + ((x : ℂ) + (t.1 : ℂ) * Complex.I) - 1 +
      (Scales.smoothingExponent : ℂ) * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) +
      (Scales.yExponent : ℂ) * (((y : ℂ) + (t.2.1 : ℂ) * Complex.I) - 1))‖ = Z ^ (Scales.kernelExponent x y v) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    congr 1
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.one_re, Complex.one_im]
    unfold Scales.kernelExponent
    ring
  have hEn : ‖Complex.exp ((((x : ℂ) + (t.1 : ℂ) * Complex.I) +
      ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) - 1) ^ 2)‖ =
      Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.one_re, Complex.one_im]
    ring
  unfold kernelWith rowContLocal
  rw [hqc, Complex.one_cpow]
  simp only [norm_mul, norm_div, norm_one, hZn, hEn]
  rw [div_eq_mul_inv]
  ring

theorem kernel_majorant_paddedBox2 (u : D.Row) (hu : u.u = 1)
    (x₀ x₁ y₀ y₁ v₀ v₁ : ℝ)
    (hx : ∀ x ∈ Set.Icc x₀ x₁, Scales.rightLine - Scales.contourOffset / 2 ≤ x)
    (hy : ∀ y ∈ Set.Icc y₀ y₁, 9 / 10 - EulerDomain.pad ≤ y ∧ y ≠ 1)
    (hv : ∀ v ∈ Set.Icc v₀ v₁, 1 / 6 + Scales.contourOffset / 2 ≤ v) :
    ∃ g : ℝ × ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧
      ∀ x ∈ Set.Icc x₀ x₁, ∀ y ∈ Set.Icc y₀ y₁, ∀ v ∈ Set.Icc v₀ v₁, ∀ Z : ℝ, 2 ≤ Z →
        ∀ t : ℝ × ℝ × ℝ,
          ‖kernelWith D (rowContLocal D) u ((x : ℂ) + (t.1 : ℂ) * Complex.I)
              ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ ≤
            Z ^ (Scales.kernelExponent x y v) * g t := by
  have hq : D.q u = 1 := PrincipalResidueFormulas.q_principal D u hu
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hpad : EulerDomain.pad = 1 / 1000000 := rfl
  obtain ⟨Cz, hCz0, hCz⟩ := RightHeckeBounds.zetaSCont_norm_le_right D (1 + 3 * Scales.contourOffset)
    (by rw [hd]; norm_num)
  obtain ⟨Cl, hCl0, hCl⟩ := RightHeckeBounds.Llam_inv_norm_le_right D (1 + Scales.contourOffset / 2)
    (by rw [hd]; norm_num)
  obtain ⟨CH, hCH0, hCH⟩ := EulerSubpower.Hu_subpower D (1 / 100) (by norm_num) 1 one_pos
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay (1 / 6) (max v₁ 1) (by norm_num)
    (le_trans (by norm_num) (le_max_right _ _)) 2
  obtain ⟨CL, B, hCL0, hCL⟩ : ∃ C B : ℝ, 0 < C ∧ ∀ σ t : ℝ, σ ∈ Set.Icc y₀ y₁ →
      ‖D.Lpsi u ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ B := by
    by_cases hyy : y₀ ≤ y₁
    · have h0 : 0 < y₀ := by
        have := (hy y₀ ⟨le_rfl, hyy⟩).1
        rw [hpad] at this
        linarith
      have h1 : (1 : ℝ) ∉ Set.Icc y₀ y₁ := fun h => (hy 1 h).2 rfl
      obtain ⟨C, B, hC, hb⟩ :=
        RightHeckeBounds.Lpsi_polynomial_growth_principal D u hu y₀ y₁ h0 hyy h1
      exact ⟨C, B, hC, fun σ t hσ => hb σ t hσ⟩
    · exact ⟨1, 0, one_pos, fun σ t hσ => absurd (le_trans hσ.1 hσ.2) hyy⟩
  obtain ⟨CW, hCW⟩ := D.W1Hat_vertical_decay (min y₀ 0) (max y₁ 0)
    (le_trans (min_le_right _ _) (le_max_right _ _)) (⌈B⌉₊ + 2)
  set K : ℝ := Real.exp ((|x₀| + |x₁| + |v₀| + |v₁| + 1) ^ 2) * |CM| * |CL * CW| *
    (Cz * CH * Cl) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      (abs_nonneg _)) (mul_nonneg (mul_nonneg hCz0.le hCH0.le) hCl0.le)
  refine ⟨fun t => K * tripleG t, tripleG_integrable.const_mul _, fun t => ?_, ?_⟩
  · have := tripleG_nonneg t
    exact mul_nonneg hK0 this
  intro x hxI y hyI v hvI Z hZ2 t
  dsimp only
  have hZ0 : 0 < Z := by linarith
  have hx_lo : Scales.rightLine - Scales.contourOffset / 2 ≤ x := hx x hxI
  have hy_lo : 9 / 10 - EulerDomain.pad ≤ y := (hy y hyI).1
  have hv_lo : 1 / 6 + Scales.contourOffset / 2 ≤ v := hv v hvI
  have hxre : ((x : ℂ) + (t.1 : ℂ) * Complex.I).re = x := by simp
  have hyre : ((y : ℂ) + (t.2.1 : ℂ) * Complex.I).re = y := by simp
  have hvre : ((v : ℂ) + (t.2.2 : ℂ) * Complex.I).re = v := by simp
  have hyim : ((y : ℂ) + (t.2.1 : ℂ) * Complex.I).im = t.2.1 := by simp
  have hvim : ((v : ℂ) + (t.2.2 : ℂ) * Complex.I).im = t.2.2 := by simp
  have h6re : (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)).re = 6 * v := by simp
  have bZ : ‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ ≤ Cz :=
    hCz _ (by rw [h6re]; rw [hd] at hv_lo ⊢; linarith)
  have bP : ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ ≤ CL * (1 + |t.2.1|) ^ B :=
    hCL y t.2.1 hyI
  have bL : ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ ≤ Cl := by
    have := hCl u ((x : ℂ) + (t.1 : ℂ) * Complex.I) (by rw [hxre]; rw [hx1, hd] at hx_lo; linarith)
    rwa [norm_inv] at this
  have hmem : (((x : ℂ) + (t.1 : ℂ) * Complex.I, (y : ℂ) + (t.2.1 : ℂ) * Complex.I,
      (v : ℂ) + (t.2.2 : ℂ) * Complex.I) : Coordinates) ∈ OmegaStarMargin (1 / 100) := by
    simp only [OmegaStarMargin, Set.mem_setOf_eq]
    rw [hxre, hyre, hvre]
    rw [hx1, hd] at hx_lo
    rw [hpad] at hy_lo
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have bH : ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
      ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ ≤ CH := by
    have := (hCH u _ hmem).2
    rwa [hq, Real.one_rpow, mul_one] at this
  have bM : ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ ≤ |CM| * hh t.2.2 := by
    have := hCM ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) (by rw [hvre]; norm_num; linarith)
      (by rw [hvre]; exact le_trans hvI.2 (le_max_left _ _))
    rw [hvim] at this
    exact le_hh this
  have hWY : (1 + |t.2.1|) ^ (⌈B⌉₊ + 2) * ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ ≤ CW := by
    have := hCW ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
      (by rw [hyre]; exact le_trans (min_le_left _ _) hyI.1)
      (by rw [hyre]; exact le_trans hyI.2 (le_max_left _ _))
    rw [hyim] at this
    exact this
  have hLW : ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
      ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ ≤ |CL * CW| * hh t.2.1 := by
    have hp1 : (1 : ℝ) ≤ 1 + |t.2.1| := by linarith [abs_nonneg t.2.1]
    have hpB : (1 + |t.2.1|) ^ B ≤ (1 + |t.2.1|) ^ ⌈B⌉₊ := by
      calc (1 + |t.2.1|) ^ B ≤ (1 + |t.2.1|) ^ ((⌈B⌉₊ : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hp1 (Nat.le_ceil B)
        _ = _ := Real.rpow_natCast _ _
    have hL' : ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ ≤
        CL * (1 + |t.2.1|) ^ ⌈B⌉₊ := bP.trans (mul_le_mul_of_nonneg_left hpB hCL0.le)
    have key : (1 + |t.2.1|) ^ 2 * (‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
        ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖) ≤ CL * CW := by
      have h1 : ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ ≤
          CL * (1 + |t.2.1|) ^ ⌈B⌉₊ * ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right hL' (norm_nonneg _)
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 + |t.2.1|) ^ 2)
      have h3 : (1 + |t.2.1|) ^ 2 * (CL * (1 + |t.2.1|) ^ ⌈B⌉₊ *
          ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖) =
          CL * ((1 + |t.2.1|) ^ (⌈B⌉₊ + 2) * ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖) := by
        rw [pow_add]; ring
      have h4 := mul_le_mul_of_nonneg_left hWY hCL0.le
      linarith
    exact le_hh key
  have bE : Real.exp ((x + v - 1) ^ 2) ≤ Real.exp ((|x₀| + |x₁| + |v₀| + |v₁| + 1) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have habs : -(|x₀| + |x₁| + |v₀| + |v₁| + 1) ≤ x + v - 1 ∧
        x + v - 1 ≤ |x₀| + |x₁| + |v₀| + |v₁| + 1 := by
      constructor <;> linarith [neg_abs_le x₀, neg_abs_le v₀, le_abs_self x₁, le_abs_self v₁,
        hxI.1, hxI.2, hvI.1, hvI.2, abs_nonneg x₀, abs_nonneg x₁, abs_nonneg v₀, abs_nonneg v₁]
    exact sq_le_sq' habs.1 habs.2
  have hZE : 0 ≤ Z ^ (Scales.kernelExponent x y v) := Real.rpow_nonneg hZ0.le _
  have hG0 : 0 ≤ Real.exp (-(t.1 + t.2.2) ^ 2) := (Real.exp_pos _).le
  have hP' : Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) ≤
      Z ^ (Scales.kernelExponent x y v) * Real.exp ((|x₀| + |x₁| + |v₀| + |v₁| + 1) ^ 2) *
        Real.exp (-(t.1 + t.2.2) ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bE hZE) hG0
  have hP'0 : 0 ≤ Z ^ (Scales.kernelExponent x y v) * Real.exp ((|x₀| + |x₁| + |v₀| + |v₁| + 1) ^ 2) *
      Real.exp (-(t.1 + t.2.2) ^ 2) :=
    mul_nonneg (mul_nonneg hZE (Real.exp_pos _).le) hG0
  have hPn : 0 ≤ Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) *
      Real.exp (-(t.1 + t.2.2) ^ 2) :=
    mul_nonneg (mul_nonneg hZE (Real.exp_pos _).le) hG0
  rw [norm_kernel_principal D u hq x y v Z hZ0 t]
  have hLc0 : 0 ≤ ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hA : (Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2)) *
      ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ ≤
      (Z ^ (Scales.kernelExponent x y v) * Real.exp ((|x₀| + |x₁| + |v₀| + |v₁| + 1) ^ 2) *
        Real.exp (-(t.1 + t.2.2) ^ 2)) * (|CM| * hh t.2.2) :=
    (mul_le_mul_of_nonneg_right hP' (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left bM hP'0)
  have hC3 : ‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
      ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ * ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ ≤
      Cz * CH * Cl :=
    mul_le_mul (mul_le_mul bZ bH (norm_nonneg _) hCz0.le) bL hLc0
      (mul_nonneg hCz0.le hCH0.le)
  have hLn0 := norm_nonneg (D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I))
  have hWv0 := norm_nonneg (D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I))
  have hz0 := norm_nonneg (D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)))
  have hH0 := norm_nonneg (Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))
  have ha1 : 0 ≤ |CM| * hh t.2.2 := mul_nonneg (abs_nonneg _) (hh_pos _).le
  have ha2 : 0 ≤ |CL * CW| * hh t.2.1 := mul_nonneg (abs_nonneg _) (hh_pos _).le
  calc _ = (Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) *
        ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖) *
        (‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
          ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖) *
        (‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
          ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
            ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ * ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹) := by
        ring
    _ ≤ ((Z ^ (Scales.kernelExponent x y v) * Real.exp ((|x₀| + |x₁| + |v₀| + |v₁| + 1) ^ 2) *
          Real.exp (-(t.1 + t.2.2) ^ 2)) * (|CM| * hh t.2.2)) *
          (|CL * CW| * hh t.2.1) * (Cz * CH * Cl) :=
        mul_le_mul (mul_le_mul hA hLW (mul_nonneg hLn0 hWv0) (mul_nonneg hP'0 ha1)) hC3
          (mul_nonneg (mul_nonneg hz0 hH0) hLc0) (mul_nonneg (mul_nonneg hP'0 ha1) ha2)
    _ = Z ^ (Scales.kernelExponent x y v) * (K * tripleG t) := by
        rw [hK]
        simp only [tripleG, gaussShear]
        ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalBox2Majorant
