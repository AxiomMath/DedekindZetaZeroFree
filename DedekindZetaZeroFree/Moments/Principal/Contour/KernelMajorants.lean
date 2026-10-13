module

public import DedekindZetaZeroFree.Analysis.GaussianWeightConvolution
public import DedekindZetaZeroFree.Moments.Principal.Contour.SecondBoxMajorant
public import DedekindZetaZeroFree.Moments.Principal.Contour.ThirdBoxMajorant

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalKernelMajorants

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions
  DedekindZetaZeroFree.Quantitative.EulerDomain MeasureTheory
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

def xiPrincipal : Set Coordinates := {p | Scales.rightLine - Scales.contourOffset / 2 < p.1.re}

def zPrincipal : Set Coordinates := {p | 1 / 6 + Scales.contourOffset / 2 < p.2.2.re}

def singW : Set Coordinates := {p | p.2.1 = 1}

def singZ : Set Coordinates := {p | p.2.1 = 1 ∨ 6 * p.2.2 = 1}

private lemma six_re (z : ℂ) : (6 * z).re = 6 * z.re := by simp [Complex.mul_re]

theorem Hu_differentiableOn (u : D.Row) :
    DifferentiableOn ℂ (fun p : Coordinates => Hu D u p.1 p.2.1 p.2.2) OmegaStar :=
  (EulerDomain.Hu_normal_convergence D u).2.2.1

private lemma kernel_differentiableAt (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z)
    (p : Coordinates) (hξ : 1 < p.1.re) (hw : 0 < p.2.1.re) (hw1 : p.2.1 ≠ 1)
    (hz : 0 < p.2.2.re) (hz6 : 6 * p.2.2 ≠ 1) (hΩ : p ∈ OmegaStar) :
    DifferentiableAt ℂ
      (fun p : Coordinates => kernelWith D (rowContLocal D) u p.1 p.2.1 p.2.2 Z) p := by
  have hqc : ((D.q u : ℝ) : ℂ) = 1 := by rw [PrincipalResidueFormulas.q_principal D u hu]; simp
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  simp only [kernelWith, rowContLocal, hqc, Complex.one_cpow, mul_one]
  have a1 : DifferentiableAt ℂ (fun p : Coordinates => p.1) p := differentiableAt_fst
  have a2 : DifferentiableAt ℂ (fun p : Coordinates => p.2.1) p :=
    differentiableAt_fst.comp p differentiableAt_snd
  have a3 : DifferentiableAt ℂ (fun p : Coordinates => p.2.2) p :=
    differentiableAt_snd.comp p differentiableAt_snd
  have hpow : DifferentiableAt ℂ (fun p : Coordinates => (Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) +
      p.1 - 1 + (Scales.smoothingExponent : ℂ) * p.2.2 + (Scales.yExponent : ℂ) * (p.2.1 - 1))) p := by
    have : (fun p : Coordinates => (Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) +
      p.1 - 1 + (Scales.smoothingExponent : ℂ) * p.2.2 + (Scales.yExponent : ℂ) * (p.2.1 - 1))) = fun p : Coordinates =>
        Complex.exp (Complex.log Z * (((Scales.xExponent / 2 : ℝ) : ℂ) +
      p.1 - 1 + (Scales.smoothingExponent : ℂ) * p.2.2 + (Scales.yExponent : ℂ) * (p.2.1 - 1))) :=
      funext fun p => Complex.cpow_def_of_ne_zero hZc _
    rw [this]
    fun_prop
  have hexp : DifferentiableAt ℂ (fun p : Coordinates =>
      Complex.exp ((p.1 + p.2.2 - 1) ^ 2)) p := by fun_prop
  have hMopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hM : DifferentiableAt ℂ (fun p : Coordinates => D.M p.2.2) p :=
    (D.M_differentiableOn.differentiableAt (hMopen.mem_nhds hz)).comp p a3
  have hW : Differentiable ℂ D.W1Hat :=
    ProbeSheet.MellinProof.realWeight_mellin_differentiable D.recipe.probe.W1
  have hWw : DifferentiableAt ℂ (fun p : Coordinates => D.W1Hat p.2.1) p :=
    (hW _).comp p a2
  have hζ : DifferentiableAt ℂ (fun p : Coordinates => D.zetaSCont (6 * p.2.2)) p :=
    (((PrincipalResidueFormulas.zetaSCont_analytic D) (6 * p.2.2)
      ⟨by simp only [Set.mem_setOf_eq]; rw [six_re]; linarith, hz6⟩).differentiableAt).comp p
      (by fun_prop : DifferentiableAt ℂ (fun p : Coordinates => 6 * p.2.2) p)
  have hξ1 : p.1 ≠ 1 := fun h => by
    rw [h] at hξ
    simp at hξ
  have hLp : DifferentiableAt ℂ (fun p : Coordinates => D.Lpsi u p.2.1) p :=
    (((D.Lpsi_analyticOnNhd u) p.2.1 ⟨hw, hw1⟩).differentiableAt).comp p a2
  have hLl : DifferentiableAt ℂ (fun p : Coordinates => D.Llam u p.1) p :=
    (((D.Llam_analyticOnNhd u) p.1 ⟨by simp only [Set.mem_setOf_eq]; linarith, hξ1⟩).differentiableAt).comp p a1
  have hHu : DifferentiableAt ℂ (fun p : Coordinates => Hu D u p.1 p.2.1 p.2.2) p :=
    (Hu_differentiableOn D u).differentiableAt (EulerDomain.OmegaStar_isOpen.mem_nhds hΩ)
  simp only [div_eq_mul_inv]
  exact (((hpow.fun_mul hexp).fun_mul hM).fun_mul hWw).fun_mul
    (((hζ.fun_mul hLp).fun_mul hHu).fun_mul
      (hLl.inv (RightHeckeBounds.Llam_ne_zero_of_one_lt D u _ hξ)))

private lemma kernel_differentiableOn_of (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z)
    (U : Set Coordinates)
    (h : ∀ p ∈ U, 1 < p.1.re ∧ 0 < p.2.1.re ∧ p.2.1 ≠ 1 ∧ 0 < p.2.2.re ∧ 6 * p.2.2 ≠ 1 ∧
      p ∈ OmegaStar) :
    DifferentiableOn ℂ
      (fun p : Coordinates => kernelWith D (rowContLocal D) u p.1 p.2.1 p.2.2 Z) U := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h p hp
  exact (kernel_differentiableAt D u hu Z hZ p h1 h2 h3 h4 h5 h6).differentiableWithinAt

theorem kernel_analytic_paddedBox₂ (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) :
    DifferentiableOn ℂ
      (fun p : Coordinates => kernelWith D (rowContLocal D) u p.1 p.2.1 p.2.2 Z)
      ((paddedBox₂ ∩ xiPrincipal ∩ zPrincipal) \ singW) := by
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hpad : EulerDomain.pad = 1 / 1000000 := rfl
  refine (kernel_differentiableOn_of D u hu Z hZ {p : Coordinates | Scales.rightLine - Scales.contourOffset / 2 < p.1.re ∧
    4 / 5 < p.2.1.re ∧ 1 / 6 + Scales.contourOffset / 2 < p.2.2.re ∧ p.2.1 ≠ 1} ?_).mono ?_
  · rintro p ⟨hxi, hy, hzz, hw1⟩
    have h6 := six_re p.2.2
    refine ⟨by linarith, by linarith, hw1, by linarith, ?_, ?_⟩
    · intro h
      have := congrArg Complex.re h
      rw [h6] at this
      simp at this
      linarith
    · simp only [OmegaStar, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro p ⟨⟨⟨hb, hxi⟩, hzp⟩, hs⟩
    simp only [paddedBox₂, box, Set.mem_setOf_eq] at hb
    exact ⟨hxi, by linarith [hb.2.1], hzp, hs⟩

theorem kernel_analytic_paddedBox₃ (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 0 < Z) :
    DifferentiableOn ℂ
      (fun p : Coordinates => kernelWith D (rowContLocal D) u p.1 p.2.1 p.2.2 Z)
      ((paddedBox₃ ∩ xiPrincipal) \ singZ) := by
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hpad : EulerDomain.pad = 1 / 1000000 := rfl
  refine (kernel_differentiableOn_of D u hu Z hZ {p : Coordinates | Scales.rightLine - Scales.contourOffset / 2 < p.1.re ∧
    9 / 10 < p.2.1.re ∧ 1 / 40 < p.2.2.re ∧ p.2.1 ≠ 1 ∧ 6 * p.2.2 ≠ 1} ?_).mono ?_
  · rintro p ⟨hxi, hy, hzz, hw1, hz6⟩
    refine ⟨by linarith, by linarith, hw1, by linarith, hz6, ?_⟩
    simp only [OmegaStar, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro p ⟨⟨hb, hxi⟩, hs⟩
    simp only [paddedBox₃, box, Set.mem_setOf_eq] at hb
    have hs0 : ¬ (p.2.1 = 1 ∨ 6 * p.2.2 = 1) := hs
    have hs' := not_or.mp hs0
    exact ⟨hxi, by linarith [hb.2.1], by linarith [hb.2.2], hs'.1, hs'.2⟩

theorem kernel_majorant_paddedBox₂ (u : D.Row) (hu : u.u = 1)
    (x₀ x₁ y₀ y₁ v₀ v₁ : ℝ)
    (hx : ∀ x ∈ Set.Icc x₀ x₁, Scales.rightLine - Scales.contourOffset / 2 ≤ x)
    (hy : ∀ y ∈ Set.Icc y₀ y₁, 9 / 10 - EulerDomain.pad ≤ y ∧ y ≠ 1)
    (hv : ∀ v ∈ Set.Icc v₀ v₁, 1 / 6 + Scales.contourOffset / 2 ≤ v) :
    ∃ g : ℝ × ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧
      ∀ x ∈ Set.Icc x₀ x₁, ∀ y ∈ Set.Icc y₀ y₁, ∀ v ∈ Set.Icc v₀ v₁, ∀ Z : ℝ, 2 ≤ Z →
        ∀ t : ℝ × ℝ × ℝ,
          ‖kernelWith D (rowContLocal D) u ((x : ℂ) + (t.1 : ℂ) * Complex.I)
              ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ ≤
            Z ^ (Scales.kernelExponent x y v) * g t :=
  PrincipalBox2Majorant.kernel_majorant_paddedBox2 D u hu x₀ x₁ y₀ y₁ v₀ v₁ hx hy hv

theorem kernel_majorant_paddedBox₃ (u : D.Row) (hu : u.u = 1)
    (x₀ x₁ y₀ y₁ v₀ v₁ : ℝ)
    (hx : ∀ x ∈ Set.Icc x₀ x₁, Scales.rightLine - Scales.contourOffset / 2 ≤ x)
    (hy : ∀ y ∈ Set.Icc y₀ y₁, 1 - EulerDomain.pad ≤ y ∧ y ≠ 1)
    (hv : ∀ v ∈ Set.Icc v₀ v₁, 1 / 20 - EulerDomain.pad ≤ v ∧ v ≠ 1 / 6) :
    ∃ g : ℝ × ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧
      ∀ x ∈ Set.Icc x₀ x₁, ∀ y ∈ Set.Icc y₀ y₁, ∀ v ∈ Set.Icc v₀ v₁, ∀ Z : ℝ, 2 ≤ Z →
        ∀ t : ℝ × ℝ × ℝ,
          ‖kernelWith D (rowContLocal D) u ((x : ℂ) + (t.1 : ℂ) * Complex.I)
              ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ ≤
            Z ^ (Scales.kernelExponent x y v) * g t :=
  PrincipalBox3Majorant.kernel_majorant_paddedBox3 D u hu x₀ x₁ y₀ y₁ v₀ v₁ hx hy hv

theorem kernel_majorant_initial_shift (u : D.Row) (hu : u.u = 1) :
    ∃ g : ℝ × ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧
      ∀ x ∈ Set.Icc Scales.rightLine 4, ∀ y ∈ Set.Icc Scales.rightLine 4,
      ∀ v ∈ Set.Icc (1 / 6 + Scales.contourOffset) 2, ∀ Z : ℝ, 2 ≤ Z →
        ∀ t : ℝ × ℝ × ℝ,
          ‖kernelWith D (rowContLocal D) u ((x : ℂ) + (t.1 : ℂ) * Complex.I)
              ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ ≤
            Z ^ (Scales.kernelExponent x y v) * g t := by
  have hq : D.q u = 1 := PrincipalResidueFormulas.q_principal D u hu
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  obtain ⟨Cz, hCz0, hCz⟩ := RightHeckeBounds.zetaSCont_norm_le_right D (1 + 6 * Scales.contourOffset)
    (by rw [hd]; norm_num)
  obtain ⟨Cp, hCp0, hCp⟩ := RightHeckeBounds.Lpsi_norm_le_right D (1 + Scales.contourOffset)
    (by rw [hd]; norm_num)
  obtain ⟨Cl, hCl0, hCl⟩ := RightHeckeBounds.Llam_inv_norm_le_right D (1 + Scales.contourOffset)
    (by rw [hd]; norm_num)
  obtain ⟨CH, hCH0, hCH⟩ := EulerSubpower.Hu_subpower D (1 / 100) (by norm_num) 1 one_pos
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay (1 / 6) 2 (by norm_num) (by norm_num) 2
  obtain ⟨CW, hCW⟩ := D.W1Hat_vertical_decay 1 4 (by norm_num) 2
  refine ⟨fun t => (Real.exp 25 * |CM| * |CW| * (Cz * Cp * CH * Cl)) * tripleG t,
    tripleG_integrable.const_mul _, fun t => ?_, ?_⟩
  · have := tripleG_nonneg t
    positivity
  intro x hx y hy v hv Z hZ t
  have hZ0 : 0 < Z := by linarith
  have hx1 : 1 + Scales.contourOffset ≤ x := hx.1
  have hy1 : 1 + Scales.contourOffset ≤ y := hy.1
  have hv1 : 1 / 6 + Scales.contourOffset ≤ v := hv.1
  have hx4 : x ≤ 4 := hx.2
  have hy4 : y ≤ 4 := hy.2
  have hv2 : v ≤ 2 := hv.2
  rw [norm_kernel_principal D u hq x y v Z hZ0 t]
  have hxre : ((x : ℂ) + (t.1 : ℂ) * Complex.I).re = x := by simp
  have hyre : ((y : ℂ) + (t.2.1 : ℂ) * Complex.I).re = y := by simp
  have hvre : ((v : ℂ) + (t.2.2 : ℂ) * Complex.I).re = v := by simp
  have hyim : ((y : ℂ) + (t.2.1 : ℂ) * Complex.I).im = t.2.1 := by simp
  have hvim : ((v : ℂ) + (t.2.2 : ℂ) * Complex.I).im = t.2.2 := by simp
  have h6re : (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)).re = 6 * v := by simp

  have bZ : ‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ ≤ Cz :=
    hCz _ (by rw [h6re]; linarith)
  have bP : ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ ≤ Cp :=
    hCp u _ (by rw [hyre]; linarith)
  have bL : ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ ≤ Cl := by
    have := hCl u ((x : ℂ) + (t.1 : ℂ) * Complex.I) (by rw [hxre]; linarith)
    rwa [norm_inv] at this
  have hmem : (((x : ℂ) + (t.1 : ℂ) * Complex.I, (y : ℂ) + (t.2.1 : ℂ) * Complex.I,
      (v : ℂ) + (t.2.2 : ℂ) * Complex.I) : Coordinates) ∈ OmegaStarMargin (1 / 100) := by
    simp only [OmegaStarMargin, Set.mem_setOf_eq]
    rw [hxre, hyre, hvre]
    rw [hd] at hx1 hy1 hv1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have bH : ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
      ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ ≤ CH := by
    have := (hCH u _ hmem).2
    rwa [hq, Real.one_rpow, mul_one] at this
  have bM : ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ ≤ |CM| * hh t.2.2 := by
    have := hCM ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) (by rw [hvre]; rw [hd] at hv1; linarith)
      (by rw [hvre]; exact hv2)
    rw [hvim] at this
    exact le_hh this
  have bW : ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ ≤ |CW| * hh t.2.1 := by
    have := hCW ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) (by rw [hyre]; rw [hd] at hy1; linarith)
      (by rw [hyre]; exact hy4)
    rw [hyim] at this
    exact le_hh this
  have bE : Real.exp ((x + v - 1) ^ 2) ≤ Real.exp 25 :=
    Real.exp_le_exp.mpr (by nlinarith [Real.exp_pos 1])
  have nZ := norm_nonneg (D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)))
  have nP := norm_nonneg (D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I))
  have nH := norm_nonneg (Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I)
    ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))
  have nL : 0 ≤ ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ := by positivity
  have nM := norm_nonneg (D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))
  have nW := norm_nonneg (D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I))
  have hZE : 0 ≤ Z ^ (Scales.kernelExponent x y v) := Real.rpow_nonneg hZ0.le _
  have hG : 0 ≤ Real.exp (-(t.1 + t.2.2) ^ 2) := (Real.exp_pos _).le
  have hE0 : 0 ≤ Real.exp ((x + v - 1) ^ 2) := (Real.exp_pos _).le
  have h3 := hh_pos t.2.2
  have h2 := hh_pos t.2.1
  have hP4 : ‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
      ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
      ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ *
      ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ ≤ Cz * Cp * CH * Cl :=
    mul_le_mul (mul_le_mul (mul_le_mul bZ bP nP hCz0.le) bH nH (by positivity)) bL nL
      (by positivity)
  have hP0 : 0 ≤ ‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
      ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
      ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ *
      ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ := by positivity
  have hm0 : 0 ≤ |CM| * hh t.2.2 := by positivity
  have hw0 : 0 ≤ |CW| * hh t.2.1 := by positivity
  have hc0 : 0 ≤ Cz * Cp * CH * Cl := by positivity
  have hZG : 0 ≤ Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) *
      Real.exp (-(t.1 + t.2.2) ^ 2) := by positivity
  calc _ ≤ Z ^ (Scales.kernelExponent x y v) * Real.exp 25 * Real.exp (-(t.1 + t.2.2) ^ 2) *
        (|CM| * hh t.2.2) * (|CW| * hh t.2.1) * (Cz * Cp * CH * Cl) := by
        refine mul_le_mul ?_ hP4 hP0 (by positivity)
        refine mul_le_mul ?_ bW nW (by positivity)
        refine mul_le_mul ?_ bM nM (by positivity)
        refine mul_le_mul ?_ le_rfl hG (by positivity)
        exact mul_le_mul le_rfl bE hE0 hZE
    _ = _ := by
        simp only [tripleG, gaussShear]
        ring

private lemma wResidue_majorant_aux (u : D.Row) (hu : u.u = 1) (v₀ : ℝ)
    (hv0 : 1 / 20 ≤ v₀) (hv1 : v₀ ≤ 1) (hv6 : 6 * v₀ ≠ 1) :
    ∃ g : ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ t : ℝ × ℝ,
      ‖wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
          ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) Z‖ ≤
        Z ^ (Scales.kernelExponent Scales.rightLine 1 v₀) * g t := by
  have hq : D.q u = 1 := PrincipalResidueFormulas.q_principal D u hu
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hx : Scales.rightLine = 1 + 1 / 10000000 := rfl
  obtain ⟨Cl, hCl0, hCl⟩ := RightHeckeBounds.Llam_inv_norm_le_right D (1 + Scales.contourOffset)
    (by rw [hd]; norm_num)
  obtain ⟨CH, hCH0, hCH⟩ := EulerSubpower.Hu_subpower D (1 / 100) (by norm_num) 1 one_pos
  obtain ⟨Cs, ks, hCs0, hks, hCs⟩ :=
    PrincipalZetaStripGrowth.zetaSCont_strip_polynomial_bound D (6 * v₀) (6 * v₀) (|6 * v₀ - 1|)
      (by linarith) le_rfl (abs_pos.mpr (sub_ne_zero.mpr hv6))
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay v₀ v₀ (by linarith) le_rfl (⌈ks⌉₊ + 2)
  have hA0 : 0 ≤ Cs * 6 ^ ⌈ks⌉₊ := by positivity
  refine ⟨fun t => (‖Spectral.RS D‖ * ‖D.W1Hat 1‖ * Real.exp 25 * |Cs * 6 ^ ⌈ks⌉₊ * CM| *
      CH * Cl) * gaussShear t, gaussShear_integrable.const_mul _, fun t => ?_, ?_⟩
  · have := gaussShear_nonneg t
    positivity
  intro Z hZ t
  have hZ0 : 0 < Z := by linarith
  have hxre : ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I).re = Scales.rightLine := by simp
  have hzre : ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I).re = v₀ := by simp
  have hzim : ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I).im = t.2 := by simp
  have hxgt : 1 < ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I).re := by
    rw [hxre, hx]; norm_num
  have hz6 : 6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hv6 this
  have hpad : (0 : ℝ) ≤ EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  rw [PrincipalResidueFormulas.wResidue_eq D u hu _ _ Z hZ0 hxgt
    (by rw [hzre]; linarith) hz6, PrincipalResidueFormulas.remainingKernel_principal D u hu]
  have hZn : ‖(Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) + ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) - 1 +
      (Scales.smoothingExponent : ℂ) * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))‖ = Z ^ (Scales.kernelExponent Scales.rightLine 1 v₀) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ0]
    congr 1
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.one_re, Complex.one_im]
    unfold Scales.kernelExponent
    ring
  have hEn : ‖Complex.exp ((((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) +
      ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) - 1) ^ 2)‖ =
      Real.exp ((Scales.rightLine + v₀ - 1) ^ 2) * Real.exp (-(t.1 + t.2) ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.one_re, Complex.one_im]
    ring
  have hmem : (((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I, (1 : ℂ),
      (v₀ : ℂ) + (t.2 : ℂ) * Complex.I) : Coordinates) ∈ OmegaStarMargin (1 / 100) := by
    simp only [OmegaStarMargin, Set.mem_setOf_eq, Complex.one_re]
    rw [hxre, hzre, hx]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have bH : ‖Hu D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) 1
      ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖ ≤ CH := by
    have := (hCH u _ hmem).2
    rwa [hq, Real.one_rpow, mul_one] at this
  have bL : ‖D.Llam u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ ≤ Cl := by
    have := hCl u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) (by rw [hxre]; exact le_rfl)
    rwa [norm_inv] at this
  have bZ : ‖D.zetaSCont (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))‖ ≤
      Cs * 6 ^ ⌈ks⌉₊ * (1 + |t.2|) ^ ⌈ks⌉₊ := by
    have h6re : (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)).re = 6 * v₀ := by simp
    have h6im : (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)).im = 6 * t.2 := by simp
    have hsep : |6 * v₀ - 1| ≤ ‖6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) - 1‖ := by
      have := Complex.abs_re_le_norm (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) - 1)
      simpa using this
    have h1 := hCs _ (by rw [h6re]) (by rw [h6re]) hsep
    rw [h6im] at h1
    have h2 : (1 + |6 * t.2|) ^ ks ≤ (1 + |6 * t.2|) ^ (⌈ks⌉₊ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (6 * t.2)]) (Nat.le_ceil ks)
    rw [Real.rpow_natCast] at h2
    have h3 : (1 + |6 * t.2|) ^ ⌈ks⌉₊ ≤ (6 * (1 + |t.2|)) ^ ⌈ks⌉₊ := by
      apply pow_le_pow_left₀ (by positivity)
      rw [abs_mul]
      norm_num
      linarith [abs_nonneg t.2]
    rw [mul_pow] at h3
    calc _ ≤ Cs * (1 + |6 * t.2|) ^ ks := h1
      _ ≤ Cs * (6 ^ ⌈ks⌉₊ * (1 + |t.2|) ^ ⌈ks⌉₊) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hCs0.le
      _ = _ := by ring
  have bM : (1 + |t.2|) ^ (⌈ks⌉₊ + 2) * ‖D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖ ≤ CM := by
    have := hCM ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) (by rw [hzre]) (by rw [hzre])
    rwa [hzim] at this
  have bMZ : ‖D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖ *
      ‖D.zetaSCont (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))‖ ≤
      |Cs * 6 ^ ⌈ks⌉₊ * CM| * hh t.2 := by
    apply le_hh
    have hp : (0 : ℝ) < 1 + |t.2| := by positivity
    have nM := norm_nonneg (D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))
    calc (1 + |t.2|) ^ 2 * (‖D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖ *
        ‖D.zetaSCont (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))‖)
        ≤ (1 + |t.2|) ^ 2 * (‖D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖ *
          (Cs * 6 ^ ⌈ks⌉₊ * (1 + |t.2|) ^ ⌈ks⌉₊)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left bZ nM
      _ = (Cs * 6 ^ ⌈ks⌉₊) * ((1 + |t.2|) ^ (⌈ks⌉₊ + 2) *
          ‖D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖) := by ring
      _ ≤ (Cs * 6 ^ ⌈ks⌉₊) * CM := mul_le_mul_of_nonneg_left bM hA0
  have bE : Real.exp ((Scales.rightLine + v₀ - 1) ^ 2) ≤ Real.exp 25 :=
    Real.exp_le_exp.mpr (by rw [hx]; nlinarith)
  have nH := norm_nonneg (Hu D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) 1
      ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))
  have nL : 0 ≤ ‖D.Llam u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ := by positivity
  have nMZ : 0 ≤ ‖D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖ *
      ‖D.zetaSCont (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))‖ := by positivity
  have hG : 0 ≤ Real.exp (-(t.1 + t.2) ^ 2) := (Real.exp_pos _).le
  have hE0 : 0 ≤ Real.exp ((Scales.rightLine + v₀ - 1) ^ 2) := (Real.exp_pos _).le
  have hh0 := hh_pos t.2
  have hZE : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine 1 v₀) := Real.rpow_nonneg hZ0.le _
  have hr0 := norm_nonneg (Spectral.RS D)
  have hw0 := norm_nonneg (D.W1Hat 1)
  calc _ = Z ^ (Scales.kernelExponent Scales.rightLine 1 v₀) * (‖Spectral.RS D‖ * ‖D.W1Hat 1‖ *
        (Real.exp ((Scales.rightLine + v₀ - 1) ^ 2) * Real.exp (-(t.1 + t.2) ^ 2)) *
        (‖D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖ *
          ‖D.zetaSCont (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))‖) *
        ‖Hu D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) 1
          ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)‖ *
        ‖D.Llam u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹) := by
        simp only [norm_mul, norm_div, hZn, hEn]
        rw [div_eq_mul_inv]
        ring
    _ ≤ Z ^ (Scales.kernelExponent Scales.rightLine 1 v₀) * (‖Spectral.RS D‖ * ‖D.W1Hat 1‖ *
        (Real.exp 25 * Real.exp (-(t.1 + t.2) ^ 2)) * (|Cs * 6 ^ ⌈ks⌉₊ * CM| * hh t.2) *
        CH * Cl) := by
        refine mul_le_mul_of_nonneg_left ?_ hZE
        refine mul_le_mul ?_ bL nL (by positivity)
        refine mul_le_mul ?_ bH nH (by positivity)
        refine mul_le_mul ?_ bMZ nMZ (by positivity)
        exact mul_le_mul le_rfl (mul_le_mul bE le_rfl hG (by positivity)) (by positivity)
          (by positivity)
    _ = _ := by
        simp only [gaussShear]
        ring

theorem wResidue_majorant_z (u : D.Row) (hu : u.u = 1) :
    ∃ g : ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ t : ℝ × ℝ,
      ‖wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
          (((1 / 20 : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z‖ ≤
        Z ^ (Scales.kernelExponent Scales.rightLine 1 (1 / 20)) * g t :=
  wResidue_majorant_aux D u hu (1 / 20) le_rfl (by norm_num) (by norm_num)

theorem wResidue_majorant_w (u : D.Row) (hu : u.u = 1) :
    ∃ g : ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ t : ℝ × ℝ,
      ‖wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
          (((1 / 6 + Scales.contourOffset : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z‖ ≤
        Z ^ (Scales.kernelExponent Scales.rightLine 1 (1 / 6 + Scales.contourOffset)) * g t :=
  wResidue_majorant_aux D u hu (1 / 6 + Scales.contourOffset) (by unfold Scales.contourOffset; norm_num)
    (by unfold Scales.contourOffset; norm_num) (by unfold Scales.contourOffset; norm_num)

private lemma wResidue_integrable_aux (u : D.Row) (hu : u.u = 1) (v₀ : ℝ)
    (hv0 : 1 / 20 ≤ v₀) (hv1 : v₀ ≤ 1) (hv6 : 6 * v₀ ≠ 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    Integrable (fun t : ℝ × ℝ =>
      wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
        ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) Z) := by
  obtain ⟨g, hg, hg0, hb⟩ := wResidue_majorant_aux D u hu v₀ hv0 hv1 hv6
  refine Integrable.mono' (hg.const_mul (Z ^ (Scales.kernelExponent Scales.rightLine 1 v₀))) ?_
    (Filter.Eventually.of_forall fun t => hb Z hZ t)
  apply Continuous.aestronglyMeasurable
  have hZ0 : 0 < Z := by linarith
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ0.ne'
  have hx : Scales.rightLine = 1 + 1 / 10000000 := rfl
  have hξ : Continuous (fun t : ℝ × ℝ => (Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) := by
    fun_prop
  have hz : Continuous (fun t : ℝ × ℝ => (v₀ : ℂ) + (t.2 : ℂ) * Complex.I) := by fun_prop
  have hξre : ∀ t : ℝ × ℝ, ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I).re = Scales.rightLine :=
    fun t => by simp
  have hzre : ∀ t : ℝ × ℝ, ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I).re = v₀ := fun t => by simp
  have hz6re : ∀ t : ℝ × ℝ, (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)).re = 6 * v₀ :=
    fun t => by simp
  have hx1 : ∀ t : ℝ × ℝ, 1 < ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I).re :=
    fun t => by rw [hξre, hx]; norm_num
  have hxne : ∀ t : ℝ × ℝ, ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) ≠ 1 := fun t h => by
    have := hx1 t
    rw [h] at this
    simp at this
  have hz6 : ∀ t : ℝ × ℝ, 6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) ≠ 1 := fun t h => by
    have := congrArg Complex.re h
    rw [hz6re] at this
    simp at this
    exact hv6 this
  have hpad : (0 : ℝ) ≤ EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  have hfun : (fun t : ℝ × ℝ => wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
        ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) Z) = fun t : ℝ × ℝ =>
      Spectral.RS D * D.W1Hat 1 * PrincipalResidueFormulas.remainingKernel D u
        ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) Z := by
    funext t
    exact PrincipalResidueFormulas.wResidue_eq D u hu _ _ Z hZ0 (hx1 t)
      (by rw [hzre]; linarith) (hz6 t)
  rw [hfun]
  refine continuous_const.mul ?_
  simp_rw [PrincipalResidueFormulas.remainingKernel_principal D u hu]
  have hpow : Continuous (fun t : ℝ × ℝ => (Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) +
      ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) - 1 +
      (Scales.smoothingExponent : ℂ) * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hZc)
  have hexp : Continuous (fun t : ℝ × ℝ => Complex.exp ((((Scales.rightLine : ℂ) + (t.1 : ℂ) *
      Complex.I) + ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I) - 1) ^ 2)) := by fun_prop
  have hM : Continuous (fun t : ℝ × ℝ => D.M ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)) :=
    D.M_differentiableOn.continuousOn.comp_continuous hz
      (fun t => by simp only [Set.mem_setOf_eq]; rw [hzre]; linarith)
  have hζ : Continuous (fun t : ℝ × ℝ =>
      D.zetaSCont (6 * ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I))) :=
    (PrincipalResidueFormulas.zetaSCont_analytic D).continuousOn.comp_continuous
      (by fun_prop) (fun t => ⟨by simp only [Set.mem_setOf_eq]; rw [hz6re]; linarith,
        hz6 t⟩)
  have hmem : ∀ t : ℝ × ℝ, (((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I, (1 : ℂ),
      (v₀ : ℂ) + (t.2 : ℂ) * Complex.I) : Coordinates) ∈ OmegaStarMargin (1 / 100) := by
    intro t
    simp only [OmegaStarMargin, Set.mem_setOf_eq, Complex.one_re]
    rw [hξre, hzre, hx]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hHu : Continuous (fun t : ℝ × ℝ => Hu D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I) 1
      ((v₀ : ℂ) + (t.2 : ℂ) * Complex.I)) :=
    (EulerDomain.Hu_normal_convergence D u).2.2.1.continuousOn.comp_continuous
      (f := fun t : ℝ × ℝ => (((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I, (1 : ℂ),
        (v₀ : ℂ) + (t.2 : ℂ) * Complex.I) : Coordinates)) (by fun_prop)
      (fun t => OmegaStarMargin_subset (1 / 100) (by norm_num) (hmem t))
  have hL : Continuous (fun t : ℝ × ℝ => D.Llam u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)) :=
    (D.Llam_analyticOnNhd u).continuousOn.comp_continuous hξ
      (fun t => ⟨by simp only [Set.mem_setOf_eq]; linarith [hx1 t], hxne t⟩)
  exact ((hpow.mul hexp).mul hM).mul
    ((hζ.mul hHu).div hL (fun t => RightHeckeBounds.Llam_ne_zero_of_one_lt D u _ (hx1 t)))

theorem wResidue_integrable_z (u : D.Row) (hu : u.u = 1) (Z : ℝ) (hZ : 2 ≤ Z) :
    Integrable (fun t : ℝ × ℝ =>
      wResidueLocal D u ((Scales.rightLine : ℂ) + (t.1 : ℂ) * Complex.I)
        (((1 / 20 : ℝ) : ℂ) + (t.2 : ℂ) * Complex.I) Z) :=
  wResidue_integrable_aux D u hu (1 / 20) le_rfl (by norm_num) (by norm_num) Z hZ

end

end DedekindZetaZeroFree.Quantitative.PrincipalKernelMajorants
