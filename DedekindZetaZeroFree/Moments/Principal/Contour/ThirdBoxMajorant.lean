module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.SubpowerBounds
public import DedekindZetaZeroFree.Moments.Principal.Contour.SeparatedStripBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalBox3Majorant

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

private lemma pad_eq : EulerDomain.pad = 1 / 1000000 := rfl

private lemma absorb (A k x y Cx Cy : ℝ) (n : ℕ) (hA : 1 ≤ A) (hk : 0 ≤ k)
    (hn : k + 2 ≤ (n : ℝ)) (hCx : 0 ≤ Cx) (hy0 : 0 ≤ y)
    (hx : x ≤ Cx * A ^ k) (hy : A ^ n * y ≤ Cy) :
    x * y * A ^ 2 ≤ Cx * Cy := by
  have hA0 : 0 < A := by linarith
  have hkey : A ^ k * A ^ (2:ℝ) ≤ A ^ (n:ℝ) := by
    rw [← Real.rpow_add hA0]
    exact Real.rpow_le_rpow_of_exponent_le hA (by linarith)
  rw [Real.rpow_two, Real.rpow_natCast] at hkey
  have e1 : x * y * A ^ 2 ≤ Cx * A ^ k * y * A ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx hy0) (by positivity)
  have e3 : y * (A ^ k * A ^ 2) ≤ y * A ^ n := mul_le_mul_of_nonneg_left hkey hy0
  have e5 : y * A ^ n ≤ Cy := by linarith [mul_comm (A ^ n) y]
  have e4 : Cx * (y * (A ^ k * A ^ 2)) ≤ Cx * Cy :=
    mul_le_mul_of_nonneg_left (e3.trans e5) hCx
  calc x * y * A ^ 2 ≤ Cx * A ^ k * y * A ^ 2 := e1
    _ = Cx * (y * (A ^ k * A ^ 2)) := by ring
    _ ≤ Cx * Cy := e4

private lemma zeta_sep (v₀ v₁ : ℝ)
    (hv : ∀ v ∈ Set.Icc v₀ v₁, 1 / 20 - EulerDomain.pad ≤ v ∧ v ≠ 1 / 6) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ v ∈ Set.Icc v₀ v₁, ∀ t : ℝ,
      ‖D.zetaSCont (6 * ((v : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * (1 + |t|) ^ k := by
  by_cases h : v₀ ≤ v₁
  · have hpad : (0:ℝ) < EulerDomain.pad := by rw [pad_eq]; norm_num
    have hpv : EulerDomain.pad = 1 / 1000000 := pad_eq
    have h0 := (hv v₀ ⟨le_rfl, h⟩).1
    have hsep : ∀ x ∈ Set.Icc (6 * v₀) (6 * v₁), x ≠ 1 := by
      intro x hx hx1
      apply (hv (x / 6) ⟨by linarith [hx.1], by linarith [hx.2]⟩).2
      rw [hx1]
    obtain ⟨C, k, hC, hk, hb⟩ :=
      PrincipalSeparatedStripBounds.zeta_on_real_interval D (6 * v₀) (6 * v₁) (by linarith) hsep
    refine ⟨C * 6 ^ k, k, by positivity, hk, fun v hv' t => ?_⟩
    have hre : (6 * ((v : ℂ) + (t : ℂ) * Complex.I)).re = 6 * v := by simp
    have him : (6 * ((v : ℂ) + (t : ℂ) * Complex.I)).im = 6 * t := by simp
    have := hb _ (by rw [hre]; linarith [hv'.1]) (by rw [hre]; linarith [hv'.2])
    rw [him] at this
    have hpos : (0:ℝ) ≤ 1 + |t| := by positivity
    have hle : (1 + |6 * t|) ^ k ≤ 6 ^ k * (1 + |t|) ^ k := by
      rw [← Real.mul_rpow (by norm_num) hpos]
      refine Real.rpow_le_rpow (by positivity) ?_ hk
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6)]
      linarith [abs_nonneg t]
    calc _ ≤ C * (1 + |6 * t|) ^ k := this
      _ ≤ C * (6 ^ k * (1 + |t|) ^ k) := mul_le_mul_of_nonneg_left hle hC.le
      _ = C * 6 ^ k * (1 + |t|) ^ k := by ring
  · exact ⟨1, 0, one_pos, le_rfl, fun v hv' => absurd (hv'.1.trans hv'.2) h⟩

private lemma Lpsi_sep (u : D.Row) (hu : u.u = 1) (y₀ y₁ : ℝ)
    (hy : ∀ y ∈ Set.Icc y₀ y₁, 1 - EulerDomain.pad ≤ y ∧ y ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ y ∈ Set.Icc y₀ y₁, ∀ t : ℝ,
      ‖D.Lpsi u ((y : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ k := by
  by_cases h : y₀ ≤ y₁
  · have hpad : (0:ℝ) < EulerDomain.pad := by rw [pad_eq]; norm_num
    have hpv : EulerDomain.pad = 1 / 1000000 := pad_eq
    have h0 := (hy y₀ ⟨le_rfl, h⟩).1
    obtain ⟨C, k, hC, hk, hb⟩ :=
      PrincipalSeparatedStripBounds.Lpsi_principal_on_real_interval D u hu y₀ y₁ (by linarith)
        (fun x hx => (hy x hx).2)
    refine ⟨C, k, hC, hk, fun y hy' t => ?_⟩
    have hre : ((y : ℂ) + (t : ℂ) * Complex.I).re = y := by simp
    have him : ((y : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have := hb _ (by rw [hre]; exact hy'.1) (by rw [hre]; exact hy'.2)
    rwa [him] at this
  · exact ⟨1, 0, one_pos, le_rfl, fun y hy' => absurd (hy'.1.trans hy'.2) h⟩

theorem kernel_majorant_paddedBox3 (u : D.Row) (hu : u.u = 1)
    (x₀ x₁ y₀ y₁ v₀ v₁ : ℝ)
    (hx : ∀ x ∈ Set.Icc x₀ x₁, Scales.rightLine - Scales.contourOffset / 2 ≤ x)
    (hy : ∀ y ∈ Set.Icc y₀ y₁, 1 - EulerDomain.pad ≤ y ∧ y ≠ 1)
    (hv : ∀ v ∈ Set.Icc v₀ v₁, 1 / 20 - EulerDomain.pad ≤ v ∧ v ≠ 1 / 6) :
    ∃ g : ℝ × ℝ × ℝ → ℝ, Integrable g ∧ (∀ p, 0 ≤ g p) ∧
      ∀ x ∈ Set.Icc x₀ x₁, ∀ y ∈ Set.Icc y₀ y₁, ∀ v ∈ Set.Icc v₀ v₁, ∀ Z : ℝ, 2 ≤ Z →
        ∀ t : ℝ × ℝ × ℝ,
          ‖kernelWith D (rowContLocal D) u ((x : ℂ) + (t.1 : ℂ) * Complex.I)
              ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ ≤
            Z ^ (Scales.kernelExponent x y v) * g t := by
  have hq : D.q u = 1 := PrincipalResidueFormulas.q_principal D u hu
  have hpad : EulerDomain.pad = 1 / 1000000 := rfl
  have hd : Scales.contourOffset = 1 / 10000000 := rfl
  have hx1 : Scales.rightLine = 1 + Scales.contourOffset := rfl
  have hpad0 : (0:ℝ) < EulerDomain.pad := by rw [hpad]; norm_num
  obtain ⟨Cz, kz, hCz, hkz, hZ⟩ := zeta_sep D v₀ v₁ hv
  obtain ⟨Cp, kp, hCp, hkp, hP⟩ := Lpsi_sep D u hu y₀ y₁ hy
  obtain ⟨CL, hCL0, hCL⟩ := RightHeckeBounds.Llam_inv_norm_le_right D (1 + Scales.contourOffset / 2)
    (by rw [hd]; norm_num)
  obtain ⟨CH, hCH0, hCH⟩ := EulerSubpower.Hu_subpower D (1 / 100) (by norm_num) 1 one_pos
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay (1 / 20 - EulerDomain.pad)
    (max v₁ (1 / 20 - EulerDomain.pad)) (by rw [hpad]; norm_num) (le_max_right _ _)
    (⌈kz⌉₊ + 2)
  obtain ⟨CW, hCW⟩ := D.W1Hat_vertical_decay (1 - EulerDomain.pad)
    (max y₁ (1 - EulerDomain.pad)) (le_max_right _ _) (⌈kp⌉₊ + 2)
  have hnz : kz + 2 ≤ ((⌈kz⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil kz]
  have hnp : kp + 2 ≤ ((⌈kp⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil kp]
  have hK0 : 0 ≤ Real.exp ((x₁ + v₁) ^ 2) * |Cz * CM| * |Cp * CW| * (CH * CL) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (abs_nonneg _))
      (mul_nonneg hCH0.le hCL0.le)
  refine ⟨fun t => (Real.exp ((x₁ + v₁) ^ 2) * |Cz * CM| * |Cp * CW| * (CH * CL)) * tripleG t,
    tripleG_integrable.const_mul _, fun t => mul_nonneg hK0 (tripleG_nonneg t), ?_⟩
  intro x hxI y hyI v hvI Z hZ2 t
  dsimp only
  have hZ0 : 0 < Z := by linarith
  have hZE : 0 ≤ Z ^ (Scales.kernelExponent x y v) := Real.rpow_nonneg hZ0.le _
  have hxl : 1 + Scales.contourOffset / 2 ≤ x := by have := hx x hxI; linarith
  have hyl : 1 - EulerDomain.pad ≤ y := (hy y hyI).1
  have hvl : 1 / 20 - EulerDomain.pad ≤ v := (hv v hvI).1
  have hxre : ((x : ℂ) + (t.1 : ℂ) * Complex.I).re = x := by simp
  have hyre : ((y : ℂ) + (t.2.1 : ℂ) * Complex.I).re = y := by simp
  have hvre : ((v : ℂ) + (t.2.2 : ℂ) * Complex.I).re = v := by simp
  have hyim : ((y : ℂ) + (t.2.1 : ℂ) * Complex.I).im = t.2.1 := by simp
  have hvim : ((v : ℂ) + (t.2.2 : ℂ) * Complex.I).im = t.2.2 := by simp
  rw [norm_kernel_principal D u hq x y v Z hZ0 t]
  have hmem : (((x : ℂ) + (t.1 : ℂ) * Complex.I, (y : ℂ) + (t.2.1 : ℂ) * Complex.I,
      (v : ℂ) + (t.2.2 : ℂ) * Complex.I) : Coordinates) ∈ OmegaStarMargin (1 / 100) := by
    simp only [OmegaStarMargin, Set.mem_setOf_eq]
    rw [hxre, hyre, hvre]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have bH : ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
      ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ ≤ CH := by
    have := (hCH u _ hmem).2
    rwa [hq, Real.one_rpow, mul_one] at this
  have bL : ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ ≤ CL := by
    have := hCL u ((x : ℂ) + (t.1 : ℂ) * Complex.I) (by rw [hxre]; linarith)
    rwa [norm_inv] at this
  have bZ := hZ v hvI t.2.2
  have bP := hP y hyI t.2.1
  have bM := hCM ((v : ℂ) + (t.2.2 : ℂ) * Complex.I) (by rw [hvre]; linarith)
    (by rw [hvre]; exact le_max_of_le_left hvI.2)
  rw [hvim] at bM
  have bW := hCW ((y : ℂ) + (t.2.1 : ℂ) * Complex.I) (by rw [hyre]; linarith)
    (by rw [hyre]; exact le_max_of_le_left hyI.2)
  rw [hyim] at bW
  have hA3 : (1 : ℝ) ≤ 1 + |t.2.2| := by linarith [abs_nonneg t.2.2]
  have hA2 : (1 : ℝ) ≤ 1 + |t.2.1| := by linarith [abs_nonneg t.2.1]
  have hF3 : ‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
      ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ ≤ |Cz * CM| * hh t.2.2 := by
    apply le_hh
    have h := absorb (1 + |t.2.2|) kz _ _ Cz CM (⌈kz⌉₊ + 2) hA3 hkz hnz hCz.le
      (norm_nonneg _) bZ bM
    linarith [h, show (1 + |t.2.2|) ^ 2 * (‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖
      * ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖) =
      ‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
      ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ * (1 + |t.2.2|) ^ 2 by ring]
  have hF2 : ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
      ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ ≤ |Cp * CW| * hh t.2.1 := by
    apply le_hh
    have h := absorb (1 + |t.2.1|) kp _ _ Cp CW (⌈kp⌉₊ + 2) hA2 hkp hnp hCp.le
      (norm_nonneg _) bP bW
    linarith [h, show (1 + |t.2.1|) ^ 2 * (‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖
      * ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖) =
      ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
      ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ * (1 + |t.2.1|) ^ 2 by ring]
  have hHL : ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
      ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ * ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹
      ≤ CH * CL :=
    mul_le_mul bH bL (inv_nonneg.mpr (norm_nonneg _)) hCH0.le
  have hs0 : 0 ≤ x + v - 1 := by linarith
  have hs1 : x + v - 1 ≤ x₁ + v₁ := by linarith [hxI.2, hvI.2]
  have hsq : (x + v - 1) ^ 2 ≤ (x₁ + v₁) ^ 2 := by nlinarith
  have hE : Real.exp ((x + v - 1) ^ 2) ≤ Real.exp ((x₁ + v₁) ^ 2) := Real.exp_le_exp.mpr hsq
  have hG : 0 ≤ Real.exp (-(t.1 + t.2.2) ^ 2) := (Real.exp_pos _).le
  have hX1 : Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2)
      ≤ Z ^ (Scales.kernelExponent x y v) * Real.exp ((x₁ + v₁) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hZE) hG
  have hX1n : 0 ≤ Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) :=
    mul_nonneg (mul_nonneg hZE (Real.exp_pos _).le) hG
  have hX1'n : 0 ≤ Z ^ (Scales.kernelExponent x y v) * Real.exp ((x₁ + v₁) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) :=
    mul_nonneg (mul_nonneg hZE (Real.exp_pos _).le) hG
  have hZn := norm_nonneg (D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)))
  have hMn := norm_nonneg (D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))
  have hWn := norm_nonneg (D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I))
  have hPn := norm_nonneg (D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I))
  have hF3n : 0 ≤ ‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
      ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ := mul_nonneg hZn hMn
  have hF2n : 0 ≤ ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
      ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ := mul_nonneg hWn hPn
  have hHLn : 0 ≤ ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hHn := norm_nonneg (Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
      ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))
  have hfac : Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) *
        ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ *
        ‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
        (‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
          ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
          ‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
            ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ *
          ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹) =
      (Z ^ (Scales.kernelExponent x y v) * Real.exp ((x + v - 1) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2)) *
        (‖D.zetaSCont (6 * ((v : ℂ) + (t.2.2 : ℂ) * Complex.I))‖ *
          ‖D.M ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖) *
        (‖D.W1Hat ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖ *
          ‖D.Lpsi u ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)‖) *
        (‖Hu D u ((x : ℂ) + (t.1 : ℂ) * Complex.I) ((y : ℂ) + (t.2.1 : ℂ) * Complex.I)
            ((v : ℂ) + (t.2.2 : ℂ) * Complex.I)‖ *
          ‖D.Llam u ((x : ℂ) + (t.1 : ℂ) * Complex.I)‖⁻¹) := by ring
  rw [hfac]
  have hc : 0 ≤ Z ^ (Scales.kernelExponent x y v) * Real.exp ((x₁ + v₁) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2) :=
    hX1'n
  calc _ ≤ (Z ^ (Scales.kernelExponent x y v) * Real.exp ((x₁ + v₁) ^ 2) * Real.exp (-(t.1 + t.2.2) ^ 2)) *
        (|Cz * CM| * hh t.2.2) * (|Cp * CW| * hh t.2.1) * (CH * CL) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul hX1 hF3 hF3n hX1'n) hF2 hF2n
          (mul_nonneg hc (mul_nonneg (abs_nonneg _) (hh_pos _).le))) hHL
          (mul_nonneg hHn hHLn) (mul_nonneg (mul_nonneg hc (mul_nonneg (abs_nonneg _) (hh_pos _).le))
            (mul_nonneg (abs_nonneg _) (hh_pos _).le))
    _ = Z ^ (Scales.kernelExponent x y v) * ((Real.exp ((x₁ + v₁) ^ 2) * |Cz * CM| * |Cp * CW| * (CH * CL)) *
          tripleG (t)) := by
        simp only [tripleG, gaussShear]
        ring

end

end DedekindZetaZeroFree.Quantitative.PrincipalBox3Majorant
