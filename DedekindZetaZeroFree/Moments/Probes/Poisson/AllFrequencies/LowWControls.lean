module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyRightBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyConvexity
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.XiControls
public import DedekindZetaZeroFree.Moments.Probes.Poisson.KernelNorm
public import DedekindZetaZeroFree.Moments.Probes.Poisson.KernelRegularity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLowWControls31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem W1Hat_mul_plus_decay (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y t : ℝ, Scales.wLine - EulerDomain.pad / 2 ≤ y → y ≤ 4 + EulerDomain.pad / 2 →
      ‖D.W1Hat ((y : ℂ) + (t : ℂ) * I)‖ * ‖(pkg D).plus u ((y : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ (-B) := by
  obtain ⟨A, CL, hA, hCL, hL⟩ := RawSharpConvexity31.plus_strip_growth D u hu
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
  have hLn : ‖(pkg D).plus u ((y : ℂ) + (t : ℂ) * I)‖ ≤ CL * (2 ^ A * (1 + |t|) ^ A) :=
    hL'.trans (mul_le_mul_of_nonneg_left h2t hCL.le)
  have hp1 : 0 ≤ (1 + |t|) ^ A := Real.rpow_nonneg hpos.le _
  calc ‖D.W1Hat ((y : ℂ) + (t : ℂ) * I)‖ * ‖(pkg D).plus u ((y : ℂ) + (t : ℂ) * I)‖
      ≤ (|CW| * (1 + |t|) ^ (-(k : ℝ))) * (CL * (2 ^ A * (1 + |t|) ^ A)) :=
        mul_le_mul ha hLn (norm_nonneg _) (by positivity)
    _ = (CL * 2 ^ A * |CW|) * ((1 + |t|) ^ A * (1 + |t|) ^ (-(k : ℝ))) := by ring
    _ = (CL * 2 ^ A * |CW|) * (1 + |t|) ^ (A - k) := by rw [hsplit]
    _ ≤ (CL * 2 ^ A * |CW|) * (1 + |t|) ^ (-B) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

private theorem comb_aux {X Q G1 G2 Mn W P L cp mi bX bG bM bWP bL bcp bmi : ℝ}
    (hX : X ≤ bX) (hG : G1 * G2 ≤ bG) (hM : Mn ≤ bM) (hWP : W * P ≤ bWP) (hL : L ≤ bL)
    (hcp : cp ≤ bcp) (hmi : mi ≤ bmi)
    (hX0 : 0 ≤ X) (hQ : 0 ≤ Q) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) (hMn : 0 ≤ Mn) (hW : 0 ≤ W)
    (hP : 0 ≤ P) (hL0 : 0 ≤ L) (hcp0 : 0 ≤ cp) (hmi0 : 0 ≤ mi) (hbX : 0 ≤ bX) (hbG : 0 ≤ bG)
    (hbM : 0 ≤ bM) (hbWP : 0 ≤ bWP) (hbL : 0 ≤ bL) (hbcp : 0 ≤ bcp) :
    X * Q * (G1 * G2 * Mn * W) * (L * P * cp * mi) ≤
      bX * Q * bG * bM * bWP * bL * bcp * bmi := by
  have h1 : X * Q ≤ bX * Q := mul_le_mul_of_nonneg_right hX hQ
  have h2 : G1 * G2 * Mn ≤ bG * bM := mul_le_mul hG hM hMn hbG
  have p3 : 0 ≤ bX * Q * (bG * bM) := mul_nonneg (mul_nonneg hbX hQ) (mul_nonneg hbG hbM)
  have h3 : X * Q * (G1 * G2 * Mn) ≤ bX * Q * (bG * bM) :=
    mul_le_mul h1 h2 (mul_nonneg (mul_nonneg hG1 hG2) hMn) (mul_nonneg hbX hQ)
  have h4 : X * Q * (G1 * G2 * Mn) * (W * P) ≤ bX * Q * (bG * bM) * bWP :=
    mul_le_mul h3 hWP (mul_nonneg hW hP) p3
  have p4 : 0 ≤ bX * Q * (bG * bM) * bWP := mul_nonneg p3 hbWP
  have h5 : X * Q * (G1 * G2 * Mn) * (W * P) * L ≤ bX * Q * (bG * bM) * bWP * bL :=
    mul_le_mul h4 hL hL0 p4
  have p5 : 0 ≤ bX * Q * (bG * bM) * bWP * bL := mul_nonneg p4 hbL
  have h6 : X * Q * (G1 * G2 * Mn) * (W * P) * L * cp ≤
      bX * Q * (bG * bM) * bWP * bL * bcp := mul_le_mul h5 hcp hcp0 p5
  have p6 : 0 ≤ bX * Q * (bG * bM) * bWP * bL * bcp := mul_nonneg p5 hbcp
  have h7 : X * Q * (G1 * G2 * Mn) * (W * P) * L * cp * mi ≤
      bX * Q * (bG * bM) * bWP * bL * bcp * bmi := mul_le_mul h6 hmi hmi0 p6
  calc X * Q * (G1 * G2 * Mn * W) * (L * P * cp * mi)
      = X * Q * (G1 * G2 * Mn) * (W * P) * L * cp * mi := by ring
    _ ≤ bX * Q * (bG * bM) * bWP * bL * bcp * bmi := h7
    _ = bX * Q * bG * bM * bWP * bL * bcp * bmi := by ring

theorem rawKernel_w_bound (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y s t : ℝ, Scales.wLine - EulerDomain.pad / 2 ≤ y → y ≤ 4 + EulerDomain.pad / 2 →
      ‖rawKernel D u ξ ((y : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖ ≤
        C * (1 + |s|) ^ (-(2 : ℝ)) * (1 + |t|) ^ (-B) := by
  have hq : 0 < frequencyNorm D.recipe u := RawKernelNorm.frequencyNorm_pos D u
  have hQ : 0 ≤ frequencyNorm D.recipe u ^ (-Scales.zLine) := Real.rpow_nonneg hq.le _
  have hp : (0 : ℝ) < EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  obtain ⟨CWL, hCWL0, hWL⟩ := W1Hat_mul_plus_decay D u hu B
  obtain ⟨C1, hC1, hLz⟩ := RawRightHecke31.recipe_L_right D Scales.zLine
    (by unfold Scales.zLine; norm_num)
  obtain ⟨CH, hCH, hHu⟩ := RawEulerProduct31.correctionProduct_subpower_paddedBoxes D 1 one_pos
  obtain ⟨Hc, hHc⟩ : ∃ Hc : ℝ, ∀ p ∈ EulerDomain.paddedBoxes,
      ‖AllRowEuler.InitialSeparation.correctionProduct D.context (rawFrequency D u)
        p.1 p.2.1 p.2.2‖ ≤ Hc :=
    ⟨_, fun p hp => (hHu (rawFrequency D u) p hp).2⟩
  obtain ⟨C4, hC4, hminus⟩ := RawRightHecke31.minus_right D 4 (by norm_num)
  obtain ⟨CM, hCM⟩ := D.M_vertical_decay Scales.zLine Scales.zLine
    (by unfold Scales.zLine; norm_num) le_rfl 2
  have hcont : Continuous (fun y : ℝ => Z ^ (Scales.kernelExponent ξ.re y Scales.zLine)) :=
    continuous_const.rpow (by unfold Scales.kernelExponent; fun_prop) (fun _ => Or.inl hZ.ne')
  obtain ⟨CZ, hCZ⟩ := (isCompact_Icc (a := Scales.wLine - EulerDomain.pad / 2)
    (b := 4 + EulerDomain.pad / 2)).exists_bound_of_continuousOn hcont.continuousOn
  have hmi : ‖(pkg D).minus u ξ‖⁻¹ ≤ C4 := by
    rw [← norm_inv]; exact (hminus u ξ hξ.ge).2.2
  refine ⟨|CZ| * frequencyNorm D.recipe u ^ (-Scales.zLine) * Real.exp ((4 + Scales.zLine - 1) ^ 2) *
    |CM| * CWL * C1 * |Hc| * C4, by positivity, ?_⟩
  intro y s t h1y h2y
  have hwre : (((y : ℂ) + (t : ℂ) * I)).re = y := by simp
  have hzre : (((Scales.zLine : ℂ) + (s : ℂ) * I)).re = Scales.zLine := by simp
  have e : ‖rawKernel D u ξ ((y : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖ =
      Z ^ (Scales.kernelExponent ξ.re y Scales.zLine) * frequencyNorm D.recipe u ^ (-Scales.zLine) *
        (Real.exp ((ξ.re + Scales.zLine - 1) ^ 2) * Real.exp (-(ξ.im + s) ^ 2) *
          ‖D.M ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ * ‖D.W1Hat ((y : ℂ) + (t : ℂ) * I)‖) *
        (‖D.recipe.L (6 * ((Scales.zLine : ℂ) + (s : ℂ) * I))‖ *
          ‖(pkg D).plus u ((y : ℂ) + (t : ℂ) * I)‖ *
          ‖AllRowEuler.InitialSeparation.correctionProduct D.context (rawFrequency D u) ξ
            ((y : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ *
          ‖(pkg D).minus u ξ‖⁻¹) := by
    have e1 := RawKernelNorm.norm_rawKernel D u ξ Scales.zLine y (s, t) Z hZ
    rw [RawKernelNorm.weightModulus_eq, RawKernelNorm.norm_rawFactor] at e1
    exact e1
  rw [e]
  have hZb : Z ^ (Scales.kernelExponent ξ.re y Scales.zLine) ≤ |CZ| := by
    have h := hCZ y ⟨h1y, h2y⟩
    simp only [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_abs_self _))
  have hGb : Real.exp ((ξ.re + Scales.zLine - 1) ^ 2) * Real.exp (-(ξ.im + s) ^ 2) ≤
      Real.exp ((4 + Scales.zLine - 1) ^ 2) := by
    rw [hξ]
    calc Real.exp ((4 + Scales.zLine - 1) ^ 2) * Real.exp (-(ξ.im + s) ^ 2)
        ≤ Real.exp ((4 + Scales.zLine - 1) ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
            (Real.exp_pos _).le
      _ = Real.exp ((4 + Scales.zLine - 1) ^ 2) := mul_one _
  have hpos : (0 : ℝ) < 1 + |s| := by positivity
  have hMb : ‖D.M ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ ≤ |CM| * (1 + |s|) ^ (-(2 : ℝ)) := by
    have h := hCM ((Scales.zLine : ℂ) + (s : ℂ) * I) hzre.ge hzre.le
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
  have hcp : ‖AllRowEuler.InitialSeparation.correctionProduct D.context (rawFrequency D u) ξ
      ((y : ℂ) + (t : ℂ) * I) ((Scales.zLine : ℂ) + (s : ℂ) * I)‖ ≤ |Hc| :=
    (hHc _ hmem).trans (le_abs_self _)
  have hLb : ‖D.recipe.L (6 * ((Scales.zLine : ℂ) + (s : ℂ) * I))‖ ≤ C1 :=
    (hLz _ hzre.ge).2.1
  have hWP := hWL y t h1y h2y
  have hfin := comb_aux hZb hGb hMb hWP hLb hcp hmi
    (Real.rpow_nonneg hZ.le _) hQ (Real.exp_pos _).le (Real.exp_pos _).le (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (inv_nonneg.mpr (norm_nonneg _)) (abs_nonneg _) (Real.exp_pos _).le
    (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hpos.le _))
    (mul_nonneg hCWL0 (Real.rpow_nonneg (by positivity) _)) hC1.le (abs_nonneg _)
  refine le_trans hfin (le_of_eq ?_)
  ring

private theorem kdiff (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) (w z : ℂ)
    (hw : Scales.wLine - EulerDomain.pad / 2 < w.re) (hz : z.re = Scales.zLine) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => rawKernel D u p.1 p.2.1 p.2.2 Z) (ξ, w, z) := by
  have hw0 : (1 / 10 : ℝ) < w.re := by
    have h := hw
    unfold Scales.wLine EulerDomain.pad at h
    linarith
  have hz' : z.re = 2 / 5 := by rw [hz]; unfold Scales.zLine; norm_num
  have hmemΩ : ((ξ, w, z) : ℂ × ℂ × ℂ) ∈ EulerDomain.OmegaStar := by
    show 0 < ξ.re ∧ 0 < w.re ∧ 0 < z.re ∧ 1 < 6 * z.re + w.re ∧ 1 < ξ.re + 6 * z.re ∧
      1 < ξ.re + w.re ∧ 2 < ξ.re + w.re + 6 * z.re ∧ 5 < 6 * ξ.re + 6 * z.re ∧
      1 / 2 < ξ.re ∧ 2 < 3 * ξ.re ∧ 5 / 2 < 3 * ξ.re + w.re
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨C4, _, hminus⟩ := RawRightHecke31.minus_right D 4 (by norm_num)
  have hne : (pkg D).minus u ξ ≠ 0 := (hminus u ξ hξ.ge).1
  exact RawKernelRegularity31.rawKernel_differentiableAt D u hu Z hZ (ξ, w, z) hmemΩ
    (by show (1 : ℝ) / 6 < z.re; rw [hz]; unfold Scales.zLine; norm_num) hne

theorem rawKernel_differentiableOn_w (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 0 < Z) (ξ z : ℂ) (hξ : ξ.re = 4)
    (hz : z.re = Scales.zLine) :
    DifferentiableOn ℂ (fun w : ℂ => rawKernel D u ξ w z Z)
      {w : ℂ | Scales.wLine - EulerDomain.pad / 2 < w.re ∧ w.re < 4 + EulerDomain.pad / 2} := by
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hd := kdiff D u hu Z hZ ξ hξ w z hw1 hz
  have hf : DifferentiableAt ℂ (fun w : ℂ => ((ξ, w, z) : ℂ × ℂ × ℂ)) w := by fun_prop
  exact (hd.comp w hf).differentiableWithinAt

theorem Iz_differentiableOn_w (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    DifferentiableOn ℂ (fun w : ℂ => Iz D u ξ w Scales.zLine Z)
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
      rawKernel D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := ⟨_, fun _ _ => rfl⟩
  have hcont : ∀ w ∈ U, Continuous (G w) := by
    intro w hw
    have hfun : G w = fun s : ℝ => (2 * (Real.pi : ℂ))⁻¹ *
        rawKernel D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := funext (hG w)
    rw [hfun]
    refine continuous_const.mul ?_
    refine continuous_iff_continuousAt.mpr (fun s => ?_)
    have hd := kdiff D u hu Z hZ ξ hξ w ((Scales.zLine : ℂ) + (s : ℂ) * I)
      (hwU w hw).1 (by simp)
    have hc : Continuous (fun s : ℝ =>
        ((ξ, w, ((Scales.zLine : ℂ) + (s : ℂ) * I)) : ℂ × ℂ × ℂ)) := by fun_prop
    exact ContinuousAt.comp
      (g := fun p : ℂ × ℂ × ℂ => rawKernel D u p.1 p.2.1 p.2.2 Z)
      (f := fun s : ℝ => ((ξ, w, ((Scales.zLine : ℂ) + (s : ℂ) * I)) : ℂ × ℂ × ℂ))
      (x := s) hd.continuousAt hc.continuousAt
  have hmeas : ∀ w ∈ U, AEStronglyMeasurable (G w) volume :=
    fun w hw => (hcont w hw).aestronglyMeasurable
  have hdiff : ∀ s : ℝ, DifferentiableOn ℂ (fun w => G w s) U := by
    intro s
    have h := (rawKernel_differentiableOn_w D u hu Z hZ ξ ((Scales.zLine : ℂ) + (s : ℂ) * I)
      hξ (by simp)).const_mul ((2 * (Real.pi : ℂ))⁻¹)
    have hfun : (fun w => G w s) = fun w : ℂ => (2 * (Real.pi : ℂ))⁻¹ *
        rawKernel D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := funext fun w => hG w s
    rw [hfun]
    exact h
  obtain ⟨C, hC0, hCb⟩ := rawKernel_w_bound D u hu Z hZ ξ hξ 0
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
            ‖rawKernel D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖
          ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * (C * (1 + |s|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = ‖(2 * (Real.pi : ℂ))⁻¹‖ * C * (1 + |s|) ^ (-(2 : ℝ)) := by ring
  have key := HolomorphicDominatedIntegral.differentiableOn_integral_of_locally_dominated
    (μ := volume) hU hmeas hdiff hdom
  have hEq : (fun w => Iz D u ξ w Scales.zLine Z) = fun w => ∫ s : ℝ, G w s := by
    funext w
    have : Iz D u ξ w Scales.zLine Z = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ s : ℝ, rawKernel D u ξ w ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := rfl
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

theorem Iz_decayOn_w (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    LowRowXiControls.DecayOn (fun w : ℂ => Iz D u ξ w Scales.zLine Z) Scales.wLine 4 := by
  intro B hB
  have hp : (0 : ℝ) < EulerDomain.pad := by unfold EulerDomain.pad; norm_num
  obtain ⟨C, hC0, hCb⟩ := rawKernel_w_bound D u hu Z hZ ξ hξ B
  refine ⟨‖(2 * (Real.pi : ℂ))⁻¹‖ * (C * ∫ s : ℝ, (1 + |s|) ^ (-(2 : ℝ))), 0, ?_⟩
  intro x hx y _
  obtain ⟨hx1, hx2⟩ := hx
  have hx1' : Scales.wLine - EulerDomain.pad / 2 ≤ x := by linarith
  have hx2' : x ≤ 4 + EulerDomain.pad / 2 := by linarith
  have hint : Integrable (fun s : ℝ => C * (1 + |s|) ^ (-(2 : ℝ)) * (1 + |y|) ^ (-B)) volume :=
    ((KernelWeightIntegration.one_add_abs_rpow_integrable 2 (by norm_num)).const_mul C).mul_const _
  have hI : Iz D u ξ ((x : ℂ) + (y : ℂ) * I) Scales.zLine Z = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ s : ℝ, rawKernel D u ξ ((x : ℂ) + (y : ℂ) * I)
          ((Scales.zLine : ℂ) + (s : ℂ) * I) Z := rfl
  have hle : ‖∫ s : ℝ, rawKernel D u ξ ((x : ℂ) + (y : ℂ) * I)
          ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖ ≤
      ∫ s : ℝ, C * (1 + |s|) ^ (-(2 : ℝ)) * (1 + |y|) ^ (-B) :=
    norm_integral_le_of_norm_le hint
      (Filter.Eventually.of_forall fun s => hCb x s y hx1' hx2')
  rw [integral_mul_const, integral_const_mul] at hle
  show ‖Iz D u ξ ((x : ℂ) + (y : ℂ) * I) Scales.zLine Z‖ ≤ _
  rw [hI, norm_mul]
  calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖∫ s : ℝ, rawKernel D u ξ ((x : ℂ) + (y : ℂ) * I)
          ((Scales.zLine : ℂ) + (s : ℂ) * I) Z‖
      ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * ((C * ∫ s : ℝ, (1 + |s|) ^ (-(2 : ℝ))) * (1 + |y|) ^ (-B)) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = ‖(2 * (Real.pi : ℂ))⁻¹‖ * (C * ∫ s : ℝ, (1 + |s|) ^ (-(2 : ℝ))) * (1 + |y|) ^ (-B) := by
        ring

theorem Iwz_w_shift (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    Iwz D u ξ 4 Scales.zLine Z = Iwz D u ξ Scales.wLine Scales.zLine Z := by
  unfold Iwz
  exact LowRowXiControls.verticalIntegral_eq_of_decayOn (by norm_num [Scales.wLine])
    (Iz_differentiableOn_w D u hu Z hZ ξ hξ) (Iz_decayOn_w D u hu Z hZ ξ hξ)

end

end DedekindZetaZeroFree.Quantitative.RawLowWControls31
