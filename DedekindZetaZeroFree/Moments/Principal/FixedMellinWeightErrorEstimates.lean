module

public import DedekindZetaZeroFree.Moments.Comparison.PoissonMellinKernelData
public import DedekindZetaZeroFree.Moments.Comparison.ContourExponentMargins

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section

namespace PrincipalErrors

open MeasureTheory Complex

private lemma hinv : Integrable (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) := by
  apply integrable_inv_one_add_sq.mono' ((by
    exact (show Continuous (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) from
      (continuous_const.add continuous_abs).rpow_const (fun x => Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 1 + |x|)))).aestronglyMeasurable))
  filter_upwards [] with x
  have hx : 0 ≤ |x| := abs_nonneg _
  have h : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [sq_nonneg (|x|), sq_abs x]
  rw [Real.rpow_neg (by positivity), Real.rpow_two, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  simpa only [one_div] using (one_div_le_one_div_of_le (by positivity) h)
private lemma hdouble : Integrable (fun p : ℝ × ℝ =>
    Real.exp (-(p.1 + p.2) ^ 2) * (1 + |p.2|) ^ (-2 : ℝ)) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq_iff (b := (1 : ℝ))).mpr (by norm_num)
  have hp := hg.mul_prod hinv
  rw [← Measure.volume_eq_prod] at hp
  have hs := (measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)).integrable_comp_of_integrable hp
  convert hs using 1
  ext p
  simp only [Function.comp_def]
open Complex
private lemma scale_norm (Z : ℝ) (hZ : 1 ≤ Z) (ξ w z : ℂ) :
    ‖comparisonRealPower (comparisonX Z) (1 / 2 - z) *
      comparisonRealPower Z (ξ + z - 1) *
      comparisonRealPower (comparisonY Z) (w - 1)‖ =
      Z ^ (comparisonE ξ.re w.re z.re) := by
  have hpos : 0 < Z := by linarith
  unfold comparisonRealPower comparisonX comparisonY
  rw [Real.log_rpow hpos, Real.log_rpow hpos, ← Complex.exp_add, ← Complex.exp_add]
  rw [Complex.norm_exp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.one_re, Complex.one_im, Complex.add_im, mul_zero,
    sub_zero, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [Real.rpow_def_of_pos hpos]
  congr 1
  norm_num [comparisonE, comparisonA, comparisonB, comparisonH₀]
  ring
private lemma numerator_six (ζ : ℂ → ℂ) (A d r : ℝ) (hd : 0 ≤ d)
    (h : ∀ s : ℂ, s.re = 6 * r → ‖ζ s‖ ≤ A * (2 + |s.im|) ^ d)
    (hA : 0 ≤ A) (z : ℂ) (hz : z.re = r) :
    ‖ζ (6 * z)‖ ≤ (A * 6 ^ d) * (2 + |z.im|) ^ d := by
  have hb := h (6 * z) (by simp [hz])
  have hi : (6 * z).im = 6 * z.im := by simp
  rw [hi, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)] at hb
  calc ‖ζ (6 * z)‖ ≤ A * (2 + 6 * |z.im|) ^ d := hb
    _ ≤ A * (6 * (2 + |z.im|)) ^ d := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.rpow_le_rpow (by positivity) _ hd
      linarith [abs_nonneg z.im]
    _ = (A * 6 ^ d) * (2 + |z.im|) ^ d := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
private lemma kernel_bound
    (M W ζ N L : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (v r d A B D : ℝ) (hd : 0 ≤ d) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hv : v ∈ Set.Icc (19 / 20 : ℝ) 1)
    (hr : r ∈ Set.Icc PrincipalZShift.zLine comparisonZeta₁)
    (hM : comparisonRapidStripDecay M PrincipalZShift.zLine comparisonZeta₁)
    (hW : comparisonRapidStripDecay W (19 / 20) 1)
    (hN : ∀ w : ℂ, w.re = v → ‖N w‖ ≤ A * (2 + |w.im|) ^ d)
    (hζ : ∀ s : ℂ, s.re = 6 * r → ‖ζ s‖ ≤ A * (2 + |s.im|) ^ d)
    (hL : ∀ ξ : ℂ, ξ.re = comparisonSigma₁ → ‖(L ξ)⁻¹‖ ≤ B)
    (hH : ∀ ξ w z : ℂ, ξ.re = comparisonSigma₁ → w.re = v → z.re = r → ‖H ξ w z‖ ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ ξ w z : ℂ,
      ξ.re = comparisonSigma₁ → w.re = v → z.re = r →
      ‖comparisonRealPower (comparisonX Z) (1 / 2 - z) *
        comparisonRealPower Z (ξ + z - 1) * comparisonRealPower (comparisonY Z) (w - 1) *
        comparisonGaussianMellinWeight M W ξ w z * (ζ (6 * z) * N w / L ξ) * H ξ w z‖ ≤
        C * Z ^ (comparisonE comparisonSigma₁ v r) * comparisonHeightEnvelope 2 ξ.im w.im z.im := by
  obtain ⟨C, hC, hb⟩ := comparisonGaussianMellinWeight_polynomial_bound M W
    comparisonSigma₁ comparisonSigma₁ (19 / 20) 1
    PrincipalZShift.zLine comparisonZeta₁ 2 d d (le_refl _) (by norm_num)
    (by norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta])
    (by norm_num [PrincipalZShift.zLine]) (by norm_num) hd hd hM hW
  refine ⟨C * (A * 6 ^ d) * A * B * D, by positivity, ?_⟩
  intro Z hZ ξ w z hξ hw hz
  have hg := hb ξ w z (by simp [comparisonClosedStrip, hξ])
    (by simpa [comparisonClosedStrip, hw] using hv)
    (by simpa [comparisonClosedStrip, hz] using hr)
  have hn := hN w hw
  have hzeta := numerator_six ζ A d r hd hζ hA.le z hz
  have hl := hL ξ hξ
  have hh := hH ξ w z hξ hw hz
  have hs := scale_norm Z hZ ξ w z
  rw [hξ, hw, hz] at hs
  rw [norm_mul, norm_mul, norm_mul, hs, norm_div, norm_mul]
  rw [div_eq_mul_inv, ← norm_inv]
  have ht := mul_le_mul (mul_le_mul hzeta hn (norm_nonneg _) (by positivity)) hl
    (norm_nonneg _) (by positivity)
  have hu := mul_le_mul ht hh (norm_nonneg _) (by positivity)
  have hscale : 0 ≤ Z ^ (comparisonE comparisonSigma₁ v r) := Real.rpow_nonneg (by linarith) _
  calc Z ^ (comparisonE comparisonSigma₁ v r) * ‖comparisonGaussianMellinWeight M W ξ w z‖ *
        (‖ζ (6 * z)‖ * ‖N w‖ * ‖(L ξ)⁻¹‖) * ‖H ξ w z‖
      = Z ^ (comparisonE comparisonSigma₁ v r) * ‖comparisonGaussianMellinWeight M W ξ w z‖ *
        (‖ζ (6 * z)‖ * ‖N w‖ * ‖(L ξ)⁻¹‖ * ‖H ξ w z‖) := by ring
    _ ≤ Z ^ (comparisonE comparisonSigma₁ v r) * ‖comparisonGaussianMellinWeight M W ξ w z‖ *
        (((A * 6 ^ d) * (2 + |z.im|) ^ d * (A * (2 + |w.im|) ^ d) * B) * D) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (A * 6 ^ d * A * B * D) * Z ^ (comparisonE comparisonSigma₁ v r) *
        (‖comparisonGaussianMellinWeight M W ξ w z‖ * (2 + |w.im|) ^ d * (2 + |z.im|) ^ d) := by ring
    _ ≤ (A * 6 ^ d * A * B * D) * Z ^ (comparisonE comparisonSigma₁ v r) *
        (C * comparisonHeightEnvelope 2 ξ.im w.im z.im) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring

theorem fixed_weight_estimates_analytic
    (RS : ℂ) (M W ζ L : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (hM : Measurable M) (hW : Measurable W)
    (hζ : Measurable ζ) (hL : Measurable L)
    (hH : Measurable (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2))
    (hMdecay : comparisonRapidStripDecay M PrincipalZShift.zLine comparisonZeta₁)
    (hWdecay : comparisonRapidStripDecay W (19 / 20) 1)
    (hNumerator : ∃ A d : ℝ, 0 < A ∧ 0 ≤ d ∧ ∀ s : ℂ,
      s.re ∈ ({(19 / 20 : ℝ), 6 * comparisonZeta₁,
        6 * PrincipalZShift.zLine} : Set ℝ) →
      ‖ζ s‖ ≤ A * (2 + |s.im|) ^ d)
    (hReciprocal : ∃ A : ℝ, 0 < A ∧ ∀ ξ : ℂ,
      ξ.re = comparisonSigma₁ → ‖(L ξ)⁻¹‖ ≤ A)
    (hCorrection : ∃ A : ℝ, 0 < A ∧ ∀ ξ w z : ℂ,
      ξ.re = comparisonSigma₁ →
      ((w.re = 19 / 20 ∧ z.re = comparisonZeta₁) ∨
        (w = 1 ∧ z.re = PrincipalZShift.zLine)) →
      ‖H ξ w z‖ ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ‖PrincipalZShift.Rw Z M W ζ L H‖ ≤
        C * Z ^ (comparisonE comparisonSigma₁ (19 / 20) comparisonZeta₁) ∧
      ‖PrincipalZShift.Rz Z RS M W ζ L H‖ ≤
        C * Z ^ (comparisonE comparisonSigma₁ 1 (4 / 25)) ∧
      ‖PrincipalZShift.Rw Z M W ζ L H‖ +
          ‖PrincipalZShift.Rz Z RS M W ζ L H‖ ≤
        C * Z ^ ((7 / 15 : ℝ) - 1 / 2000) := by
  obtain ⟨A, d, hA, hd, hN⟩ := hNumerator
  obtain ⟨B, hB, hRec⟩ := hReciprocal
  obtain ⟨D, hD, hCor⟩ := hCorrection
  have hNr (r : ℝ) (hr : r = comparisonZeta₁ ∨ r = PrincipalZShift.zLine) :
      ∀ s : ℂ, s.re = 6 * r → ‖ζ s‖ ≤ A * (2 + |s.im|) ^ d := by
    intro s hs
    apply hN
    rcases hr with rfl | rfl <;> simp [hs]
  have hNw : ∀ w : ℂ, w.re = 19 / 20 → ‖ζ w‖ ≤ A * (2 + |w.im|) ^ d := by
    intro w hw
    exact hN w (by simp [hw])
  obtain ⟨Cw, hCw, hwBound⟩ := kernel_bound M W ζ ζ L H (19 / 20) comparisonZeta₁
    d A B D hd hA hB hD (by norm_num) ⟨by norm_num [PrincipalZShift.zLine,
      comparisonZeta₁, comparisonDelta], le_refl _⟩ hMdecay hWdecay hNw
      (hNr _ (Or.inl rfl)) hRec
      (fun ξ w z hξ hw hz => hCor ξ w z hξ (Or.inl ⟨hw, hz⟩))
  have hNz : ∀ w : ℂ, w.re = 1 → ‖(1 : ℂ)‖ ≤ (A + 1) * (2 + |w.im|) ^ d := by
    intro w hw
    have hp := Real.one_le_rpow (by linarith [abs_nonneg w.im] : (1 : ℝ) ≤ 2 + |w.im|) hd
    simpa using (show (1 : ℝ) ≤ (A + 1) * (2 + |w.im|) ^ d by nlinarith)
  obtain ⟨Cz, hCz, hzBound⟩ := kernel_bound M W ζ (fun _ => 1) L
    (fun ξ _ z => H ξ 1 z) 1 PrincipalZShift.zLine
    d (A + 1) B D hd (by linarith) hB hD (by norm_num) ⟨le_refl _,
      by norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta]⟩ hMdecay hWdecay hNz
      (fun s hs => (hNr _ (Or.inr rfl) s hs).trans (by
        apply mul_le_mul_of_nonneg_right (by linarith)
        positivity)) hRec
      (fun ξ w z hξ hw hz => hCor ξ 1 z hξ (Or.inr ⟨rfl, hz⟩))
  let Ew : ℝ × ℝ × ℝ → ℝ := fun p => comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2
  let Ez : ℝ × ℝ → ℝ := fun p => Real.exp (-(p.1 + p.2) ^ 2) * (1 + |p.2|) ^ (-2 : ℝ)
  have hEw : Integrable Ew := by
    simpa [Ew] using comparisonHeightEnvelope_integrable 0 (by norm_num)
  have hEz : Integrable Ez := hdouble
  let cw := ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ * Cw * |∫ p, Ew p|
  let cz := ‖RS‖ * ‖(2 * (Real.pi : ℂ))⁻¹ ^ 2‖ * Cz * |∫ p, Ez p|
  have hcw : 0 ≤ cw := by dsimp [cw]; positivity
  have hcz : 0 ≤ cz := by dsimp [cz]; positivity
  have bw (Z : ℝ) (hZ : 1 ≤ Z) : ‖PrincipalZShift.Rw Z M W ζ L H‖ ≤
      cw * Z ^ (comparisonE comparisonSigma₁ (19 / 20) comparisonZeta₁) := by
    have hi := norm_integral_le_of_norm_le (hEw.const_mul
      (Cw * Z ^ (comparisonE comparisonSigma₁ (19 / 20) comparisonZeta₁)))
      (f := fun p : ℝ × ℝ × ℝ => PrincipalWShift.kernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I)
        (((19 / 20 : ℝ) : ℂ) + (p.2.1 : ℂ) * I)
        ((comparisonZeta₁ : ℂ) + (p.2.2 : ℂ) * I)) (by
          filter_upwards [] with p
          have hb := hwBound Z hZ
            ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I)
            (((19 / 20 : ℝ) : ℂ) + (p.2.1 : ℂ) * I)
            ((comparisonZeta₁ : ℂ) + (p.2.2 : ℂ) * I)
            (by simp) (by simp) (by simp)
          convert hb using 1
          · congr 1
            unfold PrincipalWShift.kernel comparisonGaussianMellinWeight
            ring
          · simp [Ew])
    rw [integral_const_mul] at hi
    unfold PrincipalZShift.Rw PrincipalWShift.J comparisonTripleVerticalIntegral
    rw [norm_mul]
    calc
      _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ *
        (Cw * Z ^ (comparisonE comparisonSigma₁ (19 / 20) comparisonZeta₁) * ∫ p, Ew p) :=
      mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖ *
        (Cw * Z ^ (comparisonE comparisonSigma₁ (19 / 20) comparisonZeta₁) * |∫ p, Ew p|) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = _ := by dsimp [cw]; ring
  have bz (Z : ℝ) (hZ : 1 ≤ Z) : ‖PrincipalZShift.Rz Z RS M W ζ L H‖ ≤
      cz * Z ^ (comparisonE comparisonSigma₁ 1 (4 / 25)) := by
    have hi := norm_integral_le_of_norm_le (hEz.const_mul
      (Cz * Z ^ (comparisonE comparisonSigma₁ 1 PrincipalZShift.zLine)))
      (f := fun p : ℝ × ℝ => PrincipalWShift.residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I)
        ((PrincipalZShift.zLine : ℂ) + (p.2 : ℂ) * I)) (by
          filter_upwards [] with p
          have hb := hzBound Z hZ
            ((comparisonSigma₁ : ℂ) + (p.1 : ℂ) * I) 1
            ((PrincipalZShift.zLine : ℂ) + (p.2 : ℂ) * I)
            (by simp) (by simp) (by simp)
          convert hb using 1
          · congr 1
            unfold PrincipalWShift.residueKernel comparisonGaussianMellinWeight
            simp only [sub_self, comparisonRealPower, zero_mul, Complex.exp_zero, mul_one]
            ring
          · simp [Ez, comparisonHeightEnvelope])
    rw [integral_const_mul] at hi
    unfold PrincipalZShift.Rz PrincipalWShift.doubleVerticalIntegral
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ‖RS‖ * (‖(2 * (Real.pi : ℂ))⁻¹ ^ 2‖ *
        (Cz * Z ^ (comparisonE comparisonSigma₁ 1 PrincipalZShift.zLine) * ∫ p, Ez p)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ ≤ ‖RS‖ * (‖(2 * (Real.pi : ℂ))⁻¹ ^ 2‖ *
        (Cz * Z ^ (comparisonE comparisonSigma₁ 1 PrincipalZShift.zLine) * |∫ p, Ez p|)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = _ := by dsimp [cz, PrincipalZShift.zLine]; ring
  refine ⟨cw + cz + 1, by positivity, ?_⟩
  intro Z hZ
  have hw := bw Z hZ
  have hz := bz Z hZ
  have pw := Real.rpow_le_rpow_of_exponent_le hZ comparisonE_shifted_z_margin
  have pz := Real.rpow_le_rpow_of_exponent_le hZ comparisonE_w_residue_margin
  refine ⟨hw.trans ?_, hz.trans ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
  · apply mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
  · calc _ ≤ cw * Z ^ (comparisonE comparisonSigma₁ (19 / 20) comparisonZeta₁) +
        cz * Z ^ (comparisonE comparisonSigma₁ 1 (4 / 25)) := add_le_add hw hz
      _ ≤ cw * Z ^ ((7 / 15 : ℝ) - 1 / 2000) + cz * Z ^ ((7 / 15 : ℝ) - 1 / 2000) :=
        add_le_add (mul_le_mul_of_nonneg_left pw hcw) (mul_le_mul_of_nonneg_left pz hcz)
      _ ≤ _ := by nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Z) ((7 / 15 : ℝ) - 1 / 2000)]

end PrincipalErrors
end
end DedekindZetaZeroFree
