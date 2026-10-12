module

public import DedekindZetaZeroFree.Moments.Principal.Numerator.StripRegularization
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalErrorStripBounds
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalProductSpectralProperties
public import DedekindZetaZeroFree.Nonvanishing.Mellin.NonprincipalContinuationContourBounds

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
noncomputable section
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem tail_envelope_bound (t ν : ℝ) :
    comparisonHeightEnvelope 4 t 0 ν ≤ Real.exp 2 *
      (1 + |t|) ^ (-2 : ℝ) * (1 + |ν|) ^ (-2 : ℝ) := by
  have hs : (1+|ν|)^(-2 : ℝ) ≤ (1+|t|)^(-2 : ℝ) * (1+|t+ν|)^(2 : ℝ) := by
    have ht : 1+|t| ≤ (1+|t+ν|)*(1+|ν|) := by
      have hh : |t| ≤ |t+ν|+|ν| := by simpa using abs_sub (t+ν) ν
      nlinarith [abs_nonneg (t+ν), abs_nonneg ν]
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1+|t|) ht (by norm_num : (0:ℝ) ≤ 2)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hh
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    have hd : (1+|t|)^(2 : ℝ) / (1+|ν|)^(2 : ℝ) ≤ (1+|t+ν|)^(2 : ℝ) :=
      (div_le_iff₀ (by positivity)).mpr hh
    have hi := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ ((1+|t|)^(2 : ℝ))⁻¹)
    have ht0 : (1+|t|) ^ (2 : ℕ) ≠ 0 := by positivity
    simpa [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ ht0] using hi
  have hg (x : ℝ) : Real.exp (-x^2) * (1+|x|)^(2 : ℝ) ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+|x|)
    nlinarith [sq_nonneg (|x|-1), sq_abs x]
  have hmain : Real.exp (-(t+ν)^2) * (1+|ν|)^(-2 : ℝ) ≤
      Real.exp 2 * (1+|t|)^(-2 : ℝ) := by
    calc
      _ ≤ Real.exp (-(t+ν)^2) * ((1+|t|)^(-2 : ℝ) * (1+|t+ν|)^(2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
      _ = (Real.exp (-(t+ν)^2) * (1+|t+ν|)^(2 : ℝ)) * (1+|t|)^(-2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hg _) (by positivity)
  have hz : (1+|ν|)^(-4 : ℝ) = (1+|ν|)^(-2 : ℝ) * (1+|ν|)^(-2 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  simp only [comparisonHeightEnvelope, abs_zero, add_zero, Real.one_rpow, mul_one]
  rw [hz, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hmain (by positivity)

theorem z_residue_kernel_uniform_tail_decay
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1)
    (Z : ℝ) (hZ : 1 ≤ Z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ z : ℂ, ξ.re = comparisonSigma₁ →
      z ∈ comparisonClosedStrip PrincipalZShift.zLine comparisonZeta₁ →
      1 ≤ |z.im| →
      ‖PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat R.L R.L
        (correction R C U) ξ z‖ ≤
        B * (1 + |ξ.im|) ^ (-2 : ℝ) * (1 + |z.im|) ^ (-2 : ℝ) := by
  obtain ⟨AN, d, hAN, hd, hN⟩ := PrincipalNumerator.stripNumerator_bound_away_pole
     R (9/10) 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨BL, hBL, hL⟩ := PrincipalNumerator.rightHalfPlane_reciprocal_bound R
    comparisonSigma₁ (by norm_num [comparisonSigma₁, comparisonDelta])
  obtain ⟨BH, hBH, hH⟩ := (ThreeVariableProduct.three_variable_product C).2.1 1 (by norm_num)
  let CH := BH * (R.A.exteriorNorm U.ideal) ^ (1 : ℝ)
  have hCH : 0 ≤ CH := mul_nonneg hBH.le (Real.rpow_nonneg (by
    simp [SArithmeticData.exteriorNorm, idealNorm]) _)
  have hW : comparisonRapidStripDecay R.W.W1Hat 1 1 := by
    intro N hN
    obtain ⟨CW, hCW, hb⟩ := ProbeSheet.MellinProof.realWeight_mellin_rapid_on_strip
      R.probe.W1 1 1 N hN
    refine ⟨CW+1, by positivity, ?_⟩
    intro s hs
    have h := hb s.re hs s.im
    rw [Complex.re_add_im] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  obtain ⟨BW, hBW, hweight⟩ := comparisonGaussianMellinWeight_polynomial_bound
    R.W.M R.W.W1Hat comparisonSigma₁ comparisonSigma₁ 1 1
    PrincipalZShift.zLine comparisonZeta₁ 4 0 d (le_refl _) (le_refl _)
    (by norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta])
    (by norm_num [PrincipalZShift.zLine]) (by norm_num) (by norm_num) hd
    (error_mellin_decay R) hW
  let SX := Real.exp ((1/2:ℝ) * Real.log (comparisonX Z))
  let SZ := Real.exp (2 * Real.log Z)
  have hX : 1 ≤ comparisonX Z := by
    unfold comparisonX
    exact Real.one_le_rpow hZ (by norm_num [comparisonA])
  have hlX := Real.log_nonneg hX
  have hlZ := Real.log_nonneg hZ
  refine ⟨SX * SZ * BW * (AN * 6 ^ d) * BL * CH * Real.exp 2,
    by dsimp [SX, SZ]; positivity, ?_⟩
  intro ξ z hξ hz hheight
  have hzr := hz
  simp only [comparisonClosedStrip, Set.mem_setOf_eq] at hzr
  have hN' := hN (6*z)
    (by norm_num [Complex.mul_re]; norm_num [PrincipalZShift.zLine] at hzr; linarith [hzr.1])
    (by norm_num [Complex.mul_re]; norm_num [comparisonZeta₁, comparisonDelta] at hzr; linarith [hzr.2])
    (by
      have hi := Complex.abs_im_le_norm (6*z-1)
      norm_num [Complex.mul_im, Complex.sub_im, abs_mul] at hi
      linarith)
  have hn : ‖R.L (6*z)‖ ≤ (AN * 6 ^ d) * (2+|z.im|)^d := by
    have hp : (2+|(6*z).im|)^d ≤ 6^d * (2+|z.im|)^d := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) (by positivity)]
      apply Real.rpow_le_rpow (by positivity) _ hd
      norm_num [Complex.mul_im, abs_mul]
      linarith [abs_nonneg z.im]
    exact hN'.trans ((mul_le_mul_of_nonneg_left hp hAN.le).trans_eq (by ring))
  have hl := hL ξ hξ.ge
  have hxOmega : (ξ,(1:ℂ),z) ∈ CorrectionFactors.Omega := by
    apply Or.inr
    dsimp [CorrectionFactors.omegaSecond]
    norm_num [hξ, comparisonSigma₁, comparisonDelta]
    norm_num [PrincipalZShift.zLine] at hzr
    linarith [hzr.1]
  have hh : ‖correction R C U ξ 1 z‖ ≤ CH := hH U (ξ,1,z) hxOmega
  have hsX : ‖comparisonRealPower (comparisonX Z) (1/2-z)‖ ≤ SX := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re]
    norm_num
    norm_num [PrincipalZShift.zLine] at hzr
    nlinarith [hzr.1]
  have hsZ : ‖comparisonRealPower Z (ξ+z-1)‖ ≤ SZ := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    apply Real.exp_le_exp.mpr
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, hξ]
    norm_num [comparisonSigma₁, comparisonZeta₁, comparisonDelta] at hzr ⊢
    nlinarith [hzr.2]
  have hw := hweight ξ 1 z (by simp [comparisonClosedStrip, hξ])
    (by simp [comparisonClosedStrip]) hz
  simp only [Complex.one_im, abs_zero, add_zero, Real.rpow_zero, mul_one] at hw
  have he := tail_envelope_bound ξ.im z.im
  have hb : ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ 1 z‖ *
      (2+|z.im|)^d ≤ BW * Real.exp 2 * (1+|ξ.im|)^(-2:ℝ) * (1+|z.im|)^(-2:ℝ) :=
    hw.trans ((mul_le_mul_of_nonneg_left he hBW.le).trans_eq (by ring))
  have heq : ‖PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat R.L R.L
      (correction R C U) ξ z‖ =
      ‖comparisonRealPower (comparisonX Z) (1/2-z)‖ *
      ‖comparisonRealPower Z (ξ+z-1)‖ *
      ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ 1 z‖ *
      (‖R.L (6*z)‖ * ‖(R.L ξ)⁻¹‖) * ‖correction R C U ξ 1 z‖ := by
    unfold PrincipalWShift.residueKernel comparisonGaussianMellinWeight
    simp only [norm_mul, norm_div, div_eq_mul_inv, norm_inv]
    ring
  rw [heq]
  calc
    _ ≤ SX * SZ * ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ 1 z‖ *
        (((AN * 6^d) * (2+|z.im|)^d) * BL) * CH := by
      gcongr
    _ = SX * SZ * (AN * 6^d) * BL * CH *
        (‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ 1 z‖ * (2+|z.im|)^d) := by ring
    _ ≤ SX * SZ * (AN * 6^d) * BL * CH *
        (BW * Real.exp 2 * (1+|ξ.im|)^(-2:ℝ) * (1+|z.im|)^(-2:ℝ)) := by
      gcongr
    _ = _ := by ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
noncomputable section
open MeasureTheory Complex
open scoped Classical NumberField Topology
set_option maxHeartbeats 2000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private lemma residue_envelope_integrable : Integrable (fun p : ℝ × ℝ =>
    Real.exp (-(p.1 + p.2) ^ 2) * (1 + |p.2|) ^ (-2 : ℝ)) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq_iff (b := (1 : ℝ))).mpr (by norm_num)
  have hi : Integrable (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := 2) (μ := volume) (by simp))
  have hp := hg.mul_prod hi
  rw [← Measure.volume_eq_prod] at hp
  have hs := (measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)).integrable_comp_of_integrable hp
  convert hs using 1
  ext p
  simp only [Function.comp_def]

theorem z_residue_kernel_nonpolar_line_integrable
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1)
    (Z : ℝ) (hZ : 1 ≤ Z)
    (σz : ℝ) (hσz : σz ∈ Set.Icc PrincipalZShift.zLine comparisonZeta₁)
    (hne : σz ≠ 1 / 6) :
    Integrable (fun t : ℝ × ℝ =>
      PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat R.L R.L
        (correction R C U)
        ((comparisonSigma₁ : ℂ) + (t.1 : ℂ) * Complex.I)
        ((σz : ℂ) + (t.2 : ℂ) * Complex.I)) := by
  let xi (t : ℝ × ℝ) : ℂ := comparisonSigma₁ + (t.1 : ℂ) * I
  let zz (t : ℝ × ℝ) : ℂ := σz + (t.2 : ℂ) * I
  have hx (t) : (xi t).re = comparisonSigma₁ := by simp [xi]
  have hz (t) : (zz t).re = σz := by simp [zz]
  have hpos : 0 < σz := lt_of_lt_of_le (by norm_num [PrincipalZShift.zLine]) hσz.1
  have hsep : 0 < |6 * σz - 1| := abs_pos.mpr (by
    intro he
    apply hne
    linarith)
  have homega (t) : (xi t, (1 : ℂ), zz t) ∈ CorrectionFactors.Omega := by
    apply Or.inr
    refine ⟨?_, ?_, ?_⟩
    · rw [hx]; norm_num [comparisonSigma₁, comparisonDelta]
    · norm_num
    · rw [hz]
      have hb := hσz.1
      dsimp [PrincipalZShift.zLine] at hb
      linarith
  have hc : Continuous (fun t : ℝ × ℝ => correction R C U (xi t) 1 (zz t)) := by
    have hh := CorrectionFactors.continuous_H_u C U
    have he : Continuous (fun t => (⟨(xi t, (1 : ℂ), zz t), homega t⟩ : CorrectionFactors.Omega)) := by
      apply Continuous.subtype_mk
      dsimp [xi, zz]
      fun_prop
    simpa only [Function.comp_def, CorrectionFactors.H_u, correction] using hh.comp he
  have hL : DifferentiableOn ℂ R.L {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
    change DifferentiableOn ℂ (fun s => R.continuation.L s * ∏ v ∈ R.A.Sf,
      (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))) _
    apply R.continuation.L_holo.mul
    apply DifferentiableOn.fun_finset_prod
    intro v hv
    exact ((((differentiable_id.neg).mul_const
      (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
        (R.target v.asIdeal)).differentiableOn.const_sub 1
  have hlx : Continuous (fun t => R.L (xi t)) :=
    hL.continuousOn.comp_continuous (by dsimp [xi]; fun_prop) (by
      intro t
      refine ⟨?_, ?_⟩
      · rw [hx]; norm_num [comparisonSigma₁, comparisonDelta]
      · intro he
        have := congrArg Complex.re he
        rw [hx] at this
        norm_num [comparisonSigma₁, comparisonDelta] at this)
  have hlz : Continuous (fun t => R.L (6 * zz t)) :=
    hL.continuousOn.comp_continuous (by dsimp [zz]; fun_prop) (by
      intro t
      refine ⟨?_, ?_⟩
      · simp [hz]
        positivity
      · intro he
        have := congrArg Complex.re he
        simp [hz] at this
        apply hne
        linarith)
  have hm := (error_mellin_measurable R).comp (show Measurable zz by dsimp [zz]; fun_prop)
  have hmeas : Measurable (fun t : ℝ × ℝ =>
      PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U) (xi t) (zz t)) := by
    unfold PrincipalWShift.residueKernel comparisonRealPower
    apply Measurable.mul _ hc.measurable
    apply Measurable.mul _ (hlz.measurable.div hlx.measurable)
    apply Measurable.mul _ measurable_const
    apply Measurable.mul _ hm
    dsimp [xi, zz]
    fun_prop
  obtain ⟨BN, d, hBN, hd, hbN⟩ := PrincipalNumerator.stripNumerator_bound_away_pole R
    (6 * σz) (6 * σz) |6 * σz - 1| (by positivity) (le_refl _)
    (by nlinarith [hσz.2, show comparisonZeta₁ < (2 : ℝ) / 3 by norm_num [comparisonZeta₁, comparisonDelta]]) hsep
  have hn (z : ℂ) (hz : z.re = σz) :
      ‖R.L (6 * z)‖ ≤ (BN * 6 ^ d) * (2 + |z.im|) ^ d := by
    have hb := hbN (6*z) (by simp [hz]) (by simp [hz]) (by
      simpa [hz] using Complex.abs_re_le_norm (6*z-1))
    have him : (6*z).im = 6*z.im := by simp
    rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)] at hb
    calc ‖R.L (6*z)‖ ≤ BN * (2 + 6 * |z.im|) ^ d := hb
      _ ≤ BN * (6 * (2 + |z.im|)) ^ d := by
        apply mul_le_mul_of_nonneg_left _ hBN.le
        apply Real.rpow_le_rpow (by positivity) _ hd
        linarith [abs_nonneg z.im]
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  obtain ⟨BL, hBL, hbL⟩ := PrincipalNumerator.rightHalfPlane_reciprocal_bound R comparisonSigma₁
    (by norm_num [comparisonSigma₁, comparisonDelta])
  obtain ⟨BH, hBH, hbH⟩ := CorrectionFactors.H_u_uniform_subpower_bound C 1 (by norm_num)
  let CH := BH * (R.A.exteriorNorm U.ideal) ^ (1 : ℝ)
  have hCH : 0 ≤ CH := mul_nonneg hBH.le (Real.rpow_nonneg (by
    simp [SArithmeticData.exteriorNorm, idealNorm]) _)
  have hh (t) : ‖correction R C U (xi t) 1 (zz t)‖ ≤ CH :=
    hbH U (xi t, 1, zz t) (homega t)
  have hneTrace : ∀ v, R.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := R.probe.finiteTrace_ne_one R.A R.σ R.target R.traceBad v
    exact hx (by rw [he]; rfl)
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F R.A
    R.probe.finiteTrace R.probe.continuousTrace R.probe.traceCompatible hneTrace
    R.probe.additiveMeasure R.probe.multiplicativeMeasure
    R.probe.additiveHaar R.probe.multiplicativeHaar (Classical.choice inferInstance)
    R.probe.W0 R.probe.W1 R.probe.annular R.probe.compactSupport R.probe.supportUnits
  rcases hsheet with ⟨_, _, _, _, _, _, hWd, _⟩
  have hwdecay : comparisonRapidStripDecay R.W.W1Hat 1 1 := by
    intro B hB
    obtain ⟨K, hK, hb⟩ := hWd 1 1 B (le_refl _) hB
    refine ⟨K+1, by linarith, ?_⟩
    intro w hw
    have hh := hb w.re hw w.im
    rw [Complex.re_add_im] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))
  obtain ⟨BW, hBW, hbW⟩ := comparisonGaussianMellinWeight_polynomial_bound R.W.M R.W.W1Hat
    comparisonSigma₁ comparisonSigma₁ 1 1 PrincipalZShift.zLine comparisonZeta₁ 2 0 d
    (le_refl _) (le_refl _) (by norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta])
    (by norm_num [PrincipalZShift.zLine]) (by norm_num) (by norm_num) hd (error_mellin_decay R) hwdecay
  let scale := Real.exp ((1/2-σz) * Real.log (comparisonX Z)) *
    Real.exp ((comparisonSigma₁+σz-1) * Real.log Z)
  have hs (t) : ‖comparisonRealPower (comparisonX Z) (1/2-zz t) *
      comparisonRealPower Z (xi t+zz t-1)‖ = scale := by
    rw [norm_mul, MellinZeroFree.norm_comparisonRealPower, MellinZeroFree.norm_comparisonRealPower]
    simp [scale, hx, hz]
  let K := scale * BW * (BN * 6 ^ d) * BL * CH
  have hbound (t : ℝ × ℝ) :
      ‖PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U) (xi t) (zz t)‖ ≤
        K * (Real.exp (-(t.1+t.2)^2) * (1+|t.2|)^(-2 : ℝ)) := by
    have hw := hbW (xi t) 1 (zz t) (by simp [comparisonClosedStrip, hx])
      (by norm_num [comparisonClosedStrip]) (by simpa [comparisonClosedStrip, hz] using hσz)
    simp only [Real.rpow_zero, mul_one] at hw
    have hl := hbL (xi t) (by rw [hx])
    have hnum := hn (zz t) (hz t)
    have hc := hh t
    have heq : PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U) (xi t) (zz t) =
      (comparisonRealPower (comparisonX Z) (1/2-zz t) * comparisonRealPower Z (xi t+zz t-1)) *
      comparisonGaussianMellinWeight R.W.M R.W.W1Hat (xi t) 1 (zz t) *
      (R.L (6*zz t) * (R.L (xi t))⁻¹) * correction R C U (xi t) 1 (zz t) := by
      unfold PrincipalWShift.residueKernel comparisonGaussianMellinWeight
      simp only [div_eq_mul_inv]
      ring
    rw [heq, norm_mul, norm_mul, norm_mul, hs, norm_mul]
    calc scale * ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat (xi t) 1 (zz t)‖ *
          (‖R.L (6*zz t)‖ * ‖(R.L (xi t))⁻¹‖) * ‖correction R C U (xi t) 1 (zz t)‖
        ≤ scale * ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat (xi t) 1 (zz t)‖ *
          (((BN * 6 ^ d) * (2+|(zz t).im|)^d) * BL) * CH := by
          gcongr
      _ = (scale * (BN * 6 ^ d) * BL * CH) *
          (‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat (xi t) 1 (zz t)‖ * (2+|(zz t).im|)^d) := by ring
      _ ≤ (scale * (BN * 6 ^ d) * BL * CH) *
          (BW * comparisonHeightEnvelope 2 (xi t).im 0 (zz t).im) := by
          apply mul_le_mul_of_nonneg_left hw
          dsimp [scale]; positivity
      _ = _ := by
          simp [K, comparisonHeightEnvelope, xi, zz]
          ring
  exact (residue_envelope_integrable.const_mul K).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
noncomputable section
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem z_regularization_off_pole (R : PrincipalMellin.ActualRecipe S η) (z : ℂ)
    (hz : 0 < z.re) (hne : z ≠ 1 / 6) :
    regularization R (6*z) = (6*z-1) * R.L (6*z) := by
  have hs : 0 < (6*z).re := by simp only [Complex.mul_re]; norm_num; linarith
  have hsne : 6*z ≠ 1 := by intro h; apply hne; linear_combination h / 6
  unfold regularization PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
  rw [R.continuation.regularized _ hs hsne]
  ring

theorem z_clearedKernel_differentiableOn (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (Z : ℝ) (ξ : ℂ)
    (hξ : ξ.re = comparisonSigma₁) :
    DifferentiableOn ℂ
      (fun z => PrincipalZShift.clearedKernel Z R.W.M R.W.W1Hat R.L
        (regularization R) (correction R C U) ξ z)
      {z : ℂ | PrincipalZShift.zLine - 1 / 100000 < z.re} := by
  let V : Set ℂ := {z : ℂ | PrincipalZShift.zLine - 1 / 100000 < z.re}
  have hpos : ∀ z ∈ V, 0 < z.re := by
    intro z hz
    dsimp [V, PrincipalZShift.zLine] at hz
    linarith
  have hcorr : DifferentiableOn ℂ (fun z => correction R C U ξ 1 z) V := by
    apply (CorrectionFactors.differentiableOn_H_u_z C U ξ 1).mono
    intro z hz
    apply Or.inr
    refine ⟨?_, ?_, ?_⟩
    · rw [hξ]; norm_num [comparisonSigma₁, comparisonDelta]
    · norm_num
    · exact hz
  have hM : DifferentiableOn ℂ R.W.M V :=
    (ContinuationSteps.actual_mellin_weight_far_inputs R).1.mono hpos
  have hreg : DifferentiableOn ℂ (regularization R) {s : ℂ | 0 < s.re} := by
    apply R.continuation.R_holo.mul
    apply DifferentiableOn.fun_finset_prod
    intro v hv
    exact ((((differentiable_id.neg).mul_const
      (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
        (R.target v.asIdeal)).differentiableOn.const_sub 1
  have hreg6 : DifferentiableOn ℂ (fun z => regularization R (6*z)) V := by
    apply hreg.comp (differentiable_id.const_mul 6).differentiableOn
    intro z hz
    dsimp
    have hp := hpos z hz
    simp only [Complex.mul_re]; norm_num; linarith
  have hpX : DifferentiableOn ℂ
      (fun z : ℂ => comparisonRealPower (comparisonX Z) (1/2-z)) V :=
    (((differentiable_id.const_sub (1/2)).mul_const
      (Real.log (comparisonX Z) : ℂ)).cexp).differentiableOn
  have hpZ : DifferentiableOn ℂ
      (fun z : ℂ => comparisonRealPower Z (ξ+z-1)) V :=
    ((((differentiable_id.const_add ξ).sub_const 1).mul_const
      (Real.log Z : ℂ)).cexp).differentiableOn
  have hE : DifferentiableOn ℂ (fun z : ℂ => Complex.exp ((ξ+z-1)^2)) V :=
    (((differentiable_id.const_add ξ).sub_const 1).pow 2).cexp.differentiableOn
  exact (((((hpX.mul hpZ).mul hE).mul hM).mul_const (R.W.W1Hat 1)).mul
    ((hreg6.div_const 6).div_const (R.L ξ))).mul hcorr

open MeasureTheory

theorem z_residue_integrable (R : PrincipalMellin.ActualRecipe S η) (Z : ℝ) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => PrincipalZShift.transformKernel Z R.L R.H
      ((comparisonSigma₁ : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨_, _, hG, hb, _⟩ := PrincipalMellin.actual_principal_spectral_properties S η R
  obtain ⟨C, hC, hbound⟩ := hb comparisonSigma₁ comparisonSigma₁
    (by norm_num [comparisonSigma₁, comparisonDelta]) le_rfl
  let B : ℝ := Real.exp ((comparisonSigma₁ - 8 / 15) * Real.log Z)
  have hB : 0 < B := Real.exp_pos _
  have heq (s : ℂ) : PrincipalZShift.transformKernel Z R.L R.H s =
      comparisonRealPower Z (comparisonC s) * R.G s := by
    unfold PrincipalZShift.transformKernel PrincipalMellin.ActualRecipe.G
      PrincipalMellin.ActualRecipe.N
    ring
  have hcont : Continuous (fun t : ℝ => PrincipalZShift.transformKernel Z R.L R.H
      ((comparisonSigma₁ : ℂ) + (t : ℂ) * Complex.I)) := by
    have hline : ∀ t : ℝ, 1 < (((comparisonSigma₁ : ℂ) + (t : ℂ) * Complex.I)).re := by
      intro t; simp; norm_num [comparisonSigma₁, comparisonDelta]
    have hGG : Continuous (fun t : ℝ => R.G ((comparisonSigma₁ : ℂ) + (t : ℂ) * Complex.I)) :=
      hG.continuousOn.comp_continuous (by fun_prop) hline
    simp_rw [heq]
    have hp : Continuous (fun t : ℝ => comparisonRealPower Z
        (comparisonC ((comparisonSigma₁ : ℂ) + (t : ℂ) * Complex.I))) := by
      unfold comparisonRealPower comparisonC
      fun_prop
    exact hp.mul hGG
  apply ((integrable_inv_one_add_sq).const_mul (B*C)).mono' hcont.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [heq, norm_mul]
  have hp : ‖comparisonRealPower Z
      (comparisonC ((comparisonSigma₁ : ℂ) + (t : ℂ) * Complex.I))‖ = B := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    simp [comparisonC, B]
  rw [hp]
  have hg : ‖R.G ((comparisonSigma₁ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1+t^2) :=
    hbound comparisonSigma₁ ⟨le_rfl, le_rfl⟩ t
  calc
    _ ≤ B * (C / (1+t^2)) := mul_le_mul_of_nonneg_left hg hB.le
    _ = _ := by ring

theorem z_contour
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1)
    (Z : ℝ) (hZ : 1 ≤ Z) :
    Nonempty (PrincipalZShift.ZContourConditions Z R.W.M R.W.W1Hat R.L R.L
      (regularization R) R.H (correction R C U)) := by
  obtain ⟨B, hB, hdecay⟩ :=
    z_residue_kernel_uniform_tail_decay R C hC U hU Z hZ
  refine ⟨{
    U := {z : ℂ | PrincipalZShift.zLine - 1 / 100000 < z.re}
    C := B
    C_nonneg := hB
    open_U := isOpen_lt continuous_const Complex.continuous_re
    strip := ?_
    regularization := ?_
    holomorphic := fun ξ hξ => z_clearedKernel_differentiableOn R C U Z ξ hξ
    decay := hdecay
    endpoints := ?_
    residue := z_residue_integrable R Z hZ
  }⟩
  · intro z hz
    change PrincipalZShift.zLine ≤ z.re ∧ z.re ≤ comparisonZeta₁ at hz
    change PrincipalZShift.zLine - 1 / 100000 < z.re
    linarith [hz.1]
  · intro z hz hne
    apply z_regularization_off_pole R z _ hne
    change PrincipalZShift.zLine - 1 / 100000 < z.re at hz
    norm_num [PrincipalZShift.zLine] at hz
    linarith
  · intro σz hσz
    apply z_residue_kernel_nonpolar_line_integrable R C hC U hU Z hZ σz
    · rcases hσz with hσz | hσz
      · subst σz
        norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta]
      · have heq : σz = comparisonZeta₁ := hσz
        subst σz
        norm_num [PrincipalZShift.zLine, comparisonZeta₁, comparisonDelta]
    · rcases hσz with hσz | hσz
      · subst σz
        norm_num [PrincipalZShift.zLine]
      · have heq : σz = comparisonZeta₁ := hσz
        subst σz
        norm_num [comparisonZeta₁, comparisonDelta]

end
end DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs

end
