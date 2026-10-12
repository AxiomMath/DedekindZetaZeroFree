module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NonprincipalContinuationContourBounds
public import DedekindZetaZeroFree.Moments.Principal.Numerator.StripRegularization

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
noncomputable section
open MeasureTheory Complex
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

 def wDomain : Set ℂ := {w | 19/20-1/200000 < w.re}

private lemma wDomain_open : IsOpen wDomain :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma wDomain_strip : comparisonClosedStrip (19/20) comparisonSigma₁ ⊆ wDomain := by
  intro w hw
  dsimp [comparisonClosedStrip, wDomain] at *
  linarith [hw.1]

private lemma wDomain_omega (ξ z w : ℂ) (hξ : ξ.re = comparisonSigma₁)
    (hz : z.re = comparisonZeta₁) (hw : w ∈ wDomain) :
    (ξ,w,z) ∈ CorrectionFactors.Omega := by
  apply Or.inr
  dsimp [CorrectionFactors.omegaSecond, wDomain] at *
  refine ⟨?_, ?_, ?_⟩
  · norm_num [hξ, comparisonSigma₁, comparisonDelta]
  · linarith
  · norm_num [hz, comparisonZeta₁, comparisonDelta]

private lemma w_regularization (R : PrincipalMellin.ActualRecipe S η)
    (w : ℂ) (hw : w ∈ wDomain) (hne : w ≠ 1) :
    regularization R w = (w-1) * R.L w := by
  exact PrincipalNumerator.finiteDeletionRegularization_eq R w (by dsimp [wDomain] at hw; linarith) hne

private lemma reg_holo (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ (regularization R) {s : ℂ | 0 < s.re} := by
  apply R.continuation.R_holo.mul
  apply DifferentiableOn.fun_finset_prod
  intro v hv
  exact ((((differentiable_id.neg).mul_const
    (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
      (R.target v.asIdeal)).differentiableOn.const_sub 1

private lemma w_cleared_holo (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (Z : ℝ) (ξ z : ℂ)
    (hξ : ξ.re = comparisonSigma₁) (hz : z.re = comparisonZeta₁) :
    DifferentiableOn ℂ (fun w => PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat
      R.L R.L (regularization R) (correction R C U) ξ w z) wDomain := by
  have hH := (((ThreeVariableProduct.three_variable_product C).1 U).2.2.2.2.1 ξ z).mono
    (fun w hw => wDomain_omega ξ z w hξ hz hw)
  change DifferentiableOn ℂ (fun w => correction R C U ξ w z) wDomain at hH
  have hR := (reg_holo R).mono (show wDomain ⊆ {s : ℂ | 0 < s.re} from
    fun w hw => by dsimp [wDomain] at hw; dsimp; linarith)
  have hW := (ContinuationSteps.actual_mellin_weight_contour_inputs R).2.1.mono
    (show wDomain ⊆ {w : ℂ | 3/1000-1/100000 < w.re} from
      fun w hw => by dsimp [wDomain] at hw; dsimp; linarith)
  unfold PrincipalWShift.clearedKernel comparisonRealPower
  apply DifferentiableOn.mul _ hH
  apply DifferentiableOn.mul
  · apply DifferentiableOn.mul _ hW
    apply Differentiable.differentiableOn
    fun_prop
  · exact (hR.const_mul _).div_const _

private theorem envelope_bound (t τ ν : ℝ) :
    comparisonHeightEnvelope 4 t τ ν ≤ Real.exp 2 *
      (1 + |t|) ^ (-2 : ℝ) * (1 + |τ|) ^ (-2 : ℝ) * (1 + |ν|) ^ (-2 : ℝ) := by
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
  have hw : (1+|τ|)^(-4 : ℝ) ≤ (1+|τ|)^(-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by have := abs_nonneg τ; linarith) (by norm_num)
  have hz : (1+|ν|)^(-4 : ℝ) = (1+|ν|)^(-2 : ℝ) * (1+|ν|)^(-2 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  unfold comparisonHeightEnvelope
  rw [hz, ← mul_assoc]
  calc
    _ ≤ (Real.exp 2 * (1+|t|)^(-2 : ℝ)) * (1+|ν|)^(-2 : ℝ) * (1+|τ|)^(-4 : ℝ) := by
      gcongr
    _ ≤ (Real.exp 2 * (1+|t|)^(-2 : ℝ)) * (1+|ν|)^(-2 : ℝ) * (1+|τ|)^(-2 : ℝ) := by
      gcongr
    _ = _ := by ring

private lemma weight_rapid (R : PrincipalMellin.ActualRecipe S η) :
    comparisonRapidStripDecay R.W.M comparisonZeta₁ comparisonZeta₁ ∧
    comparisonRapidStripDecay R.W.W1Hat (19/20) comparisonSigma₁ := by
  have hne : ∀ v, R.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := R.probe.finiteTrace_ne_one R.A R.σ R.target R.traceBad v
    exact hx (by rw [he]; rfl)
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F R.A
    R.probe.finiteTrace R.probe.continuousTrace R.probe.traceCompatible hne
    R.probe.additiveMeasure R.probe.multiplicativeMeasure
    R.probe.additiveHaar R.probe.multiplicativeHaar (Classical.choice inferInstance)
    R.probe.W0 R.probe.W1 R.probe.annular R.probe.compactSupport R.probe.supportUnits
  rcases hsheet with ⟨_, _, _, _, hMd, _, hWd, _⟩
  have rapid (f : ℂ → ℂ) (a b : ℝ)
      (h : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
        ‖f ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ C * (1 + |τ|) ^ (-B)) :
      comparisonRapidStripDecay f a b := by
    intro B hB
    obtain ⟨C, hC, hb⟩ := h B hB
    refine ⟨C+1, by linarith, ?_⟩
    intro s hs
    have hp := hb s.re hs s.im
    rw [Complex.re_add_im] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  constructor
  · apply rapid
    intro B hB
    exact hMd comparisonZeta₁ comparisonZeta₁ B
      (by norm_num [comparisonZeta₁, comparisonDelta]) le_rfl hB
  · apply rapid
    intro B hB
    exact hWd (19/20) comparisonSigma₁ B (by norm_num [comparisonSigma₁,comparisonDelta]) hB

private lemma weighted_decay (R : PrincipalMellin.ActualRecipe S η)
    (d : ℝ) (hd : 0 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ w z : ℂ, ξ.re = comparisonSigma₁ →
      z.re = comparisonZeta₁ → w ∈ comparisonClosedStrip (19/20) comparisonSigma₁ →
      ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ w z‖ * (2+|w.im|)^d ≤
        B * (1+|ξ.im|)^(-2 : ℝ) * (1+|z.im|)^(-2 : ℝ) * (1+|w.im|)^(-2 : ℝ) := by
  obtain ⟨B, hB, hb⟩ := comparisonGaussianMellinWeight_polynomial_bound R.W.M R.W.W1Hat
    comparisonSigma₁ comparisonSigma₁ (19/20) comparisonSigma₁ comparisonZeta₁ comparisonZeta₁
    4 d 0 le_rfl (by norm_num [comparisonSigma₁, comparisonDelta]) le_rfl
    (by norm_num [comparisonZeta₁, comparisonDelta]) (by norm_num) hd (by norm_num)
    (weight_rapid R).1 (weight_rapid R).2
  refine ⟨B*Real.exp 2, mul_pos hB (Real.exp_pos _), ?_⟩
  intro ξ w z hξ hz hw
  have h := hb ξ w z (by exact ⟨hξ.ge,hξ.le⟩) hw (by exact ⟨hz.ge,hz.le⟩)
  simp only [Real.rpow_zero, mul_one] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (envelope_bound ξ.im w.im z.im) hB.le).trans_eq (by ring))

private lemma scale_bound (Z : ℝ) (hZ : 1 ≤ Z) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ w z : ℂ, ξ.re = comparisonSigma₁ →
      z.re = comparisonZeta₁ → w ∈ comparisonClosedStrip (19/20) comparisonSigma₁ →
      ‖comparisonRealPower (comparisonX Z) (1/2-z)‖ *
        ‖comparisonRealPower Z (ξ+z-1)‖ *
        ‖comparisonRealPower (comparisonY Z) (w-1)‖ ≤ B := by
  let SX := Real.exp (Real.log (comparisonX Z))
  let SZ := Real.exp (7 * Real.log Z)
  let SY := Real.exp (4 * Real.log (comparisonY Z))
  have hX : 1 ≤ comparisonX Z := by
    unfold comparisonX; exact Real.one_le_rpow hZ (by norm_num [comparisonA])
  have hY : 1 ≤ comparisonY Z := by
    unfold comparisonY; exact Real.one_le_rpow hZ (by norm_num [comparisonB])
  have hlX := Real.log_nonneg hX
  have hlY := Real.log_nonneg hY
  have hlZ := Real.log_nonneg hZ
  refine ⟨SX*SZ*SY, by dsimp [SX,SZ,SY]; positivity, ?_⟩
  intro ξ w z hξ hz hw
  have hx : ‖comparisonRealPower (comparisonX Z) (1/2-z)‖ ≤ SX := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re]; norm_num
    norm_num [hz, comparisonZeta₁, comparisonDelta] at *
    nlinarith
  have hzz : ‖comparisonRealPower Z (ξ+z-1)‖ ≤ SZ := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    norm_num [hξ,hz,comparisonSigma₁,comparisonZeta₁,comparisonDelta] at *
    nlinarith
  have hy : ‖comparisonRealPower (comparisonY Z) (w-1)‖ ≤ SY := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re,Complex.one_re]
    have hh : w.re ≤ comparisonSigma₁ := hw.2
    norm_num [comparisonSigma₁,comparisonDelta] at hh
    nlinarith
  exact mul_le_mul (mul_le_mul hx hzz (norm_nonneg _) (by dsimp [SX]; positivity))
    hy (norm_nonneg _) (by dsimp [SX,SZ]; positivity)

private lemma row_decay (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (Z : ℝ) (hZ : 1 ≤ Z)
    (N : ℂ → ℂ) (BN d : ℝ) (hBN : 0 < BN) (hd : 0 ≤ d)
    (hN : ∀ w ∈ comparisonClosedStrip (19/20) comparisonSigma₁,
      ‖N w‖ ≤ BN * (2+|w.im|)^d) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ w z : ℂ, ξ.re = comparisonSigma₁ →
      z.re = comparisonZeta₁ → w ∈ comparisonClosedStrip (19/20) comparisonSigma₁ →
      ‖PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat R.L R.L N (correction R C U) ξ w z‖ ≤
        B * (1+|ξ.im|)^(-2 : ℝ) * (1+|z.im|)^(-2 : ℝ) * (1+|w.im|)^(-2 : ℝ) := by
  obtain ⟨BW,hBW,hweight⟩ := weighted_decay R d hd
  obtain ⟨BS,hBS,hscale⟩ := scale_bound Z hZ
  obtain ⟨BL,hBL,hL⟩ := PrincipalNumerator.rightHalfPlane_bound R (6*comparisonZeta₁)
    (by norm_num [comparisonZeta₁,comparisonDelta])
  obtain ⟨BI,hBI,hLI⟩ := PrincipalNumerator.rightHalfPlane_reciprocal_bound R comparisonSigma₁
    (by norm_num [comparisonSigma₁,comparisonDelta])
  obtain ⟨BH,hBH,hH⟩ := (ThreeVariableProduct.three_variable_product C).2.1 1 (by norm_num)
  let CH := BH * (R.A.exteriorNorm U.ideal)^(1 : ℝ)
  have hCH : 0 ≤ CH := mul_nonneg hBH.le (Real.rpow_nonneg (by
    simp [SArithmeticData.exteriorNorm,idealNorm]) _)
  refine ⟨BS*BW*BL*BN*BI*(CH+1), by positivity, ?_⟩
  intro ξ w z hξ hz hw
  have hh : ‖correction R C U ξ w z‖ ≤ CH+1 := by
    have hh := hH U (ξ,w,z) (wDomain_omega ξ z w hξ hz (wDomain_strip hw))
    change ‖correction R C U ξ w z‖ ≤ CH at hh
    linarith
  have hl : ‖R.L (6*z)‖ ≤ BL := hL _ (by simp [hz])
  have hi : ‖(R.L ξ)⁻¹‖ ≤ BI := hLI _ hξ.ge
  have heq : ‖PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat R.L R.L N (correction R C U) ξ w z‖ =
      (‖comparisonRealPower (comparisonX Z) (1/2-z)‖ *
        ‖comparisonRealPower Z (ξ+z-1)‖ * ‖comparisonRealPower (comparisonY Z) (w-1)‖) *
      ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ w z‖ *
      ‖R.L (6*z)‖ * ‖N w‖ * ‖(R.L ξ)⁻¹‖ * ‖correction R C U ξ w z‖ := by
    unfold PrincipalWShift.clearedKernel comparisonGaussianMellinWeight
    simp only [div_eq_mul_inv,norm_mul]; ring
  rw [heq]
  calc
    _ ≤ BS * ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ w z‖ * BL *
        (BN*(2+|w.im|)^d) * BI * (CH+1) := by
      gcongr
      · exact hscale ξ w z hξ hz hw
      · exact hN w hw
    _ = BS*BL*BN*BI*(CH+1) *
        (‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ w z‖ * (2+|w.im|)^d) := by ring
    _ ≤ BS*BL*BN*BI*(CH+1) * (BW*(1+|ξ.im|)^(-2 : ℝ)*
        (1+|z.im|)^(-2 : ℝ)*(1+|w.im|)^(-2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (hweight ξ w z hξ hz hw) (by positivity)
    _ = _ := by ring

private lemma tail_decay
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (Z : ℝ) (hZ : 1 ≤ Z) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ w z : ℂ, ξ.re = comparisonSigma₁ →
      z.re = comparisonZeta₁ → w ∈ comparisonClosedStrip (19/20) comparisonSigma₁ →
      1 ≤ |w.im| →
      ‖PrincipalWShift.kernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U) ξ w z‖ ≤
        B * (1+|ξ.im|)^(-2 : ℝ) * (1+|z.im|)^(-2 : ℝ) * (1+|w.im|)^(-2 : ℝ) := by
  obtain ⟨BN,d,hBN,hd,hN⟩ := PrincipalNumerator.stripRegularization_bound R
    (19/20) comparisonSigma₁ (by norm_num) (by norm_num [comparisonSigma₁,comparisonDelta])
    (by norm_num [comparisonSigma₁,comparisonDelta])
  obtain ⟨B,hB,hb⟩ := row_decay R C U Z hZ (regularization R) BN d hBN hd
    (fun w hw => hN w hw.1 hw.2)
  refine ⟨B,hB,?_⟩
  intro ξ w z hξ hz hw htail
  have hnorm : 1 ≤ ‖w-1‖ := by
    have h := Complex.abs_im_le_norm (w-1)
    simp only [Complex.sub_im,Complex.one_im,sub_zero] at h
    exact htail.trans h
  have hne : w ≠ 1 := by intro he; norm_num [he] at htail
  have hmul : PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat R.L R.L
      (regularization R) (correction R C U) ξ w z =
      (w-1) * PrincipalWShift.kernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U) ξ w z := by
    unfold PrincipalWShift.clearedKernel PrincipalWShift.kernel
    rw [w_regularization R w (wDomain_strip hw) hne]
    ring
  have hh := hb ξ w z hξ hz hw
  rw [hmul,norm_mul] at hh
  exact (le_mul_of_one_le_left (norm_nonneg _) hnorm).trans hh

private lemma L_holo_off (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ R.L {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  apply R.continuation.L_holo.mul
  apply DifferentiableOn.fun_finset_prod
  intro v hv
  exact ((((differentiable_id.neg).mul_const
    (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
      (R.target v.asIdeal)).differentiableOn.const_sub 1

 def vline (σ : ℝ) (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ)*I

private lemma vline_re (σ t : ℝ) : (vline σ t).re = σ := by simp [vline]
private lemma vline_im (σ t : ℝ) : (vline σ t).im = t := by simp [vline]
private lemma vline_cont (σ : ℝ) : Continuous (vline σ) := by unfold vline; fun_prop

private lemma L_line (R : PrincipalMellin.ActualRecipe S η)
    (σ : ℝ) (hσ : 0 < σ) (hne : σ ≠ 1) : Continuous (fun t => R.L (vline σ t)) := by
  apply (L_holo_off R).continuousOn.comp_continuous (vline_cont σ)
  intro t
  refine ⟨by simpa [vline_re] using hσ, ?_⟩
  intro he
  apply hne
  have hh := congrArg Complex.re he
  simpa [vline_re] using hh

private lemma row_measurable (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (Z σw : ℝ)
    (hσw : σw ∈ Set.Icc (19/20) comparisonSigma₁)
    (N : ℂ → ℂ) (hN : Measurable (fun t => N (vline σw t))) :
    Measurable (fun t : ℝ × ℝ × ℝ => PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat
      R.L R.L N (correction R C U) (vline comparisonSigma₁ t.1)
        (vline σw t.2.1) (vline comparisonZeta₁ t.2.2)) := by
  have hM : Continuous (fun t => R.W.M (vline comparisonZeta₁ t)) := by
    apply (ContinuationSteps.actual_mellin_weight_far_inputs R).1.continuousOn.comp_continuous
      (vline_cont comparisonZeta₁)
    intro t
    norm_num [vline_re,comparisonZeta₁,comparisonDelta]
  have hW : Continuous (fun t => R.W.W1Hat (vline σw t)) := by
    apply (ContinuationSteps.actual_mellin_weight_contour_inputs R).2.1.continuousOn.comp_continuous
      (vline_cont σw)
    intro t
    simp only [Set.mem_setOf_eq,vline_re]
    linarith [hσw.1]
  have hLξ := L_line R comparisonSigma₁ (by norm_num [comparisonSigma₁,comparisonDelta])
    (by norm_num [comparisonSigma₁,comparisonDelta])
  have hLz : Continuous (fun t => R.L (6*vline comparisonZeta₁ t)) := by
    have he : ∀ t : ℝ, 6*vline comparisonZeta₁ t = vline (6*comparisonZeta₁) (6*t) := by
      intro t
      simp only [vline,Complex.ofReal_mul,Complex.ofReal_ofNat]; ring
    simp_rw [he]
    exact (L_line R (6*comparisonZeta₁) (by norm_num [comparisonZeta₁,comparisonDelta])
      (by norm_num [comparisonZeta₁,comparisonDelta])).comp (by fun_prop)
  have hH : Continuous (fun t : ℝ × ℝ × ℝ => correction R C U
      (vline comparisonSigma₁ t.1) (vline σw t.2.1) (vline comparisonZeta₁ t.2.2)) := by
    have hc : ContinuousOn (fun x : ℂ × ℂ × ℂ => correction R C U x.1 x.2.1 x.2.2)
        CorrectionFactors.Omega := continuousOn_iff_continuous_restrict.mpr (CorrectionFactors.continuous_H_u C U)
    apply hc.comp_continuous (show Continuous (fun t : ℝ × ℝ × ℝ =>
        (vline comparisonSigma₁ t.1,vline σw t.2.1,vline comparisonZeta₁ t.2.2)) by
      unfold vline; fun_prop)
    intro t
    apply wDomain_omega _ _ _ (vline_re _ _) (vline_re _ _)
    apply wDomain_strip
    simpa only [comparisonClosedStrip,Set.mem_setOf_eq,vline_re,Set.mem_Icc] using hσw
  have hm : Measurable (fun t : ℝ × ℝ × ℝ => R.W.M (vline comparisonZeta₁ t.2.2)) := hM.measurable.comp (measurable_snd.comp measurable_snd)
  have hw : Measurable (fun t : ℝ × ℝ × ℝ => R.W.W1Hat (vline σw t.2.1)) := hW.measurable.comp (measurable_fst.comp measurable_snd)
  have hn : Measurable (fun t : ℝ × ℝ × ℝ => N (vline σw t.2.1)) := hN.comp (measurable_fst.comp measurable_snd)
  have hlx : Measurable (fun t : ℝ × ℝ × ℝ => R.L (vline comparisonSigma₁ t.1)) := hLξ.measurable.comp measurable_fst
  have hlz : Measurable (fun t : ℝ × ℝ × ℝ => R.L (6*vline comparisonZeta₁ t.2.2)) := hLz.measurable.comp (measurable_snd.comp measurable_snd)
  unfold PrincipalWShift.clearedKernel comparisonRealPower
  exact ((((((by unfold vline; fun_prop : Measurable (fun t : ℝ × ℝ × ℝ =>
    cexp ((1/2-vline comparisonZeta₁ t.2.2)* ↑(Real.log (comparisonX Z))) *
    cexp ((vline comparisonSigma₁ t.1+vline comparisonZeta₁ t.2.2-1)* ↑(Real.log Z)) *
    cexp ((vline σw t.2.1-1)* ↑(Real.log (comparisonY Z))) *
    cexp ((vline comparisonSigma₁ t.1+vline comparisonZeta₁ t.2.2-1)^2)))).mul hm).mul hw).mul
      ((hlz.mul hn).div hlx)).mul hH.measurable)

 def decayHeight (t : ℝ) : ℝ := (1+|t|)^(-2 : ℝ)

private lemma decayHeight_integrable : Integrable decayHeight := by
  change Integrable (fun t : ℝ => (1+|t|)^(-(2:ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp))

private lemma row_integrable (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (Z σw : ℝ)
    (hσw : σw ∈ Set.Icc (19/20) comparisonSigma₁)
    (N : ℂ → ℂ) (hN : Measurable (fun t => N (vline σw t)))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ ξ w z : ℂ, ξ.re = comparisonSigma₁ → z.re = comparisonZeta₁ →
      w.re = σw → ‖PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat R.L R.L N
        (correction R C U) ξ w z‖ ≤
        B * (1+|ξ.im|)^(-2 : ℝ) * (1+|z.im|)^(-2 : ℝ) * (1+|w.im|)^(-2 : ℝ)) :
    Integrable (fun t : ℝ × ℝ × ℝ => PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat
      R.L R.L N (correction R C U) (vline comparisonSigma₁ t.1)
        (vline σw t.2.1) (vline comparisonZeta₁ t.2.2)) := by
  have hg := (decayHeight_integrable.mul_prod
    (decayHeight_integrable.mul_prod decayHeight_integrable)).const_mul B
  apply hg.mono' (row_measurable R C U Z σw hσw N hN).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have h := hb (vline comparisonSigma₁ t.1) (vline σw t.2.1)
    (vline comparisonZeta₁ t.2.2) (vline_re _ _) (vline_re _ _) (vline_re _ _)
  simp only [vline_im] at h
  exact h.trans_eq (by dsimp [decayHeight]; ring)

theorem w_contour
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1)
    (Z : ℝ) (hZ : 1 ≤ Z) :
    Nonempty (PrincipalZShift.WContourConditions Z R.W.M R.W.W1Hat R.L R.L
      (regularization R) (correction R C U)) := by
  obtain ⟨BN,d,hBN,hd,hN⟩ := PrincipalNumerator.stripRegularization_bound R
    (19/20) comparisonSigma₁ (by norm_num) (by norm_num [comparisonSigma₁,comparisonDelta])
    (by norm_num [comparisonSigma₁,comparisonDelta])
  obtain ⟨BR,hBR,hrow⟩ := row_decay R C U Z hZ (regularization R) BN d hBN hd
    (fun w hw => hN w hw.1 hw.2)
  obtain ⟨BT,hBT,htail⟩ := tail_decay R C U Z hZ
  refine ⟨{ U := wDomain
            C := BT
            C_nonneg := hBT.le
            open_U := wDomain_open
            strip := wDomain_strip
            regularization := w_regularization R
            holomorphic := w_cleared_holo R C U Z
            decay := htail
            endpoints := ?_
            residue := ?_ }⟩
  · intro σw hσw
    have hlines : σw = 19/20 ∨ σw = comparisonSigma₁ := by simpa using hσw
    have hσ : σw ∈ Set.Icc (19/20) comparisonSigma₁ := by
      rcases hlines with h | h <;> rw [h] <;>
        norm_num [comparisonSigma₁,comparisonDelta]
    have hpos : 0 < σw := by linarith [hσ.1]
    have hne : σw ≠ 1 := by
      rcases hlines with h | h <;> norm_num [h,comparisonSigma₁,comparisonDelta]
    have hdist : ∀ w : ℂ, w.re = σw → 1/20000000 ≤ ‖w-1‖ := by
      intro w hw
      have hh := Complex.abs_re_le_norm (w-1)
      simp only [Complex.sub_re,Complex.one_re,hw] at hh
      rcases hlines with h | h <;> norm_num [h,comparisonSigma₁,comparisonDelta] at hh ⊢ <;>
        linarith
    have hm : Measurable (fun t => R.L (vline σw t)) := (L_line R σw hpos hne).measurable
    have hi := row_integrable R C U Z σw hσ R.L hm (20000000*BR) (by positivity) ?_
    · simpa only [PrincipalWShift.clearedKernel,PrincipalWShift.kernel,vline] using hi
    · intro ξ w z hξ hz hw
      have hs : w ∈ comparisonClosedStrip (19/20) comparisonSigma₁ := by
        simpa only [comparisonClosedStrip,Set.mem_setOf_eq,hw,Set.mem_Icc] using hσ
      have hne' : w ≠ 1 := by intro he; apply hne; simpa [he] using hw.symm
      have heq : PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat R.L R.L
          (regularization R) (correction R C U) ξ w z =
          (w-1) * PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat R.L R.L
            R.L (correction R C U) ξ w z := by
        unfold PrincipalWShift.clearedKernel
        rw [w_regularization R w (wDomain_strip hs) hne']
        ring
      have hh := hrow ξ w z hξ hz hs
      rw [heq,norm_mul] at hh
      have hh' := hdist w hw
      have hn := norm_nonneg (PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat
        R.L R.L R.L (correction R C U) ξ w z)
      have hh'' : ‖PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat
          R.L R.L R.L (correction R C U) ξ w z‖ ≤
          20000000 * (BR * (1+|ξ.im|)^(-2 : ℝ) *
            (1+|z.im|)^(-2 : ℝ) * (1+|w.im|)^(-2 : ℝ)) := by nlinarith
      exact hh''.trans_eq (by ring)
  · have hs : (1 : ℝ) ∈ Set.Icc (19/20) comparisonSigma₁ := by
      norm_num [comparisonSigma₁,comparisonDelta]
    obtain ⟨B,hB,hb⟩ := row_decay R C U Z hZ (fun _ => 1) 1 0 (by norm_num) (by norm_num)
      (by intro w hw; simp)
    have heq : ∀ ξ z : ℂ,
        PrincipalWShift.clearedKernel Z R.W.M R.W.W1Hat R.L R.L (fun _ => 1)
          (correction R C U) ξ 1 z =
        PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U) ξ z := by
      intro ξ z
      simp [PrincipalWShift.clearedKernel,PrincipalWShift.residueKernel,comparisonRealPower]
    have hm := (row_measurable R C U Z 1 hs (fun _ => 1) measurable_const).comp
      (show Measurable (fun t : ℝ × ℝ => (t.1,(0 : ℝ),t.2)) by fun_prop)
    have hm' : Measurable (fun t : ℝ × ℝ => PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat
        R.L R.L (correction R C U) (vline comparisonSigma₁ t.1) (vline comparisonZeta₁ t.2)) := by
      simpa only [Function.comp_def,vline,Complex.ofReal_zero,zero_mul,add_zero,Complex.ofReal_one,heq] using hm
    have hg := (decayHeight_integrable.mul_prod decayHeight_integrable).const_mul B
    have hi : Integrable (fun t : ℝ × ℝ => PrincipalWShift.residueKernel Z R.W.M R.W.W1Hat
        R.L R.L (correction R C U) (vline comparisonSigma₁ t.1) (vline comparisonZeta₁ t.2)) := by
      apply hg.mono' hm'.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro t
      have hh := hb (vline comparisonSigma₁ t.1) 1 (vline comparisonZeta₁ t.2)
        (vline_re _ _) (vline_re _ _) (by simpa only [comparisonClosedStrip,Set.mem_setOf_eq,
          Complex.one_re,Set.mem_Icc] using hs)
      rw [heq] at hh
      simpa [vline_im,decayHeight,mul_assoc] using hh
    simpa only [vline] using hi

end
end DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
