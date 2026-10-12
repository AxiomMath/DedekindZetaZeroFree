module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalInitialEulerSeparation
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalProductSpectralProperties

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
private theorem L_holo (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ R.L {s : ℂ | 1 < s.re} := by
  have hP := R.continuation.L_holo.mono (show {s : ℂ | 1 < s.re} ⊆
      {s : ℂ | 0 < s.re ∧ s ≠ 1} from fun s hs => ⟨by
        dsimp at hs ⊢; linarith, by intro h; simp [h] at hs⟩)
  apply hP.mul
  apply DifferentiableOn.fun_finset_prod
  intro v hv
  exact ((((differentiable_id.neg).mul_const
    (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
      (R.target v.asIdeal)).differentiableOn.const_sub 1
private theorem fullL_exp (R : PrincipalMellin.ActualRecipe S η)
    (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (HeckeLogProof.eulerLog
      (fun I : ExteriorIdeal (⊤ : Ideal (NumberField.RingOfIntegers F)) => R.target I.val) s) =
      R.continuation.L s := by
  rw [HeckeLogProof.exp_eulerLog _
    (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target) s hs]
  have hsupport : Function.support (fun I : Ideal (NumberField.RingOfIntegers F) =>
      R.target I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (NumberField.RingOfIntegers F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
    intro I hI
    refine ⟨?_, by simp⟩
    intro hzero
    have hη : R.target I = 0 := (R.target.eq_zero_iff' I).mpr (Or.inl hzero)
    exact hI (by simpa only [hη, zero_mul])
  exact ((hasSum_subtype_iff_of_support_subset hsupport).mpr
    (R.continuation.series s hs)).tsum_eq
private theorem L_bounds (R : PrincipalMellin.ActualRecipe S η) (a : ℝ) (ha : 1 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → ‖R.L s‖ ≤ B ∧ ‖(R.L s)⁻¹‖ ≤ B := by
  let M := Real.exp ((3 / 2 : ℝ) *
    ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a))
  have hM : 0 < M := Real.exp_pos _
  have hfull (s : ℂ) (hs : a ≤ s.re) :
      ‖R.continuation.L s‖ ≤ M ∧ ‖(R.continuation.L s)⁻¹‖ ≤ M := by
    rw [← fullL_exp R s (ha.trans_le hs), ← Complex.exp_neg]
    have h := HeckeLogProof.eulerLog_norm_le
      (fun I : ExteriorIdeal (⊤ : Ideal (NumberField.RingOfIntegers F)) => R.target I.val)
      (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target) a ha s hs
    constructor
    · rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      exact (Complex.re_le_norm _).trans h
    · rw [Complex.norm_exp, Complex.neg_re]; apply Real.exp_le_exp.mpr
      exact ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans h
  let u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℝ := fun v =>
    (1 - Real.exp (-a * Real.log (idealNorm v.asIdeal)))⁻¹
  have hupos (v) : 0 < u v := by
    have hQ : 1 < idealNorm v.asIdeal := by
      dsimp [idealNorm]
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hlog := Real.log_pos hQ
    dsimp [u]; apply inv_pos.mpr; apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]; nlinarith
  have hlocal (s : ℂ) (hs : a ≤ s.re) (v) :
      ‖1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 2 ∧
      ‖(1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))⁻¹‖ ≤ u v := by
    have hQ : 1 < idealNorm v.asIdeal := by
      dsimp [idealNorm]
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hlog := Real.log_pos hQ
    have hpow : ‖R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤
        Real.exp (-a * Real.log (idealNorm v.asIdeal)) := by
      rw [norm_mul]
      have hn := RayUnitary.ray_character_norm_le_one F R.A.modulus
        R.A.modulus_ne_zero R.target v.asIdeal
      calc
        _ ≤ 1 * ‖comparisonRealPower (idealNorm v.asIdeal) (-s)‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        _ = Real.exp (-s.re * Real.log (idealNorm v.asIdeal)) := by
          rw [one_mul, MellinZeroFree.norm_comparisonRealPower, Complex.neg_re]
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
    constructor
    · have h := norm_sub_le (1 : ℂ)
        (R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))
      rw [norm_one] at h
      have he : Real.exp (-a * Real.log (idealNorm v.asIdeal)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      linarith
    · rw [norm_inv]
      apply inv_anti₀ (inv_pos.mp (hupos v))
      have ht := norm_sub_norm_le (1 : ℂ)
        (R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))
      rw [norm_one] at ht
      dsimp [u] at *
      linarith
  let B1 : ℝ := M * ∏ v ∈ R.A.Sf, (2 : ℝ)
  let B2 : ℝ := M * ∏ v ∈ R.A.Sf, u v
  have hB1 : 0 < B1 := mul_pos hM (Finset.prod_pos (by intros; norm_num))
  have hB2 : 0 < B2 := mul_pos hM (Finset.prod_pos (fun v _ => hupos v))
  refine ⟨B1 + B2, by positivity, ?_⟩
  intro s hs
  have hb1 : ‖R.L s‖ ≤ B1 := by
    change ‖R.continuation.L s * ∏ v ∈ R.A.Sf,
      (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖ ≤ _
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hfull s hs).1
      (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => (hlocal s hs v).1))
      (by positivity) hM.le
  have hb2 : ‖(R.L s)⁻¹‖ ≤ B2 := by
    change ‖(R.continuation.L s * ∏ v ∈ R.A.Sf,
      (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)))⁻¹‖ ≤ _
    rw [mul_inv, norm_mul, ← Finset.prod_inv_distrib, norm_prod]
    exact mul_le_mul (hfull s hs).2
      (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => (hlocal s hs v).2))
      (by positivity) hM.le
  exact ⟨by linarith, by linarith⟩
 def box (a : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {x | a < x.1.re ∧ x.1.re < 5 ∧ a < x.2.1.re ∧ x.2.1.re < 5 ∧
    a / 6 < x.2.2.re ∧ x.2.2.re < 3}
private theorem box_omega (a : ℝ) (ha : 1 < a) : box a ⊆ CorrectionFactors.Omega := by
  intro x hx
  apply Or.inr
  dsimp [box, CorrectionFactors.omegaSecond] at *
  refine ⟨by linarith [hx.1], by linarith [hx.2.2.1], by linarith [hx.2.2.2.2.1]⟩
private theorem kernel_holo
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (Z a : ℝ) (ha : 1 < a) :
    MeromorphicSeparationGluing.SeparatelyHolomorphicOn
      (fun x => PrincipalWShift.kernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U)
        x.1 x.2.1 x.2.2) (box a) := by
  have hH := ((ThreeVariableProduct.three_variable_product C).1 U).2.2.2
  have hL := L_holo R
  have hLzero := (PrincipalMellin.actual_principal_spectral_properties S η R).2.2.2.2
  have hne : ∀ v, R.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := R.probe.finiteTrace_ne_one R.A R.σ R.target R.traceBad v
    exact hx (by rw [he]; rfl)
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F R.A
    R.probe.finiteTrace R.probe.continuousTrace R.probe.traceCompatible hne
    R.probe.additiveMeasure R.probe.multiplicativeMeasure
    R.probe.additiveHaar R.probe.multiplicativeHaar (Classical.choice inferInstance)
    R.probe.W0 R.probe.W1 R.probe.annular R.probe.compactSupport R.probe.supportUnits
  rcases hsheet with ⟨_, _, _, hM, _, hW, _, _⟩
  change DifferentiableOn ℂ R.W.M {z : ℂ | 0 < z.re} at hM
  change Differentiable ℂ R.W.W1Hat at hW
  constructor
  · intro w z
    have hHx := (hH.1 w z).mono (fun ξ hx => box_omega a ha hx)
    change DifferentiableOn ℂ (fun ξ => correction R C U ξ w z) _ at hHx
    have hLx := hL.mono (show {ξ : ℂ | (ξ, w, z) ∈ box a} ⊆ {s | 1 < s.re} from
      fun ξ hx => ha.trans hx.1)
    dsimp only
    unfold PrincipalWShift.kernel comparisonRealPower
    apply DifferentiableOn.mul _ hHx
    apply DifferentiableOn.mul
    · apply Differentiable.differentiableOn
      fun_prop
    · exact (differentiableOn_const _).div hLx
        (fun ξ hx => hLzero ξ (ha.trans hx.1))
  constructor
  · intro ξ z
    have hHw := (hH.2.1 ξ z).mono (fun w hx => box_omega a ha hx)
    change DifferentiableOn ℂ (fun w => correction R C U ξ w z) _ at hHw
    have hLw := hL.mono (show {w : ℂ | (ξ, w, z) ∈ box a} ⊆ {s | 1 < s.re} from
      fun w hx => ha.trans hx.2.2.1)
    dsimp only
    unfold PrincipalWShift.kernel comparisonRealPower
    apply DifferentiableOn.mul _ hHw
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul _ hW.differentiableOn
      apply Differentiable.differentiableOn
      fun_prop
    · exact (hLw.const_mul _).div_const _
  · intro ξ w
    have hHz := (hH.2.2 ξ w).mono (fun z hx => box_omega a ha hx)
    change DifferentiableOn ℂ (fun z => correction R C U ξ w z) _ at hHz
    have hMz := hM.mono (show {z : ℂ | (ξ, w, z) ∈ box a} ⊆ {s | 0 < s.re} from
      fun z hx => by dsimp [box] at hx; dsimp; linarith [hx.2.2.2.2.1])
    have hLz : DifferentiableOn ℂ (fun z => R.L (6 * z)) {z | (ξ,w,z) ∈ box a} :=
      hL.comp (by fun_prop) (by
        intro z hz
        simp only [Set.mem_setOf_eq, Complex.mul_re]
        norm_num
        dsimp [box] at hz
        linarith [hz.2.2.2.2.1])
    dsimp only
    unfold PrincipalWShift.kernel comparisonRealPower
    apply DifferentiableOn.mul _ hHz
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul _ (differentiableOn_const _)
      apply DifferentiableOn.mul _ hMz
      apply Differentiable.differentiableOn
      fun_prop
    · exact (hLz.mul_const _).div_const _
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
private theorem weight_decay (R : PrincipalMellin.ActualRecipe S η)
    (a : ℝ) (ha : 1 < a) (ha5 : a < 5) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ w z : ℂ, (ξ,w,z) ∈ box a →
      ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ w z‖ ≤
        B * (1 + |ξ.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ) * (1 + |z.im|) ^ (-2 : ℝ) := by
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
  have rapid (f : ℂ → ℂ) (c d : ℝ)
      (h : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc c d, ∀ τ : ℝ,
        ‖f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B)) :
      comparisonRapidStripDecay f c d := by
    intro B hB
    obtain ⟨C, hC, hb⟩ := h B hB
    refine ⟨C + 1, by linarith, ?_⟩
    intro s hs
    have hp := hb s.re hs s.im
    rw [Complex.re_add_im] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hM : comparisonRapidStripDecay R.W.M (a/6) 3 := by
    apply rapid
    intro B hB
    exact hMd (a/6) 3 B (by linarith) (by linarith) hB
  have hW : comparisonRapidStripDecay R.W.W1Hat a 5 := by
    apply rapid
    intro B hB
    exact hWd a 5 B (by linarith) hB
  obtain ⟨B, hB, hb⟩ := comparisonGaussianMellinWeight_polynomial_bound R.W.M R.W.W1Hat
    a 5 a 5 (a/6) 3 4 0 0 (by linarith) (by linarith) (by linarith)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) hM hW
  refine ⟨B * Real.exp 2, mul_pos hB (Real.exp_pos _), ?_⟩
  intro ξ w z hx
  have hh := hb ξ w z ⟨hx.1.le, hx.2.1.le⟩ ⟨hx.2.2.1.le, hx.2.2.2.1.le⟩
    ⟨hx.2.2.2.2.1.le, hx.2.2.2.2.2.le⟩
  simp only [Real.rpow_zero, mul_one] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (envelope_bound ξ.im w.im z.im) hB.le).trans_eq (by ring))
private theorem kernel_decay
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : CorrectionFactors.Frequency C) (Z a : ℝ) (ha : 1 < a) (ha5 : a < 5) (hZ : 1 ≤ Z) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ w z : ℂ, (ξ,w,z) ∈ box a →
      ‖PrincipalWShift.kernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U) ξ w z‖ ≤
        B * (1 + |ξ.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ) * (1 + |z.im|) ^ (-2 : ℝ) := by
  obtain ⟨BW, hBW, hweight⟩ := weight_decay R a ha ha5
  obtain ⟨BL, hBL, hL⟩ := L_bounds R a ha
  obtain ⟨BH, hBH, hbH⟩ := (ThreeVariableProduct.three_variable_product C).2.1 1 (by norm_num)
  let CH := BH * (R.A.exteriorNorm U.ideal) ^ (1 : ℝ)
  have hCH : 0 ≤ CH := mul_nonneg hBH.le (Real.rpow_nonneg (by
    simp [SArithmeticData.exteriorNorm, idealNorm]) _)
  let SX := Real.exp (1 / 2 * Real.log (comparisonX Z))
  let SZ := Real.exp (7 * Real.log Z)
  let SY := Real.exp (4 * Real.log (comparisonY Z))
  have hX : 1 ≤ comparisonX Z := by
    unfold comparisonX; exact Real.one_le_rpow hZ (by norm_num [comparisonA])
  have hY : 1 ≤ comparisonY Z := by
    unfold comparisonY; exact Real.one_le_rpow hZ (by norm_num [comparisonB])
  have hlX := Real.log_nonneg hX
  have hlY := Real.log_nonneg hY
  have hlZ := Real.log_nonneg hZ
  refine ⟨SX * SZ * SY * BW * (BL * BL * BL) * (CH + 1), by
    dsimp [SX, SZ, SY]; positivity, ?_⟩
  intro ξ w z hx
  have hx' := hx
  dsimp [box] at hx'
  have hsX : ‖comparisonRealPower (comparisonX Z) (1/2-z)‖ ≤ SX := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re]
    norm_num
    nlinarith [hx'.2.2.2.2.1]
  have hsZ : ‖comparisonRealPower Z (ξ+z-1)‖ ≤ SZ := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    nlinarith [hx'.2.1, hx'.2.2.2.2.2]
  have hsY : ‖comparisonRealPower (comparisonY Z) (w-1)‖ ≤ SY := by
    rw [MellinZeroFree.norm_comparisonRealPower]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re, Complex.one_re]
    nlinarith [hx'.2.2.2.1]
  have hHz : ‖correction R C U ξ w z‖ ≤ CH + 1 := by
    have h := hbH U (ξ,w,z) (box_omega a ha hx)
    change ‖correction R C U ξ w z‖ ≤ CH at h
    linarith
  have hrow : ‖R.L (6*z) * R.L w / R.L ξ‖ ≤ BL * BL * BL := by
    have hz : a ≤ (6*z).re := by
      simp only [Complex.mul_re]; norm_num; linarith [hx'.2.2.2.2.1]
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hL _ hz).1 (hL _ hx'.2.2.1.le).1
      (norm_nonneg _) hBL.le) (hL _ hx'.1.le).2 (norm_nonneg _) (by positivity)
  have heq : ‖PrincipalWShift.kernel Z R.W.M R.W.W1Hat R.L R.L (correction R C U) ξ w z‖ =
      ‖comparisonRealPower (comparisonX Z) (1/2-z)‖ *
      ‖comparisonRealPower Z (ξ+z-1)‖ * ‖comparisonRealPower (comparisonY Z) (w-1)‖ *
      ‖comparisonGaussianMellinWeight R.W.M R.W.W1Hat ξ w z‖ *
      ‖R.L (6*z) * R.L w / R.L ξ‖ * ‖correction R C U ξ w z‖ := by
    unfold PrincipalWShift.kernel comparisonGaussianMellinWeight
    simp only [norm_mul]; ring
  rw [heq]
  calc
    _ ≤ SX * SZ * SY *
        (BW * (1 + |ξ.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ) * (1 + |z.im|) ^ (-2 : ℝ)) *
        (BL * BL * BL) * (CH + 1) := by
      gcongr
      exact hweight ξ w z hx
    _ = _ := by ring

theorem initial_contour
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : CorrectionFactors.Frequency C) (hU : U.u = 1)
    (Z : ℝ) (hZ : 1 ≤ Z) :
    Nonempty (PrincipalZShift.InitialContourConditions Z R.W.M R.W.W1Hat R.L R.L
      (correction R C U)) := by
  let a : ℝ := 1 + comparisonDelta / 2
  have ha : 1 < a := by norm_num [a, comparisonDelta]
  have ha5 : a < 5 := by norm_num [a, comparisonDelta]
  obtain ⟨B, hB, hb⟩ := kernel_decay R C U Z a ha ha5 hZ
  have hh := kernel_holo R C U Z a ha
  refine ⟨{ U := box a
            C := B
            C_nonneg := hB.le
            open_U := ?_
            corridor := ?_
            holomorphic_xi := hh.1
            holomorphic_w := hh.2.1
            holomorphic_z := hh.2.2
            decay := hb }⟩
  · unfold box
    have hi (f : ℂ × ℂ × ℂ → ℝ) (hf : Continuous f) (c : ℝ) :
        IsOpen {x | c < f x} := isOpen_lt continuous_const hf
    have hj (f : ℂ × ℂ × ℂ → ℝ) (hf : Continuous f) (c : ℝ) :
        IsOpen {x | f x < c} := isOpen_lt hf continuous_const
    exact (hi (fun x => x.1.re) (by fun_prop) a).inter
      ((hj (fun x => x.1.re) (by fun_prop) 5).inter
      ((hi (fun x => x.2.1.re) (by fun_prop) a).inter
      ((hj (fun x => x.2.1.re) (by fun_prop) 5).inter
      ((hi (fun x => x.2.2.re) (by fun_prop) (a/6)).inter
        (hj (fun x => x.2.2.re) (by fun_prop) 3)))))
  · intro ξ w z hξ hw hz
    dsimp [box]
    simp only [Set.mem_Icc] at hξ hw hz
    dsimp [a, comparisonSigma₁, comparisonZeta₁, comparisonDelta] at *
    constructor; · linarith [hξ.1]
    constructor; · linarith [hξ.2]
    constructor; · linarith [hw.1]
    constructor; · linarith [hw.2]
    constructor; · linarith [hz.1]
    linarith [hz.2]
end
end DedekindZetaZeroFree.PrincipalMellinComparison.PrincipalResidueInputs
