module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalInitialContourRegularity
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalFirstPoleContour
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalResidueKernelContourBounds
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalContourRemainderDecomposition
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalResidueNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison

open Filter Asymptotics

noncomputable section
open scoped Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

@[simp] theorem frequencyNorm_principalFrequency
    (R : PrincipalMellin.ActualRecipe S η) :
    frequencyNorm R (principalFrequency R) = 1 := by
  simp only [frequencyNorm, principalFrequency, FiniteTransform.exteriorNorm,
    FiniteTransform.Residue, Ideal.span_singleton_one]
  haveI : Subsingleton (R.A.R.toSubring ⧸ (⊤ : Ideal R.A.R.toSubring)) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  simp

theorem principalInitialIntegral_eq_J_of_initial_euler
    (R : PrincipalMellin.ActualRecipe S η)
    (H : ℂ → ℂ → ℂ → ℂ)
    (hEuler : ∀ ξ w z : ℂ, ξ.re = 4 → w.re = 4 → z.re = 2 →
      separatedSeries R (principalFrequency R) ξ w z =
        (R.L (6 * z) * R.L w / R.L ξ) * H ξ w z)
    (Z : ℝ) (hZ : 0 < Z) :
    principalInitialIntegral R Z =
      PrincipalWShift.J Z R.W.M R.W.W1Hat R.L R.L H 4 4 2 := by
  unfold principalInitialIntegral initialFrequencyIntegral
    comparisonFrequencyIntegral PrincipalWShift.J comparisonTripleVerticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Finset.sum_singleton]
  rw [comparisonFrequencyKernel, frequencyNorm_principalFrequency,
    hEuler _ _ _ (by simp) (by simp) (by simp)]
  have hpower (ξ w z : ℂ) :
      comparisonRealPower (comparisonX Z) (1 / 2 - z) *
        comparisonRealPower Z (ξ + z - 1) *
        comparisonRealPower (comparisonY Z) (w - 1) =
      comparisonRealPower Z ((comparisonA : ℂ) / 2 + ξ - 1 +
        (comparisonH₀ : ℂ) * z + (comparisonB : ℂ) * (w - 1)) := by
    unfold comparisonRealPower comparisonX comparisonY
    rw [Real.log_rpow hZ, Real.log_rpow hZ]
    simp only [Complex.ofReal_mul]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    norm_num [comparisonA, comparisonB, comparisonH₀]
    ring
  rw [PrincipalWShift.kernel, hpower]
  simp only [comparisonRealPower, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one]
  ring

def principalRegularization (R : PrincipalMellin.ActualRecipe S η) (s : ℂ) : ℂ :=
  R.continuation.R s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))

@[simp] theorem principalRegularization_at_one
    (R : PrincipalMellin.ActualRecipe S η) :
    principalRegularization R 1 =
      comparisonPrincipalResidue F R.A R.target R.probe.principal R.continuation := rfl

theorem principal_coefficient_field_trace
    (R : PrincipalMellin.ActualRecipe S η) (x : F) :
    R.probe.coefficients.additiveCharacter x = (R.A.fieldTraceCharacter x : ℂ) := by
  rw [R.probe.sameTrace, PrincipalProbeConstruction.Inputs.fieldTrace_phase]
  congr 1
  funext v
  exact R.normalization.sameFiniteTrace v

def principalArithmeticContext (R : PrincipalMellin.ActualRecipe S η) :
    R.A.GeneralArithmeticContext R.σ R.target R.traceBad := by
  let A := R.A
  let D := R.probe.correction
  letI : Subsingleton (ClassGroup A.R) := R.classKilled
  have hl := ArithmeticContext.actual_hilbert_lagrangian_properties
    A R.classKilled D.H D.B D.H_actual D.B_complement
  exact {
    principal := A.principalIdealRing_of_classGroup_subsingleton R.classKilled
    classGroup_trivial := R.classKilled
    fractional_principal := fun I hI => exists_unit_of_isPrincipal I
      (ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI) hI.ne_zero
    unit_injective := A.unitQuotientClass_injective R.classKilled
    unit_image := A.unitQuotientClass_range
    correction := D
    units_lagrangian := hl.1
    primary_two := hl.2.1
    primary_three := hl.2.2
    reciprocity := ArithmeticContext.actual_hilbert_sextic_reciprocity
      A D.H D.B D.H_actual D.B_complement
    allowed_integral := fun I =>
      A.exists_allowed_integral_generator R.classKilled D.H D.B D.B_complement I
    allowed_unique := fun I a b ha hb =>
      A.allowed_generator_unique_mod_sixth R.classKilled D.H D.B D.B_complement I a b ha hb
    normOne_compact := ArithmeticContext.normOne_sixth_unit_quotient_compact A
    prime_target := fun I v hIv p hp a ha hap x hx =>
      D.prime_theta I v hIv p hp a ha hap x hx }

theorem principal_arithmetic_binding (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    PrincipalProbeConstruction.ArithmeticBinding R.A R.σ R.target R.traceBad
      C R.probe.allowed R.probe.coefficients := by
  refine ⟨R.probe.sameComplement.trans (congrArg (fun D => D.B) hC),
    R.probe.sameGenerator, R.probe.exteriorCharacters, ?_, R.probe.gammaTwo_recipe,
    R.probe.sixthUnitCharacters, principal_coefficient_field_trace R, ?_⟩
  · intro m
    rw [R.probe.theta_principal, hC]
  · intro x
    rw [principal_coefficient_field_trace R,
      PrincipalProbeConstruction.Inputs.fieldTrace_phase]

theorem principal_arithmetic_compatibility (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    WeightedFiniteCoefficient.ArithmeticCompatibility R.A R.probe.coefficients
      R.σ R.target R.traceBad C.correction := by
  exact PrincipalCorrection.probe_arithmetic_compatibility C R.probe hC
    (principal_arithmetic_binding R C hC)

theorem principal_actual_arithmetic_compatibility
    (R : PrincipalMellin.ActualRecipe S η) :
    WeightedFiniteCoefficient.ArithmeticCompatibility R.A R.probe.coefficients
      R.σ R.target R.traceBad (principalArithmeticContext R).correction := by
  exact principal_arithmetic_compatibility R (principalArithmeticContext R) rfl

def principalEulerFrequency (R : PrincipalMellin.ActualRecipe S η) :
    CorrectionFactors.Frequency (principalArithmeticContext R) where
  u := 1
  ideal := ⟨⊤, top_ne_bot, by simp⟩
  generates := by
    constructor
    · exact one_ne_zero
    · simp [SArithmeticData.extendIdeal, Ideal.map_top]
  allowed := by
    convert (principalArithmeticContext R).correction.B.one_mem using 1
    simp [SArithmeticData.IsAllowed]
  sixthFree := by
    intro p
    simp only [idealPrimeExponent]
    have ht : UniqueFactorizationMonoid.normalizedFactors
        (⊤ : Ideal (NumberField.RingOfIntegers F)) = 0 :=
      by simpa only [Ideal.one_eq_top] using
        (UniqueFactorizationMonoid.normalizedFactors_one
          (α := Ideal (NumberField.RingOfIntegers F)))
    rw [ht]
    simp

def principalContourCorrection (R : PrincipalMellin.ActualRecipe S η) (ξ w z : ℂ) : ℂ :=
  ∏' p : LocalFiniteSums.ExteriorPrime R.A,
    CorrectionFactors.localFactor (principalArithmeticContext R) (principalEulerFrequency R)
      p ξ w z

theorem principalContourCorrection_bound (R : PrincipalMellin.ActualRecipe S η) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ w z : ℂ, (ξ, w, z) ∈ CorrectionFactors.Omega →
      ‖principalContourCorrection R ξ w z‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ :=
    (ThreeVariableProduct.three_variable_product (principalArithmeticContext R)).2.1 1
      (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro ξ w z hx
  have h := hb (principalEulerFrequency R) (ξ, w, z) hx
  simpa [principalContourCorrection, CorrectionFactors.H_u, principalEulerFrequency,
    SArithmeticData.exteriorNorm, idealNorm] using h

theorem principalContourCorrection_error_bound (R : PrincipalMellin.ActualRecipe S η) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ w z : ℂ, ξ.re = comparisonSigma₁ →
      ((w.re = 19 / 20 ∧ z.re = comparisonZeta₁) ∨
        (w = 1 ∧ z.re = PrincipalZShift.zLine)) → ‖principalContourCorrection R ξ w z‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := principalContourCorrection_bound R
  refine ⟨B, hB, ?_⟩
  intro ξ w z hξ hwz
  apply hb
  apply Or.inr
  rcases hwz with ⟨hw, hz⟩ | ⟨rfl, hz⟩ <;>
    norm_num [CorrectionFactors.omegaSecond, hξ, hz, comparisonSigma₁,
      comparisonDelta, comparisonZeta₁, PrincipalZShift.zLine] at *
  linarith

theorem principalContourCorrection_principal_specialization (R : PrincipalMellin.ActualRecipe S η)
    (ξ : ℂ) (hξ : (499 / 500 : ℝ) - 1 / 100000 < ξ.re) :
    principalContourCorrection R ξ 1 (1 / 6) =
      CorrectionFactors.H_eta (principalArithmeticContext R) ξ := by
  obtain ⟨hm, hh⟩ :=
    (PrincipalCorrection.principal_specialization (principalArithmeticContext R)
      (principalEulerFrequency R) rfl).2 ξ hξ
  exact hh

theorem principal_theta_at_euler_generator (R : PrincipalMellin.ActualRecipe S η)
    (p : LocalFiniteSums.ExteriorPrime R.A) :
    R.probe.coefficients.theta (R.probe.coefficients.generator (LocalFiniteSums.primeIdeal p)) =
      LocalFiniteSums.vartheta (principalArithmeticContext R) p := by
  let C := principalArithmeticContext R
  let D := R.probe.coefficients
  have hD := principal_actual_arithmetic_compatibility R
  rw [hD.theta_recipe _ (D.generates _).1]
  change WeightedFiniteCoefficient.Proof.thetaHom R.A
    (R.A.correctionTheta C.correction.Λ C.correction.G C.correction.η_id)
    (WeightedFiniteCoefficient.fieldUnit R.A _ _) = _
  rw [WeightedFiniteCoefficient.Proof.theta_associated R.A _ C.correction.theta_unit
    _ _ (D.generates _).1 (LocalFiniteSums.generator_generates C p).1
    ((D.generates _).2.trans (LocalFiniteSums.generator_generates C p).2.symm)]
  rfl

def principalEulerPrimeEquiv (R : PrincipalMellin.ActualRecipe S η) :
    LocalFiniteSums.ExteriorPrime R.A ≃ ExteriorIdealEuler.PrimeIndex R.A.cS where
  toFun p := ⟨LocalFiniteSums.primeIdeal p, p.val.prime⟩
  invFun p := ⟨⟨p.val.val, (Ideal.prime_iff_isPrime p.val.property.1).mp p.property,
    p.val.property.1⟩, p.val.property.2⟩
  left_inv p := by rfl
  right_inv p := by rfl

theorem principal_localCorrection_eq_h_p (R : PrincipalMellin.ActualRecipe S η)
    (p : LocalFiniteSums.ExteriorPrime R.A) (s : ℂ) :
    R.localCorrection (principalEulerPrimeEquiv R p) s =
      CorrectionFactors.h_p (principalArithmeticContext R) p s := by
  unfold PrincipalMellin.ActualRecipe.localCorrection
  change Audit.Euler.principalCorrection (idealNorm p.val.asIdeal : ℂ)⁻¹
    (R.target p.val.asIdeal * comparisonRealPower (idealNorm p.val.asIdeal) (-s))
    (R.probe.coefficients.theta (R.probe.coefficients.generator
        (LocalFiniteSums.primeIdeal p)) ^ 6 *
      comparisonRealPower (idealNorm p.val.asIdeal) (3 - 6 * s)) = _
  rw [principal_theta_at_euler_generator]
  unfold Audit.Euler.principalCorrection CorrectionFactors.h_p LocalFiniteSums.qPower
    LocalFiniteSums.Q SArithmeticData.exteriorNorm LocalFiniteSums.primeIdeal
  have hn : 0 < idealNorm p.val.asIdeal := by
    unfold idealNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.val.ne_bot)
  have hm : comparisonRealPower (idealNorm p.val.asIdeal) (-1) =
      (idealNorm p.val.asIdeal : ℂ)⁻¹ := by
    rw [comparisonRealPower]
    have h := Complex.exp_neg ((Real.log (idealNorm p.val.asIdeal) : ℂ))
    simpa [← Complex.ofReal_exp, Real.exp_log hn] using h
  have h2 : comparisonRealPower (idealNorm p.val.asIdeal) (-2) =
      (idealNorm p.val.asIdeal : ℂ)⁻¹ ^ 2 := by
    rw [← hm, comparisonRealPower, comparisonRealPower, pow_two, ← Complex.exp_add]
    congr 1
    ring
  have he2 : (idealNorm p.val.asIdeal : ℂ)⁻¹ *
      comparisonRealPower (idealNorm p.val.asIdeal) (3 - 6 * s) =
      comparisonRealPower (idealNorm p.val.asIdeal) (2 - 6 * s) := by
    rw [← hm, comparisonRealPower, comparisonRealPower, comparisonRealPower,
      ← Complex.exp_add]
    congr 1
    ring
  change _ = (1 - comparisonRealPower (idealNorm p.val.asIdeal) (-2)) *
    (1 - (1 - comparisonRealPower (idealNorm p.val.asIdeal) (-1)) * R.target p.val.asIdeal *
      comparisonRealPower (idealNorm p.val.asIdeal) (-s) -
      LocalFiniteSums.vartheta (principalArithmeticContext R) p ^ 6 *
        comparisonRealPower (idealNorm p.val.asIdeal) (2 - 6 * s)) /
    ((1 - LocalFiniteSums.vartheta (principalArithmeticContext R) p ^ 6 *
        comparisonRealPower (idealNorm p.val.asIdeal) (3 - 6 * s)) *
      (1 - R.target p.val.asIdeal * comparisonRealPower (idealNorm p.val.asIdeal) (-s)))
  rw [h2, hm, ← he2]
  ring

theorem principal_H_eq_H_eta (R : PrincipalMellin.ActualRecipe S η) (s : ℂ) :
    R.H s = CorrectionFactors.H_eta (principalArithmeticContext R) s := by
  unfold PrincipalMellin.ActualRecipe.H CorrectionFactors.H_eta
  rw [← (principalEulerPrimeEquiv R).tprod_eq]
  apply tprod_congr
  intro p
  exact principal_localCorrection_eq_h_p R p s

theorem principalContourCorrection_at_double_residue
    (R : PrincipalMellin.ActualRecipe S η) (ξ : ℂ)
    (hξ : (499 / 500 : ℝ) - 1 / 100000 < ξ.re) :
    principalContourCorrection R ξ 1 (1 / 6) = R.H ξ := by
  rw [principal_H_eq_H_eta]
  exact principalContourCorrection_principal_specialization R ξ hξ

theorem principal_real_weight_measurable (R : PrincipalMellin.ActualRecipe S η) : Measurable R.W.W1Hat :=
  (ProbeSheet.MellinProof.realWeight_mellin_differentiable R.probe.W1).continuous.measurable

theorem principal_real_weight_rapid_strip_decay (R : PrincipalMellin.ActualRecipe S η) (a b : ℝ) :
    comparisonRapidStripDecay R.W.W1Hat a b := by
  intro N hN
  obtain ⟨C, hC, hb⟩ :=
    ProbeSheet.MellinProof.realWeight_mellin_rapid_on_strip R.probe.W1 a b N hN
  refine ⟨C + 1, by positivity, ?_⟩
  intro s hs
  have h := hb s.re hs s.im
  have heq : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))

private theorem principal_frequency_exponent_zero (R : PrincipalMellin.ActualRecipe S η)
    (p : LocalFiniteSums.ExteriorPrime R.A) :
    ((principalEulerFrequency R).j p).val = 0 := by
  simp only [CorrectionFactors.Frequency.j, principalEulerFrequency, idealPrimeExponent]
  have ht : UniqueFactorizationMonoid.normalizedFactors
      (⊤ : Ideal (NumberField.RingOfIntegers F)) = 0 :=
    by simpa only [Ideal.one_eq_top] using
      (UniqueFactorizationMonoid.normalizedFactors_one
        (α := Ideal (NumberField.RingOfIntegers F)))
  rw [ht]
  simp

theorem principalContourCorrection_measurable (R : PrincipalMellin.ActualRecipe S η) :
    Measurable (fun p : ℂ × ℂ × ℂ => principalContourCorrection R p.1 p.2.1 p.2.2) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (NumberField.RingOfIntegers F) :=
    Function.Injective.countable NumberField.RingOfIntegers.coe_injective
  letI : Countable (Ideal (NumberField.RingOfIntegers F)) := by
    have h : Function.Surjective (fun s : Finset (NumberField.RingOfIntegers F) =>
        Ideal.span (↑s : Set (NumberField.RingOfIntegers F))) := by
      intro I
      exact IsNoetherian.noetherian I
    exact h.countable
  unfold principalContourCorrection
  apply Measurable.tprod
  intro p
  simp only [CorrectionFactors.localFactor, principal_frequency_exponent_zero, ↓reduceIte]
  unfold CorrectionFactors.goodFactor CorrectionFactors.goodRational
    CorrectionFactors.V CorrectionFactors.W CorrectionFactors.D CorrectionFactors.E
    LocalFiniteSums.qPower
  simp only [CorrectionFactors.V, LocalFiniteSums.qPower]
  fun_prop

theorem principal_L_differentiableOn (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ R.L {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  apply R.continuation.L_holo.mul
  apply DifferentiableOn.fun_finset_prod
  intro v hv
  exact ((((differentiable_id.neg).mul_const
    (Real.log (idealNorm v.asIdeal) : ℂ)).cexp).const_mul
      (R.target v.asIdeal)).differentiableOn.const_sub 1

theorem principal_L_measurable_on_continuation_domain (R : PrincipalMellin.ActualRecipe S η) :
    Measurable (fun s : {s : ℂ | 0 < s.re ∧ s ≠ 1} => R.L s) :=
  (principal_L_differentiableOn R).continuousOn.restrict.measurable

theorem principal_L_measurable_extension (R : PrincipalMellin.ActualRecipe S η) :
    ∃ Lm : ℂ → ℂ, Measurable Lm ∧
      ∀ s : ℂ, 0 < s.re → s ≠ 1 → Lm s = R.L s := by
  let D : Set ℂ := {s : ℂ | 0 < s.re ∧ s ≠ 1}
  have hD : MeasurableSet D :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne).measurableSet
  obtain ⟨Lm, hLm, hEq⟩ := (MeasurableEmbedding.subtype_coe hD).exists_measurable_extend
    (principal_L_measurable_on_continuation_domain R) (fun _ => ⟨(0 : ℂ)⟩)
  refine ⟨Lm, hLm, ?_⟩
  intro s hs hs1
  exact congrFun hEq ⟨s, hs, hs1⟩

theorem actual_constant_eq_regularized_c₀
    (R : PrincipalMellin.ActualRecipe S η) :
    R.c = PrincipalZShift.c₀ (principalRegularization R 1) R.W.M R.W.W1Hat := rfl

theorem principal_xi_contour_conditions (R : PrincipalMellin.ActualRecipe S η) (Z : ℝ) (hZ : 1 ≤ Z) :
    Nonempty (PrincipalZShift.XiContourConditions Z R.L R.H) := by
  obtain ⟨_, _, hG, hb, _⟩ := PrincipalMellin.actual_principal_spectral_properties S η R
  obtain ⟨C, hC, hbound⟩ := hb comparisonSigma₁ 2
    (by norm_num [comparisonSigma₁, comparisonDelta])
    (by norm_num [comparisonSigma₁, comparisonDelta])
  let B : ℝ := Real.exp ((2 - 8 / 15) * Real.log Z)
  have hB : 0 < B := Real.exp_pos _
  have heq (s : ℂ) : PrincipalZShift.transformKernel Z R.L R.H s =
      comparisonRealPower Z (comparisonC s) * R.G s := by
    unfold PrincipalZShift.transformKernel PrincipalMellin.ActualRecipe.G
      PrincipalMellin.ActualRecipe.N
    ring
  refine ⟨{s : ℂ | 1 < s.re}, 2 * B * C, by positivity,
    isOpen_lt continuous_const Complex.continuous_re, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : comparisonSigma₁ ≤ s.re := hs.1
    norm_num [comparisonSigma₁, comparisonDelta] at hs'
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 10000001 / 10000000) hs'
  · have hp : DifferentiableOn ℂ (fun s => comparisonRealPower Z (comparisonC s))
        {s : ℂ | 1 < s.re} :=
      ((differentiable_id.sub_const (8 / 15)).mul_const
        (Real.log Z : ℂ)).cexp.differentiableOn
    exact (hp.mul hG).congr (fun s _ => heq s)
  · intro s hs
    rw [heq, norm_mul]
    have hp : ‖comparisonRealPower Z (comparisonC s)‖ ≤ B := by
      rw [MellinZeroFree.norm_comparisonRealPower]
      apply Real.exp_le_exp.mpr
      norm_num [comparisonC, Complex.sub_re]
      exact mul_le_mul_of_nonneg_right (by linarith [hs.2]) (Real.log_nonneg hZ)
    have hg : ‖R.G s‖ ≤ C / (1 + s.im ^ 2) := by
      have ht := hbound s.re hs s.im
      simpa only [Complex.re_add_im] using ht
    have ht : 1 / (1 + s.im ^ 2) ≤ 2 * (1 + |s.im|) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two]
      have hpos : 0 < (1 + |s.im|) ^ 2 := sq_pos_of_pos (by positivity)
      have hpos' : 0 < 1 + s.im ^ 2 := by positivity
      rw [← div_eq_mul_inv, div_le_div_iff₀ hpos' hpos]
      nlinarith [sq_nonneg (|s.im| - 1), sq_abs s.im]
    calc
      _ ≤ B * (C / (1 + s.im ^ 2)) := mul_le_mul hp hg (norm_nonneg _) hB.le
      _ = B * C * (1 / (1 + s.im ^ 2)) := by ring
      _ ≤ B * C * (2 * (1 + |s.im|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg hB.le hC)
      _ = _ := by ring

theorem principal_incomplete_reciprocal_bound
    (R : PrincipalMellin.ActualRecipe S η) (a : ℝ) (ha : 1 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → ‖(R.L s)⁻¹‖ ≤ B := by
  let coeff : ExteriorIdeal (⊤ : Ideal (NumberField.RingOfIntegers F)) → ℂ :=
    fun I => R.target I.val
  let M : ℝ := Real.exp ((3 / 2 : ℝ) *
    ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a))
  have hM : 0 < M := Real.exp_pos _
  have hfull : ∀ s : ℂ, a ≤ s.re → ‖(R.continuation.L s)⁻¹‖ ≤ M := by
    intro s hs
    have hexp : Complex.exp (HeckeLogProof.eulerLog coeff s) = R.continuation.L s := by
      rw [HeckeLogProof.exp_eulerLog _
        (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target)
        s (ha.trans_le hs)]
      have hsupport : Function.support (fun I : Ideal (NumberField.RingOfIntegers F) =>
          R.target I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
          {I : Ideal (NumberField.RingOfIntegers F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
        intro I hI
        simp only [Function.mem_support] at hI
        refine ⟨?_, by simp⟩
        intro hzero
        have hη : R.target I = 0 := (R.target.eq_zero_iff' I).mpr (Or.inl hzero)
        exact hI (by simpa only [hη, zero_mul])
      exact ((hasSum_subtype_iff_of_support_subset hsupport).mpr
        (R.continuation.series s (ha.trans_le hs))).tsum_eq
    rw [← hexp, ← Complex.exp_neg, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h := HeckeLogProof.eulerLog_norm_le coeff
      (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target)
      a ha s hs
    rw [Complex.neg_re]
    exact ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans h
  let u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℝ :=
    fun v => (1 - Real.exp (-a * Real.log (idealNorm v.asIdeal)))⁻¹
  have hupos : ∀ v, 0 < u v := by
    intro v
    have hQ : 1 < idealNorm v.asIdeal := by
      dsimp [idealNorm]
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hlog := Real.log_pos hQ
    dsimp [u]
    apply inv_pos.mpr
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    nlinarith
  refine ⟨M * ∏ v ∈ R.A.Sf, u v,
    mul_pos hM (Finset.prod_pos (fun v hv => hupos v)), ?_⟩
  intro s hs
  have hlocal : ∀ v, ‖(1 - R.target v.asIdeal *
      comparisonRealPower (idealNorm v.asIdeal) (-s))⁻¹‖ ≤ u v := by
    intro v
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
    rw [norm_inv]
    apply inv_anti₀ (inv_pos.mp (hupos v))
    have ht := norm_sub_norm_le (1 : ℂ)
      (R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))
    rw [norm_one] at ht
    dsimp [u] at *
    linarith
  change ‖(R.continuation.L s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)))⁻¹‖ ≤ _
  rw [mul_inv_rev, norm_mul]
  calc
    _ ≤ (∏ v ∈ R.A.Sf, u v) * M := by
      apply mul_le_mul
      · rw [← Finset.prod_inv_distrib, norm_prod]
        exact Finset.prod_le_prod₀ (fun v hv => norm_nonneg _) (fun v hv => hlocal v)
      · exact hfull s hs
      · exact norm_nonneg _
      · exact (Finset.prod_pos (fun v hv => hupos v)).le
    _ = _ := mul_comm _ _

theorem principal_error_reciprocal_bound
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ : ℂ,
      ξ.re = comparisonSigma₁ → ‖(R.L ξ)⁻¹‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := principal_incomplete_reciprocal_bound R comparisonSigma₁
    (by norm_num [comparisonSigma₁, comparisonDelta])
  exact ⟨B, hB, fun ξ hξ => hb ξ hξ.ge⟩

theorem principal_fixed_weight_errors_of_numerator_bound
    (R : PrincipalMellin.ActualRecipe S η)
    (hM : Measurable R.W.M)
    (hMdecay : comparisonRapidStripDecay R.W.M PrincipalZShift.zLine comparisonZeta₁)
    (hNumerator : ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ,
      s.re ∈ ({(19 / 20 : ℝ), 6 * comparisonZeta₁,
        6 * PrincipalZShift.zLine} : Set ℝ) →
      ‖R.L s‖ ≤ B * (2 + |s.im|) ^ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ‖PrincipalZShift.Rw Z R.W.M R.W.W1Hat R.L R.L (principalContourCorrection R)‖ +
        ‖PrincipalZShift.Rz Z (principalRegularization R 1) R.W.M R.W.W1Hat R.L R.L
          (principalContourCorrection R)‖ ≤ C * Z ^ ((7 / 15 : ℝ) - 1 / 2000) := by
  obtain ⟨Lm, hLm, hEq⟩ := principal_L_measurable_extension R
  have hnum : ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ,
      s.re ∈ ({(19 / 20 : ℝ), 6 * comparisonZeta₁,
        6 * PrincipalZShift.zLine} : Set ℝ) →
      ‖Lm s‖ ≤ B * (2 + |s.im|) ^ d := by
    obtain ⟨B, d, hB, hd, hb⟩ := hNumerator
    refine ⟨B, d, hB, hd, ?_⟩
    intro s hs
    have hs' : s.re = 19 / 20 ∨ s.re = 6 * comparisonZeta₁ ∨
        s.re = 6 * PrincipalZShift.zLine := by simpa only [Set.mem_insert_iff,
          Set.mem_singleton_iff] using hs
    have hpos : 0 < s.re := by
      rcases hs' with h | h | h <;> norm_num [h, comparisonZeta₁,
        PrincipalZShift.zLine, comparisonDelta]
    have hne : s ≠ 1 := by
      intro h
      rw [h] at hs'
      norm_num [comparisonZeta₁, PrincipalZShift.zLine, comparisonDelta] at hs'
    rw [hEq s hpos hne]
    exact hb s hs
  have hrec : ∃ B : ℝ, 0 < B ∧ ∀ ξ : ℂ,
      ξ.re = comparisonSigma₁ → ‖(Lm ξ)⁻¹‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ := principal_error_reciprocal_bound R
    refine ⟨B, hB, ?_⟩
    intro ξ hξ
    rw [hEq ξ (by norm_num [hξ, comparisonSigma₁, comparisonDelta]) (by
      intro h; rw [h] at hξ; norm_num [comparisonSigma₁, comparisonDelta] at hξ)]
    exact hb ξ hξ
  obtain ⟨C, hC, hb⟩ := PrincipalErrors.fixed_weight_estimates_analytic
    (principalRegularization R 1) R.W.M R.W.W1Hat Lm Lm (principalContourCorrection R)
    hM (principal_real_weight_measurable R) hLm hLm (principalContourCorrection_measurable R)
    hMdecay (principal_real_weight_rapid_strip_decay R _ _) hnum hrec
    (principalContourCorrection_error_bound R)
  have hline (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≠ 1) (t : ℝ) :
      Lm ((σ : ℂ) + (t : ℂ) * Complex.I) =
        R.L ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    apply hEq
    · simpa using hσ
    · intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
        Complex.one_re] at hr
      exact hσ1 hr
  have hw (Z : ℝ) : PrincipalZShift.Rw Z R.W.M R.W.W1Hat Lm Lm
        (principalContourCorrection R) =
      PrincipalZShift.Rw Z R.W.M R.W.W1Hat R.L R.L (principalContourCorrection R) := by
    unfold PrincipalZShift.Rw PrincipalWShift.J comparisonTripleVerticalIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    unfold PrincipalWShift.kernel
    rw [hline comparisonSigma₁ (by norm_num [comparisonSigma₁, comparisonDelta])
      (by norm_num [comparisonSigma₁, comparisonDelta])]
    rw [hline (19 / 20) (by norm_num) (by norm_num)]
    have he : (6 : ℂ) * ((comparisonZeta₁ : ℂ) + (t.2.2 : ℂ) * Complex.I) =
        ((6 * comparisonZeta₁ : ℝ) : ℂ) + ((6 * t.2.2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [he, hline (6 * comparisonZeta₁)
      (by norm_num [comparisonZeta₁, comparisonDelta])
      (by norm_num [comparisonZeta₁, comparisonDelta])]
  have hz (Z : ℝ) : PrincipalZShift.Rz Z (principalRegularization R 1) R.W.M R.W.W1Hat
        Lm Lm (principalContourCorrection R) =
      PrincipalZShift.Rz Z (principalRegularization R 1) R.W.M R.W.W1Hat R.L R.L
        (principalContourCorrection R) := by
    unfold PrincipalZShift.Rz PrincipalWShift.doubleVerticalIntegral
    congr 2
    apply integral_congr_ae
    filter_upwards [] with t
    unfold PrincipalWShift.residueKernel
    rw [hline comparisonSigma₁ (by norm_num [comparisonSigma₁, comparisonDelta])
      (by norm_num [comparisonSigma₁, comparisonDelta])]
    have he : (6 : ℂ) * ((PrincipalZShift.zLine : ℂ) + (t.2 : ℂ) * Complex.I) =
        ((6 * PrincipalZShift.zLine : ℝ) : ℂ) + ((6 * t.2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [he, hline (6 * PrincipalZShift.zLine)
      (by norm_num [PrincipalZShift.zLine]) (by norm_num [PrincipalZShift.zLine])]
  refine ⟨C, hC, ?_⟩
  intro Z hZ
  simpa only [hw, hz] using (hb Z hZ).2.2

theorem principal_initial_residue_estimate
    (R : PrincipalMellin.ActualRecipe S η) :
    (fun x : ℝ => principalInitialIntegral R x - R.c * R.f x) =O[atTop]
      (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2000)) := by
  obtain ⟨hM, hMdecay, hNumerator⟩ := PrincipalResidueInputs.error_factor_inputs R
  obtain ⟨C, hC, herrors⟩ :=
    principal_fixed_weight_errors_of_numerator_bound R hM hMdecay hNumerator
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ
  have hEuler : ∀ ξ w z : ℂ, ξ.re = 4 → w.re = 4 → z.re = 2 →
      separatedSeries R (principalFrequency R) ξ w z =
        (R.L (6 * z) * R.L w / R.L ξ) * principalContourCorrection R ξ w z := by
    intro ξ w z hξ hw hz
    exact PrincipalResidueInputs.initial_line_euler R (principalArithmeticContext R) rfl
      (principalEulerFrequency R) rfl ξ w z hξ hw hz
  obtain ⟨hi⟩ := PrincipalResidueInputs.initial_contour R
    (principalArithmeticContext R) rfl (principalEulerFrequency R) rfl Z hZ
  obtain ⟨hw⟩ := PrincipalResidueInputs.w_contour R
    (principalArithmeticContext R) rfl (principalEulerFrequency R) rfl Z hZ
  obtain ⟨hz⟩ := PrincipalResidueInputs.z_contour R
    (principalArithmeticContext R) rfl (principalEulerFrequency R) rfl Z hZ
  obtain ⟨hx⟩ := principal_xi_contour_conditions R Z hZ
  have hcorrection : ∀ ξ : ℂ, ξ.re = comparisonSigma₁ →
      principalContourCorrection R ξ 1 (1 / 6) = R.H ξ := by
    intro ξ hξ
    apply principalContourCorrection_at_double_residue R ξ
    norm_num [hξ, comparisonSigma₁, comparisonDelta]
  have hdecomp := PrincipalResidueInputs.decomposition_of_local_correction Z hZ
    R.W.M R.W.W1Hat R.L R.L (principalRegularization R) R.H
    (principalContourCorrection R) hcorrection hi hw hz hx
  have hf : R.f Z = PrincipalZShift.f Z R.L R.H :=
    comparisonPrincipalSpectralTransform_eq_f F R.A R.target R.probe.principal
      R.continuation R.H Z
  rw [principalInitialIntegral_eq_J_of_initial_euler R (principalContourCorrection R)
    hEuler Z (by linarith), hdecomp, ← actual_constant_eq_regularized_c₀, ← hf]
  have heq : R.c * R.f Z +
      PrincipalZShift.Rw Z R.W.M R.W.W1Hat R.L R.L (principalContourCorrection R) +
      PrincipalZShift.Rz Z (principalRegularization R 1) R.W.M R.W.W1Hat R.L R.L
        (principalContourCorrection R) - R.c * R.f Z =
      PrincipalZShift.Rw Z R.W.M R.W.W1Hat R.L R.L (principalContourCorrection R) +
      PrincipalZShift.Rz Z (principalRegularization R 1) R.W.M R.W.W1Hat R.L R.L
        (principalContourCorrection R) := by ring
  rw [heq]
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Z) _)] using
      (norm_add_le _ _).trans (herrors Z hZ)

end
end DedekindZetaZeroFree.PrincipalMellinComparison
