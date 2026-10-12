module

public import DedekindZetaZeroFree.Theta.Unfolding.ReverseOrbitAbsoluteIntegrability
public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorValuationSupport
public import DedekindZetaZeroFree.Theta.Unfolding.AbsoluteReverseIntegration

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)
include D

lemma rationalValue_left_root (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) (t : KPAdeles F) :
    rationalValue R T v a (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 t * g) =
      (adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * t) : ℂ) * rationalValue R T v a g := by
  let A := KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  have hc := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12 R.A.primitive_zeta12
    (algebraMap F (KPAdeles F) (a : F) * t)
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  have he : (algebraMap F (KPAdeles F) (a : F) * t) * algebraMap F (KPAdeles F) (a⁻¹ : Fˣ) = t := by
    rw [mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
  change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (algebraMap F (KPAdeles F) (a : F) * t) * A = A *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        ((algebraMap F (KPAdeles F) (a : F) * t) * algebraMap F (KPAdeles F) (a⁻¹ : Fˣ)) at hc
  rw [he] at hc
  rw [rationalValue_eq_fourier R T, ← mul_assoc, ← hc, mul_assoc]
  letI := Q.quotientHaar
  rw [ExteriorWhittakerValues.StoredWhittaker.fourier_left_root R Q.dq (T.theta v)
    (ExteriorWhittakerValues.StoredWhittaker.core_rational_root R D (D.selected v) |>
      fun h => by simpa only [D.selected_eq] using h) _ (A * g) (D.period_integrable v (A * g))]
  have hχ := adelicTraceQuotientCharacter_mk F (algebraMap F (KPAdeles F) (a : F) * t)
  refine congrArg₂ (fun z : Circle => fun c : ℂ => (z : ℂ) * c) hχ ?_
  exact (rationalValue_eq_fourier R T v a g).symm

lemma orbit_forward_digit_norm (v : R.A.UnitQuotient)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (y : R.A.G) (m : ThetaReflectionData.Row R.A) (d : ThetaDigitAverage.Dig (RowPrime R m)) :
    ‖orbitFrequencyValue R Q T v i (signedArgument R m true y d)‖ =
      ‖rationalValue R T v (Quotient.out i.1 * i.2.val) (diagonal R y)‖ := by
  change ‖rationalValue R T v (Quotient.out i.1 * i.2.val) (signedArgument R m true y d)‖ = _
  simp only [signedArgument, ite_eq_left, one_mul]
  change ‖rationalValue R T v (Quotient.out i.1 * i.2.val)
    (diagonal R y * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d))‖ = _
  rw [(OrbitExpansion.diagonal_commute_digit_root R y m d).eq, rationalValue_left_root R D, norm_mul]
  simp only [Circle.norm_coe, one_mul]

lemma rational_diagonal_norm_list (v : R.A.UnitQuotient) (a : Fˣ) (y : R.A.G)
    (L : List (ThetaBranch.ExteriorPrime R.A)) (hL : L.Nodup)
    (ha : ∀ p : ThetaBranch.ExteriorPrime R.A, p ∉ L → p.val.valuation F (a : F) = 1) :
    ‖rationalValue R T v a (diagonal R y)‖ =
      ‖(L.map (fun p => D.exteriorValue R p a)).prod‖ *
        ‖fourier R Q.dq (T.theta v) (diagonal R (R.A.diagonal a * y))‖ := by
  have ht := OrbitExpansion.rationalTail_mem R a L hL ha
  have htc := (OrbitExpansion.raw_s_commute R y _ ht).map (OrbitExpansion.rawToGroup R)
  change Commute (diagonal R y) (OrbitExpansion.rawToGroup R (OrbitExpansion.rationalTail R a L)) at htc
  have hlc : Commute (diagonal R y)
      (L.map (fun p => OrbitExpansion.finiteLift R p.val (OrbitExpansion.rationalLocalA R a (.inr p.val)))).prod := by
    apply (OrbitExpansion.commute_list_product _ _ _).symm
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact (OrbitExpansion.diagonal_commute_exterior R y p _).symm
  rw [rationalValue_eq_fourier R T, OrbitExpansion.rationalLift_decomposition, mul_assoc,
    ← htc.eq, ← mul_assoc, OrbitExpansion.fourier_full_exterior R T v _ ht,
    mul_assoc, ← hlc.eq, ← mul_assoc]
  rw [OrbitExpansion.fourier_exterior_list R D v L hL _ _]
  · simp_rw [OrbitExpansion.exteriorLiftValue_rational]
    rw [norm_mul]
    congr 1
    simpa only [mul_one] using fourier_diagonal_mul_norm R (T := T) v (R.A.diagonal a) y 1
  · intro p hp t
    exact (OrbitExpansion.diagonal_commute_exterior_root R _ p t).mul_left
      (OrbitExpansion.diagonal_commute_exterior_root R _ p t)

def forwardExterior (a : Fˣ) : ℂ := ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p a

lemma forwardExterior_finite (E : ExteriorCoefficients R Q T D) (a : Fˣ) :
    Function.HasFiniteMulSupport (fun p : ThetaBranch.ExteriorPrime R.A => D.exteriorValue R p a) := by
  apply (OrbitExpansion.exterior_order_support_finite R a).subset
  intro p hp
  by_contra hn
  simp only [Set.mem_ofPred_eq, not_not] at hn
  apply hp
  dsimp only
  rw [E.rational_exact]
  exact OrbitExpansion.sphericalFactor_order_zero R p a hn

lemma rational_diagonal_norm (E : ExteriorCoefficients R Q T D) (P : Packet R Q)
    (hf : ForwardIdentity R Q T P) (v : R.A.UnitQuotient) (a : Fˣ) (y : R.A.G) :
    ‖rationalValue R T v a (diagonal R y)‖ = ‖forwardExterior R D a‖ * ‖P.forwardProfile v (R.A.diagonal a * y)‖ := by
  let s := (OrbitExpansion.exterior_order_support_finite R a).toFinset
  have ha (p : ThetaBranch.ExteriorPrime R.A) (hp : p ∉ s) : p.val.valuation F (a : F) = 1 := by
    apply (OrbitExpansion.order_eq_zero_iff _ _).mp
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hp
  rw [rational_diagonal_norm_list R D v a y s.toList s.nodup_toList
    (by simpa only [Finset.mem_toList] using ha), hf]
  congr 2
  rw [Finset.prod_map_toList]
  symm
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hn
  apply hp
  dsimp only
  rw [E.rational_exact]
  exact OrbitExpansion.sphericalFactor_order_zero R p a ((OrbitExpansion.order_eq_zero_iff _ _).mpr (ha p hn))
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical

lemma positiveAxis_le_secondMoment (V : PositiveAxis → ℝ)
    (hV : ∀ x, 0 ≤ V x)
    (hratio : ∀ x y : PositiveAxis, x.val ≤ y.val → V y ≤ (y.val / x.val) * V x)
    (hint : Integrable (fun x : PositiveAxis => V x * x.val ^ 2) positiveHaar) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : PositiveAxis, V x ≤ B / x.val ^ 2 := by
  let f : ℝ → ℝ := fun t => if ht : 0 < t then V ⟨t, ht⟩ * t else 0
  have hf : IntegrableOn f (Set.Ioi 0) volume := by
    have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Ioi
    have h : Integrable (fun x : PositiveAxis => f x.val * x.val) positiveHaar := by
      simpa only [f, dite_eq_left (show 0 < (↑_ : ℝ) from Subtype.property _), pow_two, mul_assoc] using hint
    change Integrable ((fun t : ℝ => f t * t) ∘ Subtype.val) positiveHaar at h
    rw [← he.integrable_map_iff, positiveHaar_map_val, restrict_withDensity measurableSet_Ioi,
      integrable_withDensity_iff_integrable_smul' (by fun_prop)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at h
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)]
    change t⁻¹ * (f t * t) = f t
    field_simp [ne_of_gt (show 0 < t from ht)]
  let J : ℝ := ∫ t in Set.Ioi 0, f t
  have hnon (t : ℝ) : 0 ≤ f t := by
    dsimp [f]; split_ifs with ht
    · exact mul_nonneg (hV _) ht.le
    · rfl
  have hJ : 0 ≤ J := integral_nonneg hnon
  refine ⟨8 * J, by positivity, ?_⟩
  intro x
  have hsub : Set.Icc (x.val / 2) x.val ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht; exact lt_of_lt_of_le (div_pos x.property (by norm_num)) ht.1
  have hfx := hf.mono_set hsub
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (x.val / 2) x.val) : V x * x.val / 4 ≤ f t := by
    have htpos : 0 < t := hsub ht
    have hr := hratio ⟨t, htpos⟩ x ht.2
    have hmul : V x * t ≤ x.val * V ⟨t, htpos⟩ := by
      apply (le_div_iff₀ htpos).mp
      simpa [div_mul_eq_mul_div] using hr
    have hhalf : V x / 2 ≤ V ⟨t, htpos⟩ := by
      nlinarith [mul_nonneg (hV x) (sub_nonneg.mpr ht.1), x.property]
    dsimp [f]; rw [dite_eq_left htpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) htpos.le,
      mul_nonneg (hV x) (sub_nonneg.mpr ht.1)]
  have hlow : (x.val / 2) * (V x * x.val / 4) ≤ ∫ t in Set.Icc (x.val / 2) x.val, f t := by
    have h := setIntegral_mono_on (integrableOn_const (C := V x * x.val / 4) (hs := by simp)) hfx
      measurableSet_Icc hpoint
    have hxhalf : 0 ≤ x.val / 2 := (div_pos x.property (by norm_num)).le
    simpa [setIntegral_const, Measure.real, Real.volume_Icc, smul_eq_mul,
      sub_half, ENNReal.toReal_ofReal hxhalf] using h
  have hupp : (∫ t in Set.Icc (x.val / 2) x.val, f t) ≤ J :=
    setIntegral_mono_set hf (Filter.Eventually.of_forall hnon) (Filter.Eventually.of_forall (fun t => hsub (a := t)))
  apply (le_div_iff₀ (sq_pos_of_pos x.property)).mpr
  nlinarith [hlow.trans hupp]

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma positiveSheet_inverse_square_bound (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (P : Packet R Q) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : PositiveAxis, P.positiveSheet x ≤ B / x.val ^ 2 := by
  apply positiveAxis_le_secondMoment
  · intro x; exact (GaussianSmoothing.positiveSheet_pos N P x).le
  · intro x y hxy
    rw [GaussianSmoothing.positiveSheet_eq N P, GaussianSmoothing.sheet, GaussianSmoothing.sheet, ← integral_const_mul]
    apply integral_mono (GaussianSmoothing.sheet_integrable N P y) ((GaussianSmoothing.sheet_integrable N P x).const_mul _)
    intro z
    exact GaussianSmoothing.radial_section_le P P.v₀ x y hxy z.val
  · have hi := (GaussianSmoothing.sheet_mellin N P 2 (by norm_num)).1
    have hr := Complex.reCLM.integrable_comp hi
    simpa only [Complex.cpow_ofNat, Complex.reCLM_apply, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re] using hr
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma positive_profile_norm {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ‖P.forwardProfile v y‖ = GaussianSmoothing.radial P y := by
  rw [OrbitExpansion.forwardProfile_branch, norm_mul, DigitMasks.branch_norm, one_mul]
  change ‖(GaussianSmoothing.radial P y : ℂ)‖ = GaussianSmoothing.radial P y
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (GaussianSmoothing.radial_nonneg P y)]

lemma positive_full_sheet_integrable (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (P : Packet R Q) (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    Integrable (fun y : Sheet R.A l => (GaussianSmoothing.radial P y.val : ℂ)) (sheetHaar R.A P.v₀ N.groupHaar l) := by
  letI := N.groupHaar_isHaar
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe]
  exact (sheetTranslation R.A P.v₀ l).measurableEmbedding.integrable_map_iff.mpr
    (Complex.ofRealCLM.integrable_comp (GaussianSmoothing.sheet_integrable N P l))

lemma positive_full_sheet_integral (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (P : Packet R Q) (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    (∫ y : Sheet R.A l, (GaussianSmoothing.radial P y.val : ℂ) ∂sheetHaar R.A P.v₀ N.groupHaar l) =
      (P.positiveSheet l : ℂ) := by
  letI := N.groupHaar_isHaar
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe,
    (sheetTranslation R.A P.v₀ l).measurableEmbedding.integral_map, integral_complex_ofReal,
    GaussianSmoothing.positiveSheet_eq N P]
  rfl

lemma positive_orbit_sheet_mass (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (P : Packet R Q) (a : Fˣ) (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    Summable (fun γ : ThetaReflectionData.rationalGamma R.A =>
      ∫ y : Sheet R.A l, GaussianSmoothing.radial P (R.A.diagonal (γ.val * a) * y.val)
        ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar l) ∧
    (∑' γ : ThetaReflectionData.rationalGamma R.A,
      ∫ y : Sheet R.A l, GaussianSmoothing.radial P (R.A.diagonal (γ.val * a) * y.val)
        ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar l) = P.positiveSheet (q R.A a * l) := by
  letI := N.groupHaar_isHaar
  have hu := integral_mul_unfold R.A P.v₀ N.groupHaar a l
    (pregroupingSheet R.A P.v₀ l) (pregroupingSheet_fundamental R.A P.v₀ N.groupHaar l)
    (fun y => (GaussianSmoothing.radial P y : ℂ)) (positive_full_sheet_integrable R N P (q R.A a * l))
  have hs := hu.1.map Complex.reCLM Complex.reCLM.continuous
  simp only [Function.comp_def, integral_complex_ofReal, Complex.reCLM_apply, Complex.ofReal_re] at hs
  refine ⟨?_, ?_⟩
  · have h := hs.comp_injective (gammaEquiv R).injective
    simpa only [Function.comp_def, gammaEquiv_val, ← map_mul, pregroupingSheetHaar] using h
  · have hc := hu.1.hasSum.map Complex.reCLM Complex.reCLM.continuous
    rw [hu.2, positive_full_sheet_integral R N P] at hc
    have hv : (∑' γ : R.A.Gamma1, ∫ y in pregroupingSheet R.A P.v₀ l,
        GaussianSmoothing.radial P (γ.val.val * R.A.diagonal a * y.val) ∂sheetHaar R.A P.v₀ N.groupHaar l) =
        P.positiveSheet (q R.A a * l) := by
      simpa only [Function.comp_def, integral_complex_ofReal, Complex.reCLM_apply, Complex.ofReal_re] using hc.tsum_eq
    have ht := (gammaEquiv R).toEquiv.tsum_eq (fun γ : R.A.Gamma1 =>
      ∫ y in pregroupingSheet R.A P.v₀ l, GaussianSmoothing.radial P (γ.val.val * R.A.diagonal a * y.val)
        ∂sheetHaar R.A P.v₀ N.groupHaar l)
    have hval (γ : ThetaReflectionData.rationalGamma R.A) :
      ((gammaEquiv R).toEquiv γ).val.val = R.A.diagonal γ.val := rfl
    simpa only [hval, ← map_mul, pregroupingSheetHaar] using ht.trans hv

lemma forwardExterior_norm_le_one {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D) (a : Fˣ) :
    ‖forwardExterior R D a‖ ≤ 1 := by
  have ht := finprod_eq_prod_of_mulSupport_subset (f := fun p : ThetaBranch.ExteriorPrime R.A => D.exteriorValue R p a)
    (s := (forwardExterior_finite R D E a).toFinset)
    (by intro p hp; exact (forwardExterior_finite R D E a).mem_toFinset.mpr hp)
  rw [forwardExterior, ht, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun p _ => exteriorValue_norm_le_one R D E p a)

lemma forwardExterior_zero_nonintegral {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D) (a : Fˣ)
    (ha : (a : F) ∉ R.A.R) : forwardExterior R D a = 0 := by
  change ¬ (∀ p, p ∉ R.A.Sf → p.valuation F (a : F) ≤ 1) at ha
  push Not at ha
  obtain ⟨p, hp, hv⟩ := ha
  apply finprod_eq_zero _ (⟨p, hp⟩ : ThetaBranch.ExteriorPrime R.A) _ (forwardExterior_finite R D E a)
  exact exteriorValue_zero_of_order_neg R D E _ _ (OrbitExpansion.order_negative_of_valuation_gt_one p a hv)

lemma orbitMass_forward_bound (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (P : Packet R Q) (D : SourceFactorization R Q T)
    (E : ExteriorCoefficients R Q T D) (hf : ForwardIdentity R Q T P)
    (v : R.A.UnitQuotient) (ξ : ThetaReflectionData.Frequency R.A)
    (γ : ThetaReflectionData.rationalGamma R.A) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    orbitMass R N T P v m true ξ γ d l ≤
      ∫ y : Sheet R.A l, GaussianSmoothing.radial P (R.A.diagonal (γ.val * Quotient.out ξ) * y.val)
        ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar l := by
  letI := N.groupHaar_isHaar
  have hi : Integrable (fun y : Sheet R.A l => orbitFrequencyValue R Q T v (ξ, γ)
      (signedArgument R m true y.val d)) (pregroupingSheetHaar R.A P.v₀ N.groupHaar l) :=
    continuous_pregroupingSheet_integrable R N P.v₀ l _
      ((orbitFrequencyValue_continuous R T v (ξ, γ)).comp
        ((DigitMasks.signedArgument_continuous R m true d).comp continuous_subtype_val))
  have hj := continuous_pregroupingSheet_integrable R N P.v₀ l
    (fun y => (GaussianSmoothing.radial P (R.A.diagonal (γ.val * Quotient.out ξ) * y.val) : ℂ))
    (Complex.continuous_ofReal.comp ((GaussianSmoothing.continuous_radial P).comp (continuous_const.mul continuous_subtype_val)))
  apply integral_mono hi.norm (Complex.reCLM.integrable_comp hj)
  intro y
  dsimp only
  rw [orbit_forward_digit_norm R D, rational_diagonal_norm R D E P hf, positive_profile_norm R,
    mul_comm (Quotient.out ξ) γ.val]
  exact mul_le_of_le_one_left (GaussianSmoothing.radial_nonneg P _) (forwardExterior_norm_le_one R D E _)

lemma orbit_forward_zero_off_support {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (P : Packet R Q) (hf : ForwardIdentity R Q T P)
    (v : R.A.UnitQuotient) (ξ : ThetaReflectionData.Frequency R.A)
    (γ : ThetaReflectionData.rationalGamma R.A) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m))
    (h : ((ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ : Fˣ) : F) ∉ R.A.R) :
    orbitFrequencyValue R Q T v (ξ, γ) (signedArgument R m true y d) = 0 := by
  have hx : (Quotient.out ξ : Fˣ).val ∉ R.A.R := by
    intro hx
    apply h
    have hm : (ThetaReflectionData.rowUnit R.A m : F) ∈ R.A.R := m.val.property
    exact R.A.R.mul_mem (R.A.R.pow_mem hm 2) hx
  have ha : ((Quotient.out ξ * γ.val : Fˣ) : F) ∉ R.A.R := fun ha => hx ((gamma_integral_iff R γ _).mp ha)
  apply norm_eq_zero.mp
  rw [orbit_forward_digit_norm R D, rational_diagonal_norm R D E P hf,
    forwardExterior_zero_nonintegral R D E _ ha, norm_zero, zero_mul]

 theorem orbitMass_forward_summable_bound (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (hf : ForwardIdentity R Q T P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v m ξ d (l : PositiveAxis),
      Summable (fun γ => orbitMass R N T P v m true ξ γ d l) ∧
      (∑' γ, orbitMass R N T P v m true ξ γ d l) ≤ K * (l.val ^ 2)⁻¹ * frequencyMajorant R m ξ := by
  obtain ⟨K, hK, hb⟩ := positiveSheet_inverse_square_bound R N P
  refine ⟨K, hK, ?_⟩
  intro v m ξ d l
  letI := N.groupHaar_isHaar
  by_cases hx : ((ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ : Fˣ) : F) ∈ R.A.R
  · have hs := positive_orbit_sheet_mass R N P (Quotient.out ξ) l
    have ht : Summable (fun γ => orbitMass R N T P v m true ξ γ d l) :=
      Summable.of_nonneg_of_le (fun γ => orbitMass_nonneg R N T P v m true ξ γ d l)
        (fun γ => orbitMass_forward_bound R N T P D E hf v ξ γ m d l) hs.1
    refine ⟨ht, ?_⟩
    have hle := Summable.tsum_le_tsum (fun γ => orbitMass_forward_bound R N T P D E hf v ξ γ m d l) ht hs.1
    rw [hs.2] at hle
    refine hle.trans ((hb (q R.A (Quotient.out ξ) * l)).trans_eq ?_)
    have hn : (q R.A (Quotient.out ξ)).val = ThetaReflectionData.frequencyNorm R.A ξ := by
      have he := ThetaReflectionData.frequencyNorm_mk R.A (Quotient.out ξ)
      simpa only [Quotient.out_eq, q] using he.symm
    simp only [frequencyMajorant, ite_eq_left hx, zpow_neg, zpow_ofNat]
    change K / ((q R.A (Quotient.out ξ)).val * l.val) ^ 2 = _
    rw [hn]; simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]; ring
  · have he (γ : ThetaReflectionData.rationalGamma R.A) : orbitMass R N T P v m true ξ γ d l = 0 := by
      unfold orbitMass
      simp only [orbit_forward_zero_off_support R D E P hf v ξ γ _ m d hx, norm_zero, integral_zero]
    simp only [he, tsum_zero, frequencyMajorant, ite_eq_right hx, mul_zero, le_refl]
    exact ⟨summable_zero, trivial⟩
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma orbitMass_forward_joint_bound (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (hf : ForwardIdentity R Q T P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v m d (l : PositiveAxis),
      Summable (fun i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A =>
        orbitMass R N T P v m true i.1 i.2 d l) ∧
      (∑' i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A,
        orbitMass R N T P v m true i.1 i.2 d l) ≤
        K * (l.val ^ 2)⁻¹ * (∑' ξ, frequencyMajorant R m ξ) := by
  obtain ⟨K, hK, hb⟩ := orbitMass_forward_summable_bound R N T P D E hf
  refine ⟨K, hK, ?_⟩
  intro v m d l
  have hξ : Summable (fun ξ => ∑' γ, orbitMass R N T P v m true ξ γ d l) :=
    Summable.of_nonneg_of_le (fun ξ => tsum_nonneg (fun γ => orbitMass_nonneg R N T P v m true ξ γ d l))
      (fun ξ => (hb v m ξ d l).2) ((frequencyMajorant_summable R m).mul_left (K * (l.val ^ 2)⁻¹))
  have hs := (summable_prod_of_nonneg (fun i => orbitMass_nonneg R N T P v m true i.1 i.2 d l)).mpr
    ⟨fun ξ => (hb v m ξ d l).1, hξ⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun ξ => (hb v m ξ d l).2) hξ
    ((frequencyMajorant_summable R m).mul_left (K * (l.val ^ 2)⁻¹))

lemma orbitMass_forward_smoothed (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (hf : ForwardIdentity R Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (Z : ℝ) (hZ : 0 < Z) :
    (∀ i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A,
      Integrable (fun t : PositiveAxis => ‖P.kernel t.val‖ * ‖digitWeight R m d‖ *
        orbitMass R N T P v m true i.1 i.2 d ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar) ∧
    Summable (fun i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A =>
      ∫ t : PositiveAxis, ‖P.kernel t.val‖ * ‖digitWeight R m d‖ *
        orbitMass R N T P v m true i.1 i.2 d ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar) := by
  obtain ⟨K, hK, hb⟩ := orbitMass_forward_joint_bound R N T P D E hf
  let C : ℝ := ‖digitWeight R m d‖ * K * Z ^ 2 * (∑' ξ, frequencyMajorant R m ξ)
  apply dominated_nonnegative_series
    (g := fun t : PositiveAxis => C * (‖P.kernel t.val‖ * (t.val ^ 2)⁻¹))
  · intro i t
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (orbitMass_nonneg R N T P _ _ _ _ _ _ _)
  · intro i
    exact (((kernel_continuous R N P).norm.stronglyMeasurable.mul stronglyMeasurable_const).mul
      (orbitMass_measurable R N T P v m true i.1 i.2 d Z hZ)).aestronglyMeasurable
  · intro t
    exact ((hb v m d ⟨t.val / Z, div_pos t.property hZ⟩).1).mul_left _
  · intro t
    rw [tsum_mul_left]
    have h := mul_le_mul_of_nonneg_left ((hb v m d ⟨t.val / Z, div_pos t.property hZ⟩).2)
      (mul_nonneg (norm_nonneg (P.kernel t.val)) (norm_nonneg (digitWeight R m d)))
    refine h.trans_eq ?_
    dsimp only [C]
    change ‖P.kernel t.val‖ * ‖digitWeight R m d‖ *
      (K * ((t.val / Z) ^ 2)⁻¹ * _) = _
    rw [div_pow, inv_div]
    simp only [div_eq_mul_inv]
    ring
  · exact (kernel_inverse_square_moment_integrable R N P).const_mul C

lemma orbit_product_integrable_of_mass (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) b Z (hZ : 0 < Z)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m))
    (hi : Integrable (fun t : PositiveAxis => ‖P.kernel t.val‖ * ‖digitWeight R m d‖ *
      orbitMass R N T P v m b i.1 i.2 d ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar) :
    letI := N.groupHaar_isHaar;
    Integrable (fun p : PositiveAxis × R.A.G1 =>
      P.kernel p.1.val * digitWeight R m d * orbitFrequencyValue R Q T v i
        (signedArgument R m b (sheetTranslation R.A P.v₀
          ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val d))
      (positiveHaar.prod ((kernelHaar R.A P.v₀ N.groupHaar).restrict (pregroupingDomain R.A).carrier)) := by
  letI := N.groupHaar_isHaar
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  apply (integrable_prod_iff (orbit_product_continuous R N T P v m b i.1 i.2 d Z hZ).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with t
    have hc : Continuous (fun y : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩ =>
      P.kernel t.val * digitWeight R m d * orbitFrequencyValue R Q T v i (signedArgument R m b y.val d)) :=
      continuous_const.mul ((orbitFrequencyValue_continuous R T v i).comp
        ((DigitMasks.signedArgument_continuous R m b d).comp continuous_subtype_val))
    have hi := continuous_pregroupingSheet_integrable R N P.v₀ _ _ hc
    rw [pregroupingSheetHaar_eq_map] at hi
    exact (sheetTranslation R.A P.v₀ _).measurableEmbedding.integrable_map_iff.mp hi
  · have he (t : PositiveAxis) := (sheet_mass_coordinates R N P.v₀
      ⟨t.val / Z, div_pos t.property hZ⟩ (fun y =>
        P.kernel t.val * digitWeight R m d * orbitFrequencyValue R Q T v i (signedArgument R m b y.val d))).symm
    simp_rw [he, orbitMass_weighted_eq R N T P]
    exact hi

 theorem forward_orbit_product_integrable (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (hf : ForwardIdentity R Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) Z (hZ : 0 < Z)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) :
    letI := N.groupHaar_isHaar;
    Integrable (fun p : PositiveAxis × R.A.G1 =>
      P.kernel p.1.val * digitWeight R m d * orbitFrequencyValue R Q T v i
        (signedArgument R m true (sheetTranslation R.A P.v₀
          ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val d))
      (positiveHaar.prod ((kernelHaar R.A P.v₀ N.groupHaar).restrict (pregroupingDomain R.A).carrier)) :=
  orbit_product_integrable_of_mass R N T P v m true Z hZ i d
    ((orbitMass_forward_smoothed R N T P D E hf v m d Z hZ).1 i)

 theorem forward_orbit_pregrouping (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (hf : ForwardIdentity R Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) Z (hZ : 0 < Z) :
    letI := N.groupHaar_isHaar;
    Summable (fun i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A =>
      ∑ d : ThetaDigitAverage.Dig (RowPrime R m),
        ∫ t : PositiveAxis, ∫ y : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
          ‖P.kernel t.val * digitWeight R m d * orbitFrequencyValue R Q T v i
            (signedArgument R m true y.val d)‖
          ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar) := by
  letI := N.groupHaar_isHaar
  simp_rw [orbitMass_weighted_eq R N T P]
  exact summable_sum (fun d _ => (orbitMass_forward_smoothed R N T P D E hf v m d Z hZ).2)
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem reverseAbsolute (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (hf : ForwardIdentity R Q T P) (H : SameResidueProfiles R Q T P) :
    ReverseAbsolute R N Q T P := by
  apply reverseAbsolute_of_orbit R N T P
  · intro v m b Z hZ
    cases b with
    | false => exact reverse_orbit_pregrouping R N T P D E H v m Z hZ
    | true => exact forward_orbit_pregrouping R N T P D E hf v m Z hZ
  · intro v m b Z hZ i d
    cases b with
    | false => exact reverse_orbit_product_integrable R N T P D E H v m Z hZ i d
    | true => exact forward_orbit_product_integrable R N T P D E hf v m Z hZ i d

def jointReverseAbsoluteSources {N : TraceHaarTransport R} (C : JointSameResidueProfileSources R N) : JointReverseAbsoluteSources R N where
  toJointSameResidueProfileSources := C
  absolute := reverseAbsolute R C.transport C.realization C.packet C.factorization
    C.exterior C.forward C.profiles
end DedekindZetaZeroFree.OrbitFrequencies
end
