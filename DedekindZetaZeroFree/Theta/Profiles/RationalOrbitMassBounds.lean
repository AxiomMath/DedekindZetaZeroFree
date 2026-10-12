module

public import DedekindZetaZeroFree.Theta.Profiles.GaussianSmoothing
public import DedekindZetaZeroFree.Theta.Unfolding.SmoothingMassFubini
public import DedekindZetaZeroFree.Theta.Profiles.UnmaskedAbsoluteSheetBounds
public import DedekindZetaZeroFree.Theta.Profiles.OrbitSheetMassBounds
public import DedekindZetaZeroFree.Theta.Unfolding.IntegralFrequencyMajorant

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma kernel_continuous (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (P : Packet R Q) : Continuous (fun t : PositiveAxis => P.kernel t.val) :=
  (thetaProfileGaussianKernel_continuousOn _ _ _ (GaussianSmoothing.C0_pos N P) P.A₀_pos
    (Fintype.card_pos_iff.mpr ⟨P.v₀⟩)).comp_continuous continuous_subtype_val (fun t => t.property)

lemma kernel_square_moment_integrable (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (P : Packet R Q) : Integrable (fun t : PositiveAxis => ‖P.kernel t.val‖ * t.val ^ 2) positiveHaar := by
  have hi := thetaProfileGaussianKernel_absolute_moment P.C₀ P.A₀ (Fintype.card (InfinitePlace F))
    (GaussianSmoothing.C0_pos N P) P.A₀_pos (Fintype.card_pos_iff.mpr ⟨P.v₀⟩) 2
  let f : ℝ → ℝ := fun t => ‖P.kernel t‖ * t ^ 2
  have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  change Integrable (f ∘ Subtype.val) positiveHaar
  rw [← he.integrable_map_iff, positiveHaar_map_val, restrict_withDensity measurableSet_Ioi,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le), smul_eq_mul, f, Packet.kernel,
    div_eq_mul_inv]
  change ‖thetaProfileGaussianKernel P.C₀ P.A₀ (Fintype.card (InfinitePlace F)) t‖ * (t ^ (2 : ℝ)) * t⁻¹ = _
  rw [Real.rpow_two]
  ring
lemma kernel_inverse_square_moment_integrable (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (P : Packet R Q) : Integrable (fun t : PositiveAxis => ‖P.kernel t.val‖ * (t.val ^ 2)⁻¹) positiveHaar := by
  have hi := thetaProfileGaussianKernel_absolute_moment P.C₀ P.A₀ (Fintype.card (InfinitePlace F))
    (GaussianSmoothing.C0_pos N P) P.A₀_pos (Fintype.card_pos_iff.mpr ⟨P.v₀⟩) (-2)
  let f : ℝ → ℝ := fun t => ‖P.kernel t‖ * (t ^ 2)⁻¹
  have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  change Integrable (f ∘ Subtype.val) positiveHaar
  rw [← he.integrable_map_iff, positiveHaar_map_val, restrict_withDensity measurableSet_Ioi,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le), smul_eq_mul, f, Packet.kernel,
    div_eq_mul_inv]
  change ‖thetaProfileGaussianKernel P.C₀ P.A₀ (Fintype.card (InfinitePlace F)) t‖ * (t ^ (-2 : ℝ)) * t⁻¹ = _
  rw [Real.rpow_neg ht.le, Real.rpow_two]
  ring
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MeasureTheory
open scoped Classical

lemma dominated_nonnegative_series {X I : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : I → X → ℝ) (g : X → ℝ)
    (hf : ∀ i x, 0 ≤ f i x) (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (hs : ∀ x, Summable (fun i => f i x))
    (hb : ∀ x, (∑' i, f i x) ≤ g x) (hg : Integrable g μ) :
    (∀ i, Integrable (f i) μ) ∧ Summable (fun i => ∫ x, f i x ∂μ) := by
  have hi : ∀ i, Integrable (f i) μ := by
    intro i
    apply hg.mono' (hm i)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf i x)]
    exact (Summable.le_tsum (hs x) i (fun j _ => hf j x)).trans (hb x)
  refine ⟨hi, ?_⟩
  apply summable_of_sum_le (fun i => integral_nonneg (hf i))
  intro s
  rw [← integral_finsetSum s (fun i _ => hi i)]
  apply integral_mono (integrable_finsetSum s (fun i _ => hi i)) hg
  intro x
  exact (Summable.sum_le_tsum s (fun i _ => hf i x) (hs x)).trans (hb x)
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

lemma gamma_unit (γ : ThetaReflectionData.rationalGamma R.A) : γ.val ∈ R.A.U := by
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp γ.property
  rw [← he]
  exact R.A.U.pow_mem hu 6

lemma gamma_integral_iff (γ : ThetaReflectionData.rationalGamma R.A) (a : Fˣ) :
    ((a * γ.val : Fˣ) : F) ∈ R.A.R ↔ (a : F) ∈ R.A.R := by
  change (∀ p, p ∉ R.A.Sf → p.valuation F ((a * γ.val : Fˣ) : F) ≤ 1) ↔ _
  simp only [Units.val_mul, map_mul]
  have he (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) : p.valuation F (γ.val : F) = 1 :=
    gamma_unit R γ p hp
  constructor
  · intro h p hp
    simpa only [he p hp, mul_one] using h p hp
  · intro h p hp
    simpa only [he p hp, mul_one] using h p hp

theorem unmasked_orbit_sheet_mass (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (H : SameResidueProfiles R Q T P) (v : R.A.UnitQuotient) (a : Fˣ) (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    Summable (fun γ : ThetaReflectionData.rationalGamma R.A =>
      ∫ y : Sheet R.A l, ‖fourier R Q.dq (T.theta v)
        (diagonal R (R.A.diagonal (γ.val * a) / y.val) *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)‖
        ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar l) ∧
    (∑' γ : ThetaReflectionData.rationalGamma R.A,
      ∫ y : Sheet R.A l, ‖fourier R Q.dq (T.theta v)
        (diagonal R (R.A.diagonal (γ.val * a) / y.val) *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)‖
        ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar l) =
    ∫ y : Sheet R.A (q R.A a / l), ‖fourier R Q.dq (T.theta v)
      (diagonal R y.val * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)‖
      ∂sheetHaar R.A P.v₀ N.groupHaar (q R.A a / l) := by
  letI := N.groupHaar_isHaar
  let f : R.A.G → ℂ := fun y => fourier R Q.dq (T.theta v)
    (diagonal R y * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)
  have hf := unmasked_full_sheet_integrable R N T P H v (q R.A a / l)
  have hu := integral_div_unfold R.A P.v₀ N.groupHaar a l
    (pregroupingSheet R.A P.v₀ l) (pregroupingSheet_fundamental R.A P.v₀ N.groupHaar l)
    (fun y => (‖f y‖ : ℂ)) (Complex.ofRealCLM.integrable_comp hf.norm)
  have hs := hu.1.map Complex.reCLM Complex.reCLM.continuous
  simp only [Function.comp_def, integral_complex_ofReal, Complex.reCLM_apply,
    Complex.ofReal_re] at hs
  refine ⟨?_, ?_⟩
  · have h := hs.comp_injective (gammaEquiv R).injective
    simpa only [Function.comp_def, gammaEquiv_val, ← map_mul, pregroupingSheetHaar, f] using h
  · have ht := (gammaEquiv R).toEquiv.tsum_eq (fun γ : R.A.Gamma1 =>
      ∫ y in pregroupingSheet R.A P.v₀ l,
        ‖f (γ.val.val * R.A.diagonal a / y.val)‖ ∂sheetHaar R.A P.v₀ N.groupHaar l)
    have hc := hu.1.hasSum.map Complex.reCLM Complex.reCLM.continuous
    rw [hu.2] at hc
    have hv : (∑' γ : R.A.Gamma1, ∫ y in pregroupingSheet R.A P.v₀ l,
        ‖f (γ.val.val * R.A.diagonal a / y.val)‖ ∂sheetHaar R.A P.v₀ N.groupHaar l) =
        ∫ y : Sheet R.A (q R.A a / l), ‖f y.val‖ ∂sheetHaar R.A P.v₀ N.groupHaar (q R.A a / l) := by
      simpa only [Function.comp_def, integral_complex_ofReal, Complex.reCLM_apply,
        Complex.ofReal_re] using hc.tsum_eq
    have hval (γ : ThetaReflectionData.rationalGamma R.A) :
        ((gammaEquiv R).toEquiv γ).val.val = R.A.diagonal γ.val := rfl
    simpa only [hval, ← map_mul, pregroupingSheetHaar, f] using ht.trans hv

lemma orbit_reverse_zero_off_support {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (v : R.A.UnitQuotient) (ξ : ThetaReflectionData.Frequency R.A)
    (γ : ThetaReflectionData.rationalGamma R.A) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m))
    (h : ((ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ : Fˣ) : F) ∉ R.A.R) :
    orbitFrequencyValue R Q T v (ξ, γ) (signedArgument R m false y d) = 0 := by
  apply norm_eq_zero.mp
  rw [orbit_reverse_norm R D]
  have he : digitExterior R D m (Quotient.out ξ * γ.val) d = 0 := by
    by_contra hn
    have hi := digitExterior_row_square_integral R D E m _ d hn
    rw [← mul_assoc] at hi
    exact h ((gamma_integral_iff R γ _).mp hi)
  change ‖digitExterior R D m (Quotient.out ξ * γ.val) d‖ * _ = 0
  rw [he, norm_zero, zero_mul]
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
def orbitMass (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (ξ : ThetaReflectionData.Frequency R.A)
    (γ : ThetaReflectionData.rationalGamma R.A) (d : ThetaDigitAverage.Dig (RowPrime R m))
    (l : PositiveAxis) : ℝ := by
  letI := N.groupHaar_isHaar
  exact ∫ y : Sheet R.A l, ‖orbitFrequencyValue R Q T v (ξ, γ)
    (signedArgument R m b y.val d)‖ ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar l
lemma orbitMass_nonneg (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) b ξ γ d l : 0 ≤ orbitMass R N T P v m b ξ γ d l := by
  unfold orbitMass
  exact integral_nonneg (fun _ => norm_nonneg _)
lemma sheet_coordinates_continuous (w : InfinitePlace F) (Z : ℝ) (hZ : 0 < Z) :
    Continuous (fun p : PositiveAxis × R.A.G1 =>
      (sheetTranslation R.A w ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val) := by
  have ht : Continuous (fun p : PositiveAxis × R.A.G1 =>
      (⟨p.1.val / Z, div_pos p.1.property hZ⟩ : PositiveAxis)) :=
    ((continuous_subtype_val.comp continuous_fst).div_const Z).subtype_mk _
  change Continuous (fun p : PositiveAxis × R.A.G1 =>
    normSection R.A w ⟨p.1.val / Z, div_pos p.1.property hZ⟩ * p.2.val)
  have he : (fun p : PositiveAxis × R.A.G1 =>
    normSection R.A w ⟨p.1.val / Z, div_pos p.1.property hZ⟩ * p.2.val) =
    (normSplit R.A w) ∘ (fun p => (⟨p.1.val / Z, div_pos p.1.property hZ⟩, p.2)) := rfl
  rw [he]
  exact (normSplit R.A w).continuous.comp (ht.prodMk continuous_snd)
end DedekindZetaZeroFree.OrbitFrequencies
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma orbitMass_measurable (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) b ξ γ d (Z : ℝ) (hZ : 0 < Z) :
    StronglyMeasurable (fun t : PositiveAxis =>
      orbitMass R N T P v m b ξ γ d ⟨t.val / Z, div_pos t.property hZ⟩) := by
  letI := N.groupHaar_isHaar
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  have hc : Continuous (fun p : PositiveAxis × R.A.G1 =>
      orbitFrequencyValue R Q T v (ξ, γ) (signedArgument R m b
        (sheetTranslation R.A P.v₀ ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val d)) :=
    (orbitFrequencyValue_continuous R T v (ξ, γ)).comp
      ((DigitMasks.signedArgument_continuous R m b d).comp (sheet_coordinates_continuous R P.v₀ Z hZ))
  have he (t : PositiveAxis) : orbitMass R N T P v m b ξ γ d
      ⟨t.val / Z, div_pos t.property hZ⟩ =
      ∫ z : R.A.G1, ‖orbitFrequencyValue R Q T v (ξ, γ) (signedArgument R m b
        (sheetTranslation R.A P.v₀ ⟨t.val / Z, div_pos t.property hZ⟩ z).val d)‖
        ∂((kernelHaar R.A P.v₀ N.groupHaar).restrict (pregroupingDomain R.A).carrier) := by
    unfold orbitMass
    rw [pregroupingSheetHaar_eq_map,
      (sheetTranslation R.A P.v₀ ⟨t.val / Z, div_pos t.property hZ⟩).measurableEmbedding.integral_map]
  simp_rw [he]
  exact hc.norm.stronglyMeasurable.integral_prod_right'

lemma orbit_product_continuous (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) b ξ γ d (Z : ℝ) (hZ : 0 < Z) :
    Continuous (fun p : PositiveAxis × R.A.G1 =>
      P.kernel p.1.val * digitWeight R m d * orbitFrequencyValue R Q T v (ξ, γ)
        (signedArgument R m b
          (sheetTranslation R.A P.v₀ ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val d)) :=
  (((kernel_continuous R N P).comp continuous_fst).mul continuous_const).mul
    ((orbitFrequencyValue_continuous R T v (ξ, γ)).comp
      ((DigitMasks.signedArgument_continuous R m b d).comp (sheet_coordinates_continuous R P.v₀ Z hZ)))

lemma orbitMass_reverse_bound (N : TraceHaarTransport R) {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (v : R.A.UnitQuotient) (ξ : ThetaReflectionData.Frequency R.A)
    (γ : ThetaReflectionData.rationalGamma R.A) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    orbitMass R N T P v m false ξ γ d l ≤
      ∫ y : Sheet R.A l, ‖fourier R Q.dq (T.theta v)
        (diagonal R (R.A.diagonal (γ.val * Quotient.out ξ) / y.val) *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)‖
        ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar l := by
  letI := N.groupHaar_isHaar
  have hi : Integrable (fun y : Sheet R.A l => orbitFrequencyValue R Q T v (ξ, γ)
      (signedArgument R m false y.val d)) (pregroupingSheetHaar R.A P.v₀ N.groupHaar l) :=
    continuous_pregroupingSheet_integrable R N P.v₀ l _
      ((orbitFrequencyValue_continuous R T v (ξ, γ)).comp
        ((DigitMasks.signedArgument_continuous R m false d).comp continuous_subtype_val))
  have hj : Integrable (fun y : Sheet R.A l => fourier R Q.dq (T.theta v)
      (diagonal R (R.A.diagonal (γ.val * Quotient.out ξ) / y.val) *
        KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12))
      (pregroupingSheetHaar R.A P.v₀ N.groupHaar l) := by
    apply continuous_pregroupingSheet_integrable R N P.v₀ l
    exact (SheetRescaling.fourier_continuous T v).comp
      (((DigitMasks.diagonal_selected_continuous R).comp
        (continuous_const.div' continuous_subtype_val)).mul continuous_const)
  apply integral_mono hi.norm hj.norm
  intro y
  dsimp only
  rw [orbit_reverse_norm R D, mul_comm (Quotient.out ξ) γ.val]
  change ‖digitExterior R D m (γ.val * Quotient.out ξ) d‖ * _ ≤ _
  exact mul_le_of_le_one_left (norm_nonneg _) (digitExterior_norm_le_one R D E m _ d)

theorem orbitMass_reverse_summable_bound (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (H : SameResidueProfiles R Q T P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v m ξ d (l : PositiveAxis),
      Summable (fun γ => orbitMass R N T P v m false ξ γ d l) ∧
      (∑' γ, orbitMass R N T P v m false ξ γ d l) ≤ K * l.val ^ 2 * frequencyMajorant R m ξ := by
  obtain ⟨K, hK, hb⟩ := unmasked_full_sheet_norm_bound R N T P H 2 (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro v m ξ d l
  letI := N.groupHaar_isHaar
  by_cases hx : ((ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ : Fˣ) : F) ∈ R.A.R
  · have hs := unmasked_orbit_sheet_mass R N T P H v (Quotient.out ξ) l
    have ht : Summable (fun γ => orbitMass R N T P v m false ξ γ d l) :=
      Summable.of_nonneg_of_le (fun γ => orbitMass_nonneg R N T P v m false ξ γ d l)
        (fun γ => orbitMass_reverse_bound R N T P D E v ξ γ m d l) hs.1
    refine ⟨ht, ?_⟩
    have hle := Summable.tsum_le_tsum
      (fun γ => orbitMass_reverse_bound R N T P D E v ξ γ m d l) ht hs.1
    rw [hs.2] at hle
    have hn : (q R.A (Quotient.out ξ)).val = ThetaReflectionData.frequencyNorm R.A ξ := by
      have he := ThetaReflectionData.frequencyNorm_mk R.A (Quotient.out ξ)
      simpa only [Quotient.out_eq, q] using he.symm
    refine hle.trans ((hb v (q R.A (Quotient.out ξ) / l)).trans ?_)
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hK).trans_eq
    simp only [frequencyMajorant, ite_eq_left hx]
    change K * (((q R.A (Quotient.out ξ)).val / l.val) ^ (-2 : ℝ)) = _
    rw [hn]
    rw [Real.rpow_neg (div_pos (ThetaReflectionData.frequencyNorm_pos R.A ξ) l.property).le, Real.rpow_two]
    simp only [zpow_neg, zpow_ofNat, div_pow, inv_div]
    ring
  · have he (γ : ThetaReflectionData.rationalGamma R.A) : orbitMass R N T P v m false ξ γ d l = 0 := by
      unfold orbitMass
      simp only [orbit_reverse_zero_off_support R D E v ξ γ _ m d hx, norm_zero, integral_zero]
    simp only [he, tsum_zero, frequencyMajorant, ite_eq_right hx, mul_zero, le_refl]
    exact ⟨summable_zero, trivial⟩
end DedekindZetaZeroFree.OrbitFrequencies
end
