module

public import DedekindZetaZeroFree.Theta.Profiles.RationalOrbitMassBounds

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma orbitMass_reverse_joint_bound (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (H : SameResidueProfiles R Q T P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v m d (l : PositiveAxis),
      Summable (fun i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A =>
        orbitMass R N T P v m false i.1 i.2 d l) ∧
      (∑' i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A,
        orbitMass R N T P v m false i.1 i.2 d l) ≤
        K * l.val ^ 2 * (∑' ξ, frequencyMajorant R m ξ) := by
  obtain ⟨K, hK, hb⟩ := orbitMass_reverse_summable_bound R N T P D E H
  refine ⟨K, hK, ?_⟩
  intro v m d l
  have hξ : Summable (fun ξ => ∑' γ, orbitMass R N T P v m false ξ γ d l) :=
    Summable.of_nonneg_of_le (fun ξ => tsum_nonneg (fun γ => orbitMass_nonneg R N T P v m false ξ γ d l))
      (fun ξ => (hb v m ξ d l).2) ((frequencyMajorant_summable R m).mul_left (K * l.val ^ 2))
  have hs := (summable_prod_of_nonneg (fun i => orbitMass_nonneg R N T P v m false i.1 i.2 d l)).mpr
    ⟨fun ξ => (hb v m ξ d l).1, hξ⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun ξ => (hb v m ξ d l).2) hξ
    ((frequencyMajorant_summable R m).mul_left (K * l.val ^ 2))

lemma orbitMass_reverse_smoothed (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (H : SameResidueProfiles R Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) (Z : ℝ) (hZ : 0 < Z) :
    (∀ i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A,
      Integrable (fun t : PositiveAxis => ‖P.kernel t.val‖ * ‖digitWeight R m d‖ *
        orbitMass R N T P v m false i.1 i.2 d ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar) ∧
    Summable (fun i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A =>
      ∫ t : PositiveAxis, ‖P.kernel t.val‖ * ‖digitWeight R m d‖ *
        orbitMass R N T P v m false i.1 i.2 d ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar) := by
  obtain ⟨K, hK, hb⟩ := orbitMass_reverse_joint_bound R N T P D E H
  let C : ℝ := ‖digitWeight R m d‖ * K / Z ^ 2 * (∑' ξ, frequencyMajorant R m ξ)
  apply dominated_nonnegative_series
    (g := fun t : PositiveAxis => C * (‖P.kernel t.val‖ * t.val ^ 2))
  · intro i t
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (orbitMass_nonneg R N T P _ _ _ _ _ _ _)
  · intro i
    exact (((kernel_continuous R N P).norm.stronglyMeasurable.mul stronglyMeasurable_const).mul
      (orbitMass_measurable R N T P v m false i.1 i.2 d Z hZ)).aestronglyMeasurable
  · intro t
    exact ((hb v m d ⟨t.val / Z, div_pos t.property hZ⟩).1).mul_left _
  · intro t
    rw [tsum_mul_left]
    have h := mul_le_mul_of_nonneg_left ((hb v m d ⟨t.val / Z, div_pos t.property hZ⟩).2)
      (mul_nonneg (norm_nonneg (P.kernel t.val)) (norm_nonneg (digitWeight R m d)))
    refine h.trans_eq ?_
    dsimp only [C]
    field_simp
  · exact (kernel_square_moment_integrable R N P).const_mul C

lemma orbitMass_weighted_eq (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) b i d
    (t : PositiveAxis) (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    (∫ y : Sheet R.A l, ‖P.kernel t.val * digitWeight R m d *
      orbitFrequencyValue R Q T v i (signedArgument R m b y.val d)‖
      ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar l) =
      ‖P.kernel t.val‖ * ‖digitWeight R m d‖ * orbitMass R N T P v m b i.1 i.2 d l := by
  letI := N.groupHaar_isHaar
  simp only [norm_mul, ← integral_const_mul, orbitMass]

theorem reverse_orbit_product_integrable (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (H : SameResidueProfiles R Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) Z (hZ : 0 < Z)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (d : ThetaDigitAverage.Dig (RowPrime R m)) :
    letI := N.groupHaar_isHaar;
    Integrable (fun p : PositiveAxis × R.A.G1 =>
      P.kernel p.1.val * digitWeight R m d * orbitFrequencyValue R Q T v i
        (signedArgument R m false (sheetTranslation R.A P.v₀
          ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val d))
      (positiveHaar.prod ((kernelHaar R.A P.v₀ N.groupHaar).restrict (pregroupingDomain R.A).carrier)) := by
  letI := N.groupHaar_isHaar
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  apply (integrable_prod_iff (orbit_product_continuous R N T P v m false i.1 i.2 d Z hZ).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with t
    have hc : Continuous (fun y : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩ =>
      P.kernel t.val * digitWeight R m d * orbitFrequencyValue R Q T v i (signedArgument R m false y.val d)) :=
      continuous_const.mul ((orbitFrequencyValue_continuous R T v i).comp
        ((DigitMasks.signedArgument_continuous R m false d).comp continuous_subtype_val))
    have hi := continuous_pregroupingSheet_integrable R N P.v₀ _ _ hc
    rw [pregroupingSheetHaar_eq_map] at hi
    exact (sheetTranslation R.A P.v₀ _).measurableEmbedding.integrable_map_iff.mp hi
  · have hi := (orbitMass_reverse_smoothed R N T P D E H v m d Z hZ).1 i
    have he (t : PositiveAxis) := (sheet_mass_coordinates R N P.v₀
      ⟨t.val / Z, div_pos t.property hZ⟩ (fun y =>
        P.kernel t.val * digitWeight R m d * orbitFrequencyValue R Q T v i (signedArgument R m false y.val d))).symm
    simp_rw [he, orbitMass_weighted_eq R N T P]
    exact hi

theorem reverse_orbit_pregrouping (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)
    (H : SameResidueProfiles R Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) Z (hZ : 0 < Z) :
    letI := N.groupHaar_isHaar;
    Summable (fun i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A =>
      ∑ d : ThetaDigitAverage.Dig (RowPrime R m),
        ∫ t : PositiveAxis, ∫ y : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
          ‖P.kernel t.val * digitWeight R m d * orbitFrequencyValue R Q T v i
            (signedArgument R m false y.val d)‖
          ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar) := by
  letI := N.groupHaar_isHaar
  simp_rw [orbitMass_weighted_eq R N T P]
  exact summable_sum (fun d _ => (orbitMass_reverse_smoothed R N T P D E H v m d Z hZ).2)
end DedekindZetaZeroFree.OrbitFrequencies
end
