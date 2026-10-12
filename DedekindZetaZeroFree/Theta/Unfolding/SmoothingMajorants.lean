module

public import DedekindZetaZeroFree.Theta.Unfolding.SheetIntegrability
public import DedekindZetaZeroFree.Theta.Unfolding.AbsoluteOrbitIntegration

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical ENNReal
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def smoothingMajorant {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) (t : PositiveAxis) : ℝ := by
  letI := C.transport.groupHaar_isHaar
  exact ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
    ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
      ‖C.packet.kernel t.val * digitWeight R m d *
        orbitFrequencyValue R C.sources C.realization v i
          (signedArgument R m b z.val d)‖
      ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar
        ⟨t.val / Z, div_pos t.property hZ⟩

theorem smoothingMajorant_nonneg {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) (t : PositiveAxis) :
    0 ≤ smoothingMajorant R C v m b Z hZ i t := by
  unfold smoothingMajorant
  exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))

theorem smoothingMajorant_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) :
    Integrable (smoothingMajorant R C v m b Z hZ i) positiveHaar := by
  letI := C.transport.groupHaar_isHaar
  exact integrable_finset_sum Finset.univ
    (fun d _ => C.absolute.orbit_smoothing_integrable v m b Z hZ i d)

theorem smoothingMajorant_integral_summable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun i : OrbitIndex R =>
      ∫ t, smoothingMajorant R C v m b Z hZ i t ∂positiveHaar) := by
  letI := C.transport.groupHaar_isHaar
  have he (i : OrbitIndex R) :
      (∫ t, smoothingMajorant R C v m b Z hZ i t ∂positiveHaar) =
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        ∫ t : PositiveAxis, ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
          ‖C.packet.kernel t.val * digitWeight R m d *
            orbitFrequencyValue R C.sources C.realization v i
              (signedArgument R m b z.val d)‖
          ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar
            ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar := by
    unfold smoothingMajorant
    exact integral_finset_sum _
      (fun d _ => C.absolute.orbit_smoothing_integrable v m b Z hZ i d)
  simp_rw [he]
  exact C.absolute.orbit_pregrouping v m b Z hZ

theorem mul_orbitSheet_integral_norm_le {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) (t : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    (∫ z, ‖C.packet.kernel t.val * orbitSheet R C v m b i
      ⟨t.val / Z, div_pos t.property hZ⟩ z‖
      ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar
        ⟨t.val / Z, div_pos t.property hZ⟩) ≤
      smoothingMajorant R C v m b Z hZ i t := by
  letI := C.transport.groupHaar_isHaar
  let l : PositiveAxis := ⟨t.val / Z, div_pos t.property hZ⟩
  let k := C.packet.kernel t.val
  have hc := (orbitSheet_integrable R C v m b i l).const_mul k
  have hd := (sheet_digit_majorant_integrable R C v m b i l).const_mul ‖k‖
  calc
    _ ≤ ∫ z : Sheet R.A l, ‖k‖ *
        ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
          ‖digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
            (signedArgument R m b z.val d)‖
        ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l := by
      apply integral_mono hc.norm hd
      intro z
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (orbitSheet_norm_le R C v m b i l z) (norm_nonneg k)
    _ = smoothingMajorant R C v m b Z hZ i t := by
      rw [integral_const_mul, integral_finset_sum _ (fun d _ =>
        C.absolute.orbit_sheet_integrable v m b i d l), Finset.mul_sum]
      unfold smoothingMajorant
      apply Finset.sum_congr rfl
      intro d _
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by simp only [k, norm_mul, mul_assoc])

theorem smoothingIntegrand_norm_le {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) (t : PositiveAxis) :
    ‖C.packet.kernel t.val * orbitIntegral R C v m b i
      ⟨t.val / Z, div_pos t.property hZ⟩‖ ≤
      smoothingMajorant R C v m b Z hZ i t := by
  letI := C.transport.groupHaar_isHaar
  rw [orbitIntegral, ← integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans
    (mul_orbitSheet_integral_norm_le R C v m b Z hZ i t)

theorem orbitTerm_norm_summable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun i : OrbitIndex R => ‖orbitTerm R C v m b Z hZ i‖) := by
  apply (smoothingMajorant_integral_summable R C v m b Z hZ).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro i
  exact norm_integral_le_of_norm_le
    (smoothingMajorant_integrable R C v m b Z hZ i)
    (Filter.Eventually.of_forall (smoothingIntegrand_norm_le R C v m b Z hZ i))

theorem smoothingIntegrand_hasFiniteIntegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) :
    HasFiniteIntegral (fun t : PositiveAxis => C.packet.kernel t.val *
      orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar := by
  exact (smoothingMajorant_integrable R C v m b Z hZ i).hasFiniteIntegral.mono
    (Filter.Eventually.of_forall (fun t =>
      (smoothingIntegrand_norm_le R C v m b Z hZ i t).trans (le_abs_self _)))

theorem smoothingIntegrand_integrable_of_aestronglyMeasurable
    {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R)
    (hm : AEStronglyMeasurable (fun t : PositiveAxis => C.packet.kernel t.val *
      orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar) :
    Integrable (fun t : PositiveAxis => C.packet.kernel t.val *
      orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar :=
  ⟨hm, smoothingIntegrand_hasFiniteIntegral R C v m b Z hZ i⟩

theorem smoothingMajorant_summable_ae {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) :
    ∀ᵐ t ∂positiveHaar, Summable (fun i : OrbitIndex R =>
      smoothingMajorant R C v m b Z hZ i t) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable Fˣ := Units.val_injective.countable
  letI : Countable (OrbitIndex R) := Countable.of_equiv Fˣ (orbitFrequencyEquiv R).symm
  exact AbsoluteIntegration.summable_majorant_ae
    (smoothingMajorant_integrable R C v m b Z hZ)
    (smoothingMajorant_nonneg R C v m b Z hZ)
    (smoothingMajorant_integral_summable R C v m b Z hZ)

theorem smoothingIntegrand_integral_norm_summable
    {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z)
    (hm : ∀ i, AEStronglyMeasurable (fun t : PositiveAxis => C.packet.kernel t.val *
      orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar) :
    Summable (fun i : OrbitIndex R => ∫ t : PositiveAxis,
      ‖C.packet.kernel t.val * orbitIntegral R C v m b i
        ⟨t.val / Z, div_pos t.property hZ⟩‖ ∂positiveHaar) := by
  apply (smoothingMajorant_integral_summable R C v m b Z hZ).of_nonneg_of_le
    (fun i => integral_nonneg (fun _ => norm_nonneg _))
  intro i
  exact integral_mono
    (smoothingIntegrand_integrable_of_aestronglyMeasurable R C v m b Z hZ i (hm i)).norm
    (smoothingMajorant_integrable R C v m b Z hZ i)
    (smoothingIntegrand_norm_le R C v m b Z hZ i)

end DedekindZetaZeroFree.OrbitExpansion

end
