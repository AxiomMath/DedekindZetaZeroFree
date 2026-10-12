module

public import DedekindZetaZeroFree.Theta.Unfolding.AbsoluteOrbitRegrouping

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma branch_norm {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ‖P.branch v y‖ = 1 := by
  rw [P.branch_global, norm_mul, Circle.norm_coe, one_mul]
  apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by decide)
  rw [← map_pow]
  have h := congrArg (fun u : Fˣ => (u : F))
    (R.A.H_S (R.A.diagonal (R.probe.unitReps.representative v).val) y).property
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_one] using congrArg R.σ h

lemma smoothing_orbitSheet_norm_le {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) (z : Sheet R.A l) (k : ℂ) :
    ‖k * orbitSheet R C v m b i l z‖ ≤
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        ‖k * digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
          (signedArgument R m b z.val d)‖ := by
  unfold orbitSheet
  split_ifs
  · simp only [one_mul, norm_mul, norm_inv, branch_norm R C.packet, inv_one, one_mul]
    calc
      _ ≤ ‖k‖ * ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
          ‖digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
            (signedArgument R m b z.val d)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = _ := by simp only [Finset.mul_sum, norm_mul, mul_assoc]
  · simp only [zero_mul, mul_zero, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

def orbitMass {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) (t : PositiveAxis) : ℝ := by
  letI := C.transport.groupHaar_isHaar
  exact ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
    ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
      ‖C.packet.kernel t.val * digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
        (signedArgument R m b z.val d)‖
      ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩

lemma orbitMass_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) :
    Integrable (orbitMass R C v m b Z hZ i) positiveHaar := by
  letI := C.transport.groupHaar_isHaar
  exact integrable_finset_sum _ (fun d _ => C.absolute.orbit_smoothing_integrable v m b Z hZ i d)

lemma orbitMass_integral_summable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun i : OrbitIndex R => ∫ t, orbitMass R C v m b Z hZ i t ∂positiveHaar) := by
  letI := C.transport.groupHaar_isHaar
  have he (i : OrbitIndex R) : (∫ t, orbitMass R C v m b Z hZ i t ∂positiveHaar) =
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        ∫ t : PositiveAxis, ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
          ‖C.packet.kernel t.val * digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
            (signedArgument R m b z.val d)‖
          ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩
          ∂positiveHaar := by
    unfold orbitMass
    exact integral_finset_sum _ (fun d _ => C.absolute.orbit_smoothing_integrable v m b Z hZ i d)
  simp_rw [he]
  exact C.absolute.orbit_pregrouping v m b Z hZ

lemma smoothed_orbit_norm_le {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z)
    (i : OrbitIndex R) (t : PositiveAxis) :
    ‖C.packet.kernel t.val * orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩‖ ≤
      orbitMass R C v m b Z hZ i t := by
  letI := C.transport.groupHaar_isHaar
  let l : PositiveAxis := ⟨t.val / Z, div_pos t.property hZ⟩
  let μ := pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l
  have hi := ((hx v m b Z hZ).1 i l).const_mul (C.packet.kernel t.val)
  have hd (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
      Integrable (fun z : Sheet R.A l =>
        ‖C.packet.kernel t.val * digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
          (signedArgument R m b z.val d)‖) μ := by
    simpa only [norm_mul, mul_assoc] using
      (C.absolute.orbit_sheet_integrable v m b i d l).const_mul ‖C.packet.kernel t.val‖
  change ‖C.packet.kernel t.val * ∫ z, orbitSheet R C v m b i l z ∂μ‖ ≤ _
  rw [← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hm := integral_mono hi.norm (integrable_finset_sum _ (fun d _ => hd d))
    (fun z => smoothing_orbitSheet_norm_le R C v m b i l z (C.packet.kernel t.val))
  exact hm.trans_eq (integral_finset_sum _ (fun d _ => hd d))

theorem smoothed_orbit_integral_norm_summable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun i : OrbitIndex R => ∫ t : PositiveAxis,
      ‖C.packet.kernel t.val * orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩‖
      ∂positiveHaar) := by
  apply (orbitMass_integral_summable R C v m b Z hZ).of_nonneg_of_le
  · intro i
    exact integral_nonneg (fun _ => norm_nonneg _)
  · intro i
    exact integral_mono ((hx v m b Z hZ).2.1 i).norm
      (orbitMass_integrable R C v m b Z hZ i)
      (smoothed_orbit_norm_le R C hx v m b Z hZ i)

theorem groupedOrbitTerm_eq_integral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z)
    (ξ : ThetaReflectionData.Frequency R.A) :
    groupedOrbitTerm R C v m b Z hZ ξ =
      ∫ t : PositiveAxis, C.packet.kernel t.val *
        (∑' γ : ThetaReflectionData.rationalGamma R.A,
          orbitIntegral R C v m b (ξ, γ) ⟨t.val / Z, div_pos t.property hZ⟩) ∂positiveHaar := by
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable Fˣ := Units.val_injective.countable
  have hs := (smoothed_orbit_integral_norm_summable R C hx v m b Z hZ).prod_factor ξ
  have hi := integral_tsum_of_summable_integral_norm
    (fun γ => (hx v m b Z hZ).2.1 (ξ, γ)) hs
  change (∑' γ : ThetaReflectionData.rationalGamma R.A,
    ∫ t : PositiveAxis, C.packet.kernel t.val *
      orbitIntegral R C v m b (ξ, γ) ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar) = _
  simpa only [tsum_mul_left] using hi

end DedekindZetaZeroFree.OrbitExpansion

end
