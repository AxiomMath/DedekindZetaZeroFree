module

public import DedekindZetaZeroFree.Theta.Unfolding.OrbitExtractionDefinitions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem quotientNonconstant_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool) (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    Integrable (fun z => quotientTheta R C.sources C.realization C.packet v m b l z -
      quotientUpper R C.sources C.realization C.packet v m b l z)
      (sheetQuotientHaar R.A C.packet.v₀ C.transport.groupHaar l) := by
  letI := C.transport.groupHaar_isHaar
  exact (C.descent.theta_integrable v m b l).sub (C.descent.upper_integrable v m b l)

theorem thetaAverage_sub_upperAverage {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool) (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    thetaAverage R C.transport C.sources C.realization C.packet v m b l -
      upperAverage R C.transport C.sources C.realization C.packet v m b l =
    ∫ z, (quotientTheta R C.sources C.realization C.packet v m b l z -
      quotientUpper R C.sources C.realization C.packet v m b l z)
      ∂sheetQuotientHaar R.A C.packet.v₀ C.transport.groupHaar l := by
  letI := C.transport.groupHaar_isHaar
  exact (integral_sub (C.descent.theta_integrable v m b l)
    (C.descent.upper_integrable v m b l)).symm

theorem smoothedTheta_sub_mainTerm {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z)
    (hi : Integrable (fun t : PositiveAxis => C.packet.kernel t.val *
      thetaAverage R C.transport C.sources C.realization C.packet v m b
        ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar) :
    smoothedTheta R C.transport C.sources C.realization C.packet v m b Z -
      mainTerm R C.transport C.sources C.realization C.packet v m b Z =
    ∫ t : PositiveAxis, C.packet.kernel t.val *
      (thetaAverage R C.transport C.sources C.realization C.packet v m b
        ⟨t.val / Z, div_pos t.property hZ⟩ -
       upperAverage R C.transport C.sources C.realization C.packet v m b
        ⟨t.val / Z, div_pos t.property hZ⟩) ∂positiveHaar := by
  rw [smoothedTheta, mainTerm, dif_pos hZ, dif_pos hZ]
  simp_rw [mul_sub]
  exact (integral_sub hi (C.descent.smoothing_integrable v m b Z hZ)).symm

theorem thetaAverage_sub_upperAverage_domain {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool) (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    thetaAverage R C.transport C.sources C.realization C.packet v m b l -
      upperAverage R C.transport C.sources C.realization C.packet v m b l =
    ∫ z : Sheet R.A l, (weightedDigits R C.sources C.realization C.packet v m b z.val -
      weightedUpper R C.sources C.realization C.packet v m b z.val)
      ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l := by
  letI := C.transport.groupHaar_isHaar
  rw [thetaAverage_sub_upperAverage,
    pregroupingSheet_integral R.A C.packet.v₀ C.transport.groupHaar l _
      (quotientNonconstant_integrable R C v m b l)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [C.descent.quotientTheta_projection R]
  congr 1
  unfold quotientUpper
  have h := Quotient.exact (Quotient.out_eq (sheetProjection R.A l y))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  have hv := congrArg Subtype.val hγ
  change γ.val.val * y.val = (Quotient.out (sheetProjection R.A l y)).val at hv
  rw [← hv]
  exact C.descent.weighted_upper_descent v m b ⟨γ.val.val, γ.property⟩ _

end DedekindZetaZeroFree.OrbitExpansion

end
