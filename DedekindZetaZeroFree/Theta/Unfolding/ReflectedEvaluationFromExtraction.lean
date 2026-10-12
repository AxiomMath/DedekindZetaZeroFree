module

public import DedekindZetaZeroFree.Theta.Unfolding.AbsoluteOrbitSmoothing

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

theorem reverse_sheet_pregrouping {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x : Fˣ) (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    Summable (fun γ : ThetaReflectionData.rationalGamma R.A =>
      ∫ y : Sheet R.A l, ‖reverseSheetWord R C.realization C.packet v x γ y.val‖
        ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) ∧
    (∑' γ : ThetaReflectionData.rationalGamma R.A,
      ∫ y : Sheet R.A l, reverseSheetWord R C.realization C.packet v x γ y.val
        ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) =
      (Characters.L R v x)⁻¹ * C.realization.sheet C.packet v
        (ThetaReflectionData.rationalClass R.A x) (q R.A x / l) := by
  letI := C.transport.groupHaar_isHaar
  exact reverse_sheet_orbit R C v x l (pregroupingSheet R.A C.packet.v₀ l)
    (pregroupingSheet_fundamental R.A C.packet.v₀ C.transport.groupHaar l)

theorem exterior_sheet_pregrouping {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (ξ : ThetaReflectionData.Frequency R.A) (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    (∀ γ : ThetaReflectionData.rationalGamma R.A, Integrable
      (fun y : Sheet R.A l => exteriorDigitCoefficient R C m (Quotient.out ξ) *
        reverseSheetWord R C.realization C.packet v (Quotient.out ξ) γ y.val)
      (pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l)) ∧
    Summable (fun γ : ThetaReflectionData.rationalGamma R.A =>
      ∫ y : Sheet R.A l, ‖exteriorDigitCoefficient R C m (Quotient.out ξ) *
        reverseSheetWord R C.realization C.packet v (Quotient.out ξ) γ y.val‖
        ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) ∧
    (∑' γ : ThetaReflectionData.rationalGamma R.A,
      ∫ y : Sheet R.A l, exteriorDigitCoefficient R C m (Quotient.out ξ) *
        reverseSheetWord R C.realization C.packet v (Quotient.out ξ) γ y.val
        ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) =
      exteriorDigitCoefficient R C m (Quotient.out ξ) * (Characters.L R v (Quotient.out ξ))⁻¹ *
        C.realization.sheet C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
          (q R.A (Quotient.out ξ) / l) := by
  letI := C.transport.groupHaar_isHaar
  have h := reverse_sheet_pregrouping R C v (Quotient.out ξ) l
  refine ⟨?_, ?_, ?_⟩
  · intro γ
    exact ((reverse_sheet_word_integrable R C v (Quotient.out ξ) γ l).restrict).const_mul _
  · simp only [norm_mul, integral_const_mul]
    exact h.1.mul_left _
  · simp only [integral_const_mul, tsum_mul_left]
    rw [h.2, frequencyClass_out R ξ, mul_assoc]

theorem orbitIntegral_fiber_eq_of_extraction {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (Z : ℝ) (hZ : 0 < Z)
    (ξ : ThetaReflectionData.Frequency R.A) (l : PositiveAxis)
    (hextract : letI := C.transport.groupHaar_isHaar;
      ∀ γ : ThetaReflectionData.rationalGamma R.A,
        orbitSheet R C v m false (ξ, γ) l =ᵐ[
          pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l]
          (fun y => exteriorDigitCoefficient R C m (Quotient.out ξ) *
            reverseSheetWord R C.realization C.packet v (Quotient.out ξ) γ y.val)) :
    Summable (fun γ : ThetaReflectionData.rationalGamma R.A =>
      ‖orbitIntegral R C v m false (ξ, γ) l‖) ∧
    (∑' γ : ThetaReflectionData.rationalGamma R.A, orbitIntegral R C v m false (ξ, γ) l) =
      exteriorDigitCoefficient R C m (Quotient.out ξ) * (Characters.L R v (Quotient.out ξ))⁻¹ *
        C.realization.sheet C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
          (q R.A (Quotient.out ξ) / l) := by
  letI := C.transport.groupHaar_isHaar
  have hs := exterior_sheet_pregrouping R C v m ξ l
  have he (γ : ThetaReflectionData.rationalGamma R.A) :
      orbitIntegral R C v m false (ξ, γ) l =
        ∫ y : Sheet R.A l, exteriorDigitCoefficient R C m (Quotient.out ξ) *
          reverseSheetWord R C.realization C.packet v (Quotient.out ξ) γ y.val
          ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l := by
    have hi := (hx v m false Z hZ).1 (ξ, γ) l
    have hj := hs.1 γ
    exact integral_congr_ae (hextract γ)
  simp_rw [he]
  exact ⟨hs.2.1.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _),
    hs.2.2⟩

theorem reverse_orbit_evaluation_of_pointwise_extraction {N : TraceHaarTransport R}
    (C : JointUpperVanishingSources R N) (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (Z : ℝ) (hZ : 0 < Z)
    (hextract : letI := C.transport.groupHaar_isHaar;
      ∀ (ξ : ThetaReflectionData.Frequency R.A) (γ : ThetaReflectionData.rationalGamma R.A)
        (l : PositiveAxis), orbitSheet R C v m false (ξ, γ) l =ᵐ[
          pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l]
          (fun y => exteriorDigitCoefficient R C m (Quotient.out ξ) *
            reverseSheetWord R C.realization C.packet v (Quotient.out ξ) γ y.val)) :
    Summable (fun ξ => ‖actualReflectedTerm R C v m Z ξ‖) ∧
    HasSum (actualReflectedTerm R C v m Z)
      (∑' i : OrbitIndex R, orbitTerm R C v m false Z hZ i) := by
  apply reverse_orbit_evaluation_of_fiber_identity R C hx v m Z hZ
  intro ξ
  rw [groupedOrbitTerm_eq_integral R C hx v m false Z hZ ξ]
  have hs := exterior_sheet_smoothing R C v m ξ Z hZ
  refine hs.2.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with t
  rw [(orbitIntegral_fiber_eq_of_extraction R C hx v m Z hZ ξ
    ⟨t.val / Z, div_pos t.property hZ⟩ (fun γ => hextract ξ γ _)).2]

end DedekindZetaZeroFree.OrbitExpansion

end
