module

public import DedekindZetaZeroFree.Theta.Unfolding.ProductCoordinateSmoothingIntegrability
public import DedekindZetaZeroFree.Theta.Digits.AbsoluteFourierReconstruction
public import DedekindZetaZeroFree.Theta.Unfolding.NonconstantQuotientAverage
public import DedekindZetaZeroFree.Theta.Whittaker.ArchimedeanFiberSmoothness

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical ENNReal
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem orbitSheet_hasSum {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (l : PositiveAxis) (z : Sheet R.A l) :
    HasSum (fun i : OrbitIndex R => orbitSheet R C v m b i l z)
      (weightedDigits R C.sources C.realization C.packet v m b z.val -
        weightedUpper R C.sources C.realization C.packet v m b z.val) := by
  apply orbitSheet_hasSum_of_rationalPeriod_norm_summable R C v m b l z
  intro d
  obtain ⟨K, hKc, hKo, hl⟩ := thetaFiber_exists_compact_open_level R C.realization v
    (signedArgument R m b z.val d)
  exact rationalPeriod_norm_summable_at_smooth_level R C.realization v _ K hKc hKo hl
    (thetaFiber_isArchSmooth R C.realization v _)

theorem absolute_extraction {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N) :
    AbsoluteExtraction R C := by
  intro v m b Z hZ
  letI := C.transport.groupHaar_isHaar
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable Fˣ := Units.val_injective.countable
  letI : Countable (OrbitIndex R) := Countable.of_equiv Fˣ (orbitFrequencyEquiv R).symm
  have hq (i : OrbitIndex R) (l : PositiveAxis) := orbitSheet_integrable R C v m b i l
  have ht (i : OrbitIndex R) := smoothingIntegrand_integrable R C v m b Z hZ i
  have hsheetSum : ∀ᵐ t ∂positiveHaar,
      HasSum (fun i : OrbitIndex R => C.packet.kernel t.val *
        orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩)
      (C.packet.kernel t.val *
        (thetaAverage R C.transport C.sources C.realization C.packet v m b
          ⟨t.val / Z, div_pos t.property hZ⟩ -
         upperAverage R C.transport C.sources C.realization C.packet v m b
          ⟨t.val / Z, div_pos t.property hZ⟩)) := by
    filter_upwards [smoothingMajorant_summable_ae R C v m b Z hZ] with t htmaj
    let l : PositiveAxis := ⟨t.val / Z, div_pos t.property hZ⟩
    have hi (i : OrbitIndex R) := (hq i l).const_mul (C.packet.kernel t.val)
    have hmass : Summable (fun i : OrbitIndex R =>
        ∫ z, ‖C.packet.kernel t.val * orbitSheet R C v m b i l z‖
          ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) := by
      exact htmaj.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
        (fun i => mul_orbitSheet_integral_norm_le R C v m b Z hZ i t)
    have hx := (AbsoluteIntegration.hasSum_integral hi hmass
      (Filter.Eventually.of_forall (fun z =>
        (orbitSheet_hasSum R C v m b l z).mul_left (C.packet.kernel t.val)))).2
    simp only [integral_const_mul] at hx
    rw [← thetaAverage_sub_upperAverage_domain R C v m b l] at hx
    exact hx
  have hmass := smoothingIntegrand_integral_norm_summable R C v m b Z hZ
    (fun i => (ht i).aestronglyMeasurable)
  obtain ⟨hnonconstant, hsum⟩ := AbsoluteIntegration.hasSum_integral ht hmass hsheetSum
  have hupper := C.descent.smoothing_integrable v m b Z hZ
  have htheta : Integrable (fun t : PositiveAxis => C.packet.kernel t.val *
      thetaAverage R C.transport C.sources C.realization C.packet v m b
        ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar := by
    convert hnonconstant.add hupper using 1
    funext t
    simp only [Pi.add_apply, mul_sub, sub_add_cancel]
  refine ⟨hq, ht, orbitTerm_norm_summable R C v m b Z hZ, ?_, htheta⟩
  rw [smoothedTheta_sub_mainTerm R C v m b Z hZ htheta]
  exact hsum

end DedekindZetaZeroFree.OrbitExpansion

end
