module

public import DedekindZetaZeroFree.Theta.Unfolding.SignedDigitExpansion

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.MomentSources
open scoped NumberField Classical
open NumberField MeasureTheory
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem finite_profiles_of_same_residue {Q : AdmissibleFlatSources R}
    {T : Realization R Q} {P : Packet R Q} (H : SameResidueProfiles R Q T P) :
    RMSeparatedExpansion.FiniteProfileFamily R.A (T.H P) := by
  letI := Q.finite_companions
  letI := H.finite_classes
  exact PrincipalMellinSource.finiteProfileFamily_of_uniform_log_bounds
    R.A (T.H P) H.smooth H.bounds

theorem mainTerm_eq_zero {N : TraceHaarTransport R} {Q : AdmissibleFlatSources R}
    {T : Realization R Q} {P : Packet R Q} (h : BothUpperZero R N Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) :
    mainTerm R N Q T P v m b Z = 0 := by
  unfold mainTerm
  split_ifs with hZ
  · have he : (fun t : ThetaProfileHaarSheets.PositiveAxis => P.kernel t.val *
        upperAverage R N Q T P v m b ⟨t.val / Z, div_pos t.property hZ⟩) = fun _ => (0 : ℂ) := by
      funext t
      rw [h v m b _]
      exact mul_zero _
    rw [he]
    exact integral_zero _ _
  · rfl

theorem smoothedTheta_sign_eq {N : TraceHaarTransport R} {Q : AdmissibleFlatSources R}
    {T : Realization R Q} {P : Packet R Q} (A : DigitsDescent R N Q T P)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (Z : ℝ) :
    smoothedTheta R N Q T P v m true Z = smoothedTheta R N Q T P v m false Z := by
  have he : ∀ y, weightedDigits R Q T P v m true y = weightedDigits R Q T P v m false y := by
    intro y
    unfold weightedDigits
    rw [A.weyl]
  have hq : ∀ l, thetaAverage R N Q T P v m true l = thetaAverage R N Q T P v m false l := by
    intro l
    unfold thetaAverage
    apply integral_congr_ae
    filter_upwards [] with z
    exact he (Quotient.out z).val
  unfold smoothedTheta
  split_ifs
  · apply integral_congr_ae
    filter_upwards [] with t
    rw [hq]
  · rfl

theorem SignedUnfolding.identity {N : TraceHaarTransport R} {Q : AdmissibleFlatSources R}
    {T : Realization R Q} {P : Packet R Q} (U : SignedUnfolding R N Q T P)
    (A : DigitsDescent R N Q T P) (u : R.A.Rˣ) (hu : u ∈ U.Ur)
    (h d : R.A.Exterior) (hh : Powerful h.val) (hd : Squarefree d.val)
    (hc : h.val ⊔ d.val = ⊤) (Z : ℝ) (hZ : 0 < Z) :
    ThetaReflectionData.forwardB R.A R.probe.coefficients
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z =
    RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps R.σ
      (Characters.psi R) (Characters.L R (U.row_class u)) (T.H P (U.row_class u)) h d Z +
      mainTerm R N Q T P (U.row_class u) (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) false Z -
      mainTerm R N Q T P (U.row_class u) (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z := by
  rw [U.forward_unfolding u hu h d hh hd hc Z hZ,
    U.reverse_unfolding u hu h d hh hd hc Z hZ,
    smoothedTheta_sign_eq R A]
  ring

def CertifiedPacket.toMomentSource (C : CertifiedPacket R) : SelectedMomentSource R where
  Ur := C.unfolding.Ur
  units := C.unfolding.units
  psi := Characters.psi R
  primitive := Characters.primitive R
  L := Characters.L R
  norm_one := Characters.norm_one R
  characters_compatible := Characters.compatible R
  H := C.realization.H C.packet
  profiles := finite_profiles_of_same_residue R C.profiles
  reflected_domination := by
    intro u hu h d hh hd hc Z hZ
    refine ⟨C.unfolding.row_class u, ?_⟩
    have he := C.unfolding.identity R C.descent u hu h d hh hd hc Z hZ
    rw [mainTerm_eq_zero R C.upperZero, mainTerm_eq_zero R C.upperZero, add_zero, sub_zero] at he
    rw [he]

theorem momentSource_of_certified_packet (C : CertifiedPacket R) :
    RootAligned R ∧ Nonempty (SelectedMomentSource R) :=
  ⟨C.aligned, ⟨C.toMomentSource R⟩⟩

end DedekindZetaZeroFree.MomentSources

end
