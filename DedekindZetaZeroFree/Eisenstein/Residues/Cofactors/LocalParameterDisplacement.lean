module

public import DedekindZetaZeroFree.Eisenstein.Induction.FullCompactForwardFactor
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.BoxFiberDisplacement

@[expose] public section

noncomputable section
open _root_.DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant renaming forwardSection_real_formula → forwardSection_real_formula
open scoped Classical NumberField TensorProduct BigOperators
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages KPLocalExceptionalConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem finite_parameter_value (E Q : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (hEQ : E ⊆ Q)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (g : Raw R.A) (z : ℂ) (q : Q) :
    let v := cofactorSourceLevel R P C Q (hE.trans hEQ)
    let y := cofactorExtendedTuple R P C E hE φ v
    Complex.exp (z * (FaithfulSource.RepairedInducing.localLog R P C g (.inr q.val) : ℂ)) •
      localValue R.A P C (.inr q.val) (g (.inr q.val))
        (y ⟨.inr q.val, Finset.inr_mem_disjSum.mpr q.property⟩) =
      (compactTrivialization (C.canonical q.val).borel (C.polarization q.val)
        (C.canonical q.val).iwasawa .plus z
        (ExteriorTensorHaar.enlargedProfiles F ζ hζ P C E Q hE φ z q)).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (.inr q.val) (g (.inr q.val))) := by
  dsimp only
  simp only [FaithfulSource.RepairedInducing.localLog, CurrentFullCompactBinding.forwardAbs_eq]
  by_cases hq : q.val ∈ E
  · simp only [ExteriorTensorHaar.enlargedProfiles, dite_eq_left hq,
      ActualFullCompactTransport.fullCompactProfiles, FiniteSourceTransport.parameterSource_extension]
    simp [cofactorExtendedTuple, cofactorSourceLevel, cofactorSourceTuple, hq,
      localValue, FiniteSourceTransport.localLogNorm, LocalCompactChange.forwardAbs]
  · simp only [ExteriorTensorHaar.enlargedProfiles, dite_eq_right hq,
      FiniteSourceTransport.parameterSource_extension]
    have hn : q.val ∉ C.exceptional := fun h => hq (hE h)
    simp only [cofactorExtendedTuple, cofactorSourceLevel, Finset.inr_mem_disjSum,
      dite_eq_right hq]
    rw [CurrentExteriorReference.plusReference_eq_exterior R.A P C q.val hn]
    rfl

theorem complex_spherical_parameter (g : Raw R.A) (z : ℂ) (v : InfinitePlace F) :
    Complex.exp (z * (FaithfulSource.RepairedInducing.localLog R P C g (.inl v) : ℂ)) *
      localValue R.A P C (.inl v) (g (.inl v)) (plusReference R.A P C (.inl v)) =
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (.inl v)).epsilon : ℂ) *
      KPComplexIntertwinerParameterMajorant.forwardSection z
        KPComplexStandardIntertwinerGerm.compactSpherical (complexMatrix R.A v (g (.inl v))) := by
  let m := complexMatrix R.A v (g (.inl v))
  have hzero : KPComplexIntertwinerParameterMajorant.forwardSection 0
      KPComplexStandardIntertwinerGerm.compactSpherical m =
      KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter m := by
    simpa [KPComplexStandardIntertwinerGerm.compactSpherical,
      KPCplxPrincipalSeriesCharts.sphericalSection] using
      forwardSection_real_formula 0 KPComplexStandardIntertwinerGerm.compactSpherical m
  change Complex.exp (z * ((2 * Real.log (KPComplexIntertwinerParameterMajorant.rowRatio m) : ℝ) : ℂ)) *
    ((KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (.inl v)).epsilon : ℂ) *
      KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter m) = _
  rw [← hzero]
  unfold KPComplexIntertwinerParameterMajorant.forwardSection
  have he : Complex.exp (z * ((2 * Real.log
      (KPComplexIntertwinerParameterMajorant.rowRatio m) : ℝ) : ℂ)) *
      Complex.exp (((4/3 : ℂ) + 2*0) * (Real.log
        (KPComplexIntertwinerParameterMajorant.rowRatio m) : ℂ)) =
      Complex.exp (((4/3 : ℂ) + 2*z) * (Real.log
        (KPComplexIntertwinerParameterMajorant.rowRatio m) : ℂ)) := by
    rw [← Complex.exp_add]
    apply congrArg Complex.exp
    push_cast
    ring
  rw [mul_left_comm (Complex.exp _) _, ← mul_assoc (Complex.exp _) (Complex.exp _) _, he]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
