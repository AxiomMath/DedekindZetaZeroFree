module

public import DedekindZetaZeroFree.Theta.Unfolding.ReverseOrbitIntegration
public import DedekindZetaZeroFree.Theta.Unfolding.BranchCoordinateFrequencySeries

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open BranchCoordinateSeries
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def numericalReflectedTerm {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (Z : ℝ)
    (ξ : ThetaReflectionData.Frequency R.A) : ℂ :=
  ThetaBranch.exteriorFrequencyCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D ξ *
    (sourceFrequencyCharacter R (Characters.psi R) (Characters.L R) (Characters.compatible R) v ξ)⁻¹ *
      C.realization.H C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
        (Z * ThetaReflectionData.frequencyNorm R.A ξ)

theorem numerical_frequency_dictionary {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun ξ => ‖numericalReflectedTerm R C v m D Z ξ‖) ∧
    (∑' ξ, numericalReflectedTerm R C v m D Z ξ) =
      RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps R.σ
        (Characters.psi R) (Characters.L R v) (C.realization.H C.packet v) D.h D.d Z := by
  have hrec : ThetaPhaseSeparation.SquarefreeGeneratorReciprocity R.A R.probe.allowed R.σ :=
    PrincipalMellinSource.squarefree_source_generator_reciprocity R
  have hs := separated_summand_norm_summable R.A R.probe.allowed R.probe.unitReps R.σ
    (Characters.psi R) (Characters.primitive R) (Characters.L R v) (Characters.norm_one R v)
    (C.realization.H C.packet) (finite_profiles_of_same_residue R C.profiles) v D.h D.d Z hZ
  have hb := branchCoordinateSummand_norm_summable_of_separated R.A R.probe.allowed
    R.probe.unitReps R.σ (Characters.psi R) (Characters.primitive R)
    (Characters.L R v) (Characters.norm_one R v) hrec (C.realization.H C.packet v) m D Z hs
  obtain ⟨hf, hfreq⟩ := branchCoordinateSeries_eq_frequencySeries R
    (Characters.psi R) (Characters.L R) (Characters.primitive R) (Characters.compatible R)
    (C.realization.H C.packet v) v m D Z hb
  have hsep := (branch_coordinate_series_eq_expansion R.A R.probe.allowed R.probe.unitReps R.σ
    (Characters.psi R) (Characters.primitive R) (Characters.L R v) (Characters.norm_one R v)
    hrec (C.realization.H C.packet v) m D Z hb)
  exact ⟨hf, hfreq.symm.trans hsep⟩

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
