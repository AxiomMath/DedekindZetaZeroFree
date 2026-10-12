module

public import DedekindZetaZeroFree.Eisenstein.Residues.PositiveTraceCoefficient
public import DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.LocalRealization
public import DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.ScalarInjectivityAndRegularity
public import DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.LieWordGeneration
public import DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.FiniteCoverCovariance
public import DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.SU2Covariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem tensorDetected_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (TensorActions R N)) :
    Nonempty (TensorDetected R N) := by
  obtain ⟨P⟩ := prior
  obtain ⟨D₁, _, _⟩ := detected_period_source_exists  R hR N ⟨P.toJointRealizedFlatSources⟩
  obtain ⟨D₂, _⟩ := detected_dictionary_exists  R N ⟨D₁⟩
  obtain ⟨D₃, _⟩ := detected_faithful_dictionary_exists  R N ⟨D₂⟩
  obtain ⟨D₄, _⟩ := detected_hc_generated_dictionary_exists  R N ⟨D₃⟩
  obtain ⟨D₅, _⟩ := detected_finite_covariant_dictionary_exists  R N ⟨D₄⟩
  obtain ⟨D₆, _⟩ := detected_complex_covariant_dictionary_exists  R N ⟨D₅⟩
  exact ⟨D₆.tensorDetected R N⟩
end DedekindZetaZeroFree.ThetaExpansion

end
