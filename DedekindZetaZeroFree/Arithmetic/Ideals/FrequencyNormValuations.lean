module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.MaskedPrimitiveInducers

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_frequency_norm_dictionary
    (R : PrincipalMellin.ActualRecipe S η) (u : Frequency R) :
    frequencyNorm R u = (Detector.frequencyNorm F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) u.val.val : ℝ) ∧
    1 ≤ frequencyNorm R u := by
  refine ⟨rfl, ?_⟩
  change (1 : ℝ) ≤ (Detector.frequencyNorm F _ u.val.val : ℝ)
  exact_mod_cast (Detector.exterior_frequency_support_finite_norm_pos F _
    R.A.Sf.finite_toSet u.val.val u.val.property).2.2

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic
