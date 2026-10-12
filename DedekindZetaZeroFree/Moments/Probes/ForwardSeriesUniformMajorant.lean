module

public import DedekindZetaZeroFree.Moments.Reflected.DyadicMomentSource
public import DedekindZetaZeroFree.Moments.Probes.ForwardGaussianSeriesBounds

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]

theorem forward_weight_norm_le_one
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)
    (c : ExteriorSquarefreeIdeal R.A.cS) (n : R.A.Exterior) :
    ‖ThetaReflectionData.forwardArithmeticWeight R.A R.probe.coefficients c n‖ ≤ 1 := by
  have ht : ‖R.probe.coefficients.theta
      (ThetaReflectionData.forwardModulus R.A R.probe.coefficients c n)‖ = 1 := by
    let m' : ThetaReflectionData.Row R.A :=
      ⟨ThetaReflectionData.forwardModulus R.A R.probe.coefficients c n,
        mul_ne_zero (R.probe.coefficients.generates c.val).1
          (pow_ne_zero _ (R.probe.coefficients.generates n).1)⟩
    exact (congrArg norm (R.probe.theta_principal m')).trans (Circle.norm_coe _)
  rw [ThetaReflectionData.forwardArithmeticWeight, norm_mul, ht, mul_one]
  exact NormalizedProbe.PrincipalData.norm_gammaTwo_le_one
    R.A R.σ R.target R.traceBad R.probe c

theorem forward_summand_norm_summable
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)
    (m : ThetaReflectionData.Row R.A) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun i : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior =>
      ‖ThetaReflectionData.forwardSummand R.A R.probe.coefficients m Z i.1 i.2‖) :=
  PoissonProbeDyadicMomentTransfer.ActualDyadicMomentSource.forwardSummand_norm_summable_of_weight
    R.A R.probe.coefficients (forward_weight_norm_le_one R) m Z hZ

theorem forward_hasSum
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)
    (m : ThetaReflectionData.Row R.A) (Z : ℝ) (hZ : 0 < Z) :
    HasSum (fun i : ExteriorSquarefreeIdeal R.A.cS × R.A.Exterior =>
      ThetaReflectionData.forwardSummand R.A R.probe.coefficients m Z i.1 i.2)
      (ThetaReflectionData.forwardB R.A R.probe.coefficients m Z) :=
  (forward_summand_norm_summable R m Z hZ).of_norm.hasSum

end
end DedekindZetaZeroFree.MomentSources
