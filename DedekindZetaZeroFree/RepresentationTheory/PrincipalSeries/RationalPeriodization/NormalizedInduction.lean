module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarRealizationAndCompactFiniteness
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RationalPeriodization.GlobalSmoothness

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem scalarSource_rational_covariance (x : PlusCore R N P C)
    (r : KPGlobalCenterRationalCharacter.R F R.A.zeta12 R.A.primitive_zeta12)
    (y : KPAdeles F) (g : Group R) :
    scalarSourceEvaluator R N P C x ((r.val.val * KPGlobalTorusFunctionData.N
      F R.A.zeta12 R.A.primitive_zeta12 y) * g) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 r.val : NNReal) : ℝ)) (1/2+0) *
        (KPGlobalCenterRationalCharacter.lambdaR F R.A.zeta12 R.A.primitive_zeta12 r : ℂ) *
          scalarSourceEvaluator R N P C x g := by
  rw [mul_assoc]
  change (quotientRationalEvaluator R N P C x _).val.val 1 = _
  rw [quotientRationalEvaluator_torus, quotientRationalEvaluator_upperRoot, one_mul]
  have hf := (quotientRationalEvaluator R N P C x g).val.property r 1
  change (quotientRationalEvaluator R N P C x g).val.val (r.val * 1) =
    (KPGlobalCenterRationalCharacter.lambdaR F R.A.zeta12 R.A.primitive_zeta12 r : ℂ) *
      (quotientRationalEvaluator R N P C x g).val.val 1 at hf
  rw [mul_one] at hf
  rw [hf]
  rw [EisensteinReferenceSections.SeedScalarTransport.normalized_multiplier]
  simp only [KPGlobalTorusBorelTwistCompatibility.normPower, zero_mul, Complex.exp_zero, mul_one]
  exact (mul_assoc _ _ _).symm

theorem scalarSource_induced (x : PlusCore R N P C) :
    KPLiteralRaw.Induced F R.A.zeta12 R.A.primitive_zeta12 0 (scalarSourceEvaluator R N P C x) :=
  ⟨scalarSource_smooth R N P C x, scalarSource_rational_covariance R N P C x⟩

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
