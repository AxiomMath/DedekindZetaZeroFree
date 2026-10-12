module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.RootPeriod

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma diagonal_upper_projector (y : R.A.G) (x : KPAdeles F) :
    diagonal R y * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x =
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        ((localIdele R y : KPAdeles F) * x) * diagonal R y := by
  have h := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12 R.A.primitive_zeta12
    ((localIdele R y : KPAdeles F) * x) (localIdele R y)
  have hc : ((localIdele R y : KPAdeles F) * x) *
      (↑((localIdele R y)⁻¹) : KPAdeles F) = x := by
    rw [mul_right_comm, Units.mul_inv, one_mul]
  rw [hc] at h
  exact h.symm

theorem stage08_fourier_root_translate {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (v : R.A.UnitQuotient) (y : R.A.G) (x : KPAdeles F) :
    MomentSources.fourier R A.sources.dq
      (KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x)
        (A.realization.theta v)) (diagonal R y) =
      (adelicTraceQuotientCharacter F
        (QuotientAddGroup.mk ((localIdele R y : KPAdeles F) * x)) : ℂ) *
        MomentSources.fourier R A.sources.dq (A.realization.theta v) (diagonal R y) := by
  rw [fourier_rightAction, diagonal_upper_projector, stage08_fourier_upper]

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
