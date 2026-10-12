module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.SphericalExteriorInsertion
public import DedekindZetaZeroFree.Theta.Whittaker.Nonvanishing.NormalizedFourierCoefficient
public import DedekindZetaZeroFree.Theta.Periods.RepeatedCorePeriod

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem current_period_source_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) : Nonempty (NonDegenerate.PeriodSource R N) := by
  obtain ⟨P,C,hP,hC⟩ := EisensteinReferenceSections.FrozenFibers.exists_model_fibers R.A R.classKilled
  obtain ⟨u,hu⟩ := exists_initial_plus_fourier_ne_zero_normalized R P C N hC
  let x := RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
    (bad R.A P C) ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u)
  obtain ⟨D,hD,hflat⟩ := exists_repeated_core_period_source R P C  hR N x
    (coreFlatInsertion_initial_exterior_spherical R P C hC (PiTensorProduct.tprod ℂ u)) hu
  exact ⟨D⟩
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
