module

public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.LocalLines
public import DedekindZetaZeroFree.Theta.Whittaker.Sources.CovariantConstruction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.SphericalExteriorInsertion
public import DedekindZetaZeroFree.Theta.Whittaker.Nonvanishing.NormalizedFourierCoefficient

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

theorem current_local_lines_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) : Nonempty (TensorLocalLines R N) := by
  obtain ⟨P,C,hP,hC⟩ := EisensteinReferenceSections.FrozenFibers.exists_model_fibers R.A R.classKilled
  obtain ⟨u,hu⟩ := exists_initial_plus_fourier_ne_zero_normalized R P C N hC
  let μ := fun q : KPFinitePlace F => Measure.addHaarMeasure (TensorSeedSource.integerCompacts q)
  letI : ∀ q, (μ q).IsAddHaarMeasure := fun q => inferInstance
  exact ⟨canonicalTensorLocalLines R P C μ
    (fun _ => Measure.addHaarMeasure_self)  hR N hC u
    (coreFlatInsertion_initial_exterior_spherical R P C hC (PiTensorProduct.tprod ℂ u)) hu⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
