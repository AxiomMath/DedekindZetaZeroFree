module

public import DedekindZetaZeroFree.Theta.Profiles.CanonicalSphericalRealization

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion RootDerivatives
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem current_native_transport_exists
    (R:PrincipalMellin.ActualRecipe S η) (hR:RootAligned R) (N:TraceHaarTransport R) :
    ∃A:JointExteriorCoefficientSources R N, SourceNativeLie R A.factorization ∧ Nonempty (SphericalTransportData R A) := by
  obtain ⟨P,C,hP,hC⟩ := EisensteinReferenceSections.FrozenFibers.exists_model_fibers R.A R.classKilled
  obtain ⟨u,hu⟩ := exists_initial_plus_fourier_ne_zero_normalized R P C N hC
  let μ := fun q:KPFinitePlace F=>Measure.addHaarMeasure (TensorSeedSource.integerCompacts q)
  letI : ∀q,(μ q).IsAddHaarMeasure := fun q=>inferInstance
  have hμ : ∀q,μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _)=1 :=
    fun _=>Measure.addHaarMeasure_self
  have hs := coreFlatInsertion_initial_exterior_spherical R P C hC (PiTensorProduct.tprod ℂ u)
  exact ⟨canonicalStage08 R P C μ hμ  hR N hC u hs hu,
    canonicalStage08_native R P C μ hμ  hR N hC u hs hu,
    canonical_spherical_transport R P C μ hμ  hR N hC u hs hu⟩
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
