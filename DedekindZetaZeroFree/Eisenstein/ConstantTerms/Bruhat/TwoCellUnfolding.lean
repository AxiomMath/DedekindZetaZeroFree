module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.StandardIntegral.AbsoluteIntegrability

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

theorem actual_upper_constantTerm_eq
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (∫ q : KPCompactFourier.AdditiveQuotient F,
      KPContActualChamberNormalSeries.E F ζ hζ U ι f s
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
      ∂KPWildKernelUpperBound.quotientHaar F) =
    KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s) g +
      ∫ x : KPGlobalTorusFunctionData.Adeles F,
        KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
          (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
            (KPCubicCoverConstruction.adelicW F ζ hζ) *
            KPGlobalTorusFunctionData.N F ζ hζ x * g)
        ∂KPAdditiveHaar.adelicMeasure F := by
  letI := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let v := KPContFlatSourceRecipe.flatR F ζ hζ s
    (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι (f s))
  have hsum : ∀ q : KPCompactFourier.AdditiveQuotient F,
      KPGlobalEisensteinData.EisensteinSummable
        (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
          KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.rational F ζ hζ
            (Quotient.out c)) v.val
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) := by
    intro q
    have hh := KPContActualChamberNormalSeries.mixed_summable F ζ hζ U ι f hι hf
      0 [] s hs (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
    change Summable (fun c => ‖KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
      (KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.rational F ζ hζ
        (Quotient.out c) * (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g))‖)
    simpa only [KPGlobalEisensteinData.EisensteinSummable,
      KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord,
      List.foldr_nil, iteratedDerivWithin_zero, KPContActualChamberNormalSeries.term,
      chamber_lift_eq_rational] using hh
  have h := KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.integral_two_cells
    F ζ hζ s v (KPAdditiveHaar.adelicMeasure F) (KPWildKernelUpperBound.quotientHaar F)
    (actual_quotientHaar_compatible F) g hsum
    (standard_measurable F ζ hζ U ι s (f s) g)
    (actual_standard_integrable F ζ hζ U ι f hι hf s hs g)
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with q
  unfold KPContActualChamberNormalSeries.E KPGlobalEisensteinData.eisenstein
  apply tsum_congr
  intro c
  unfold KPContActualChamberNormalSeries.term
  rw [chamber_lift_eq_rational]
  rfl
  rfl

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
