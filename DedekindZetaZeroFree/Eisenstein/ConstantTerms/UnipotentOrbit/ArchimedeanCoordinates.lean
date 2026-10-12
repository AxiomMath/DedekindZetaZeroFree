module

public import DedekindZetaZeroFree.Metaplectic.Kubota.Cusps.FiniteKernelLevel
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.KernelTorus.ContinuityAndIntegrability
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspKernelTorus.ProbabilityHaarTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open KPContFlatCuspIncomingEvaluation
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S) (hι : Function.Injective ι)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
variable (a : Cusps F ζ hζ C R P H U) (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F)
include hι hf hs in

theorem actual_arch_root_orbit_coordinate (x : InfiniteAdeleRing F) :
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s
   (KPGlobalTorusFunctionData.N F ζ hζ (x,0) * localGroup F ζ hζ C R P H U a t 0 b ε) =
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s
   (localGroup F ζ hζ C R P H U a t
     (mixedToHorizontal F (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) b ε) := by
 obtain ⟨e,he,-,-⟩ := KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
 rw [root_arch_insertion, localGroup, localGroup, ← mul_assoc,
   ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
 rw [← he s hs, ← he s hs, KPContSectorScalarLineAlgebra.group_lift_formula,
   KPContSectorScalarLineAlgebra.group_lift_formula]
 congr 2
 rw [archBasepoint_mul, KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection,
   KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
 apply congrArg _
 apply Prod.ext
 · funext i
   change KPArch.action (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ _)).out _ = _
   rw [projective_action_mk, upper_root_action]
   apply Prod.ext
   · change 0 + complexParameter F ζ hζ x (KPCusp.complexPlace F i) = _
     rw [zero_add]
     rfl
   · rfl
 · rfl
end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
