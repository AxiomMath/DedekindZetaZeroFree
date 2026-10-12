module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspSections.MeanMonodromy
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactUnipotentPeriods

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMeanZeroSection

open scoped Classical NumberField Topology
open MeasureTheory KPContFlatCuspIncomingEvaluation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

section CompactIntegration
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup X] [NormedSpace ℝ X]

end CompactIntegration

open KPContFlatCuspCasimirSpecialization

section Algebra
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : Cusps F ζ hζ C R P H U)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)

include hs in

theorem actual_component_casimir
 (i : Fin (H.atlas (atlasLevel F ζ hζ C R P H U)).componentCount)
 (z : KPArch.Space (KPCuspLogShape.dimension F)) :
 KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
   (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s i).val z =
 KPContActualChamberCasimirJets.lambda F s *
   (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s i).val z := by
 obtain ⟨O⟩ := KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ
   (atlasLevel F ζ hζ C R P H U) R P H i z
 let p := KPContCotangentActualOverlap.placeEquiv F ζ hζ
 let a : KPContActualChamberCasimirJets.Frame F ζ hζ C R P H U i :=
   { kind := .orbifold z O
     places := p
     splitting := fun _ => 1
     splitting_locallyConstant := IsLocallyConstant.const 1 }
 let x := KPContCotangentActualOverlap.labeledAInv p z
 have hxz : KPContCotangentActualOverlap.labeledA p x = z := by
   funext k
   simp only [x, KPContCotangentActualOverlap.labeledAInv, KPContCotangentActualOverlap.labeledA]
   rw [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
 have hx : x ∈ a.omega := by
   change KPContCotangentActualOverlap.labeledA p x ∈ O.neighborhood
   rw [hxz]
   exact O.center_mem
 have hh := KPContActualChamberCasimirJets.casimir F ζ hζ C R P H U ι f hι hf s hs a x hx
 have he : KPContActualChamberCasimirJets.frameJet F ζ hζ C R P H U ι f hι hf 0 s a =
   fun y => (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s i).val
     (KPContCotangentActualOverlap.labeledA p y) := by
   funext y
   simp [KPContActualChamberCasimirJets.frameJet, KPContCotangentActualOverlap.LiftedChart.coefficient,
     a, KPContCotangentActualOverlap.ChartKind.representative]
 rw [he] at hh
 have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv _ _ p
   (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s i).val
   (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf 0 s hs i) x
 change _ = HyperbolicChart.laplacian _ (fun y =>
   (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s i).val
     (KPContCotangentActualOverlap.labeledA p y)) x at hb
 rw [←hb] at hh
 change KPContActualSphericalFlatStage.localLaplacian _ _
   (KPContCotangentActualOverlap.labeledA p x) = _ at hh
 simpa only [hxz] using hh

include hι hf hs in

theorem actual_parameterScalar_zero_fiber (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f 0 s z ∈
      KPCuspGenuineMonodromy.scalarFiber F ζ hζ (atlasLevel F ζ hζ C R P H U) := by
  let e := KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension
  obtain ⟨p, rfl⟩ := e.surjective z
  change KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f 0 s
    (KPCuspCharts.toArch F p) ∈ _
  rw [parameterScalar_zero_coordinates]
  unfold KPContActualChamberMeanZeroAdapter.meanZeroJetSheet
  simp only [map_one, Units.val_one, one_mul]
  apply Submodule.sub_mem
  · intro ε hε
    exact actualCuspSheet_central_fixed F ζ hζ C R P H U a ι hι f hf s hs p.2 p.1.2
      ⟨ε, hε⟩ p.1.1
  · exact (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
      (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a)
      0 s p.2 p.1.2).property.1.1 _

include hι hf hs in

theorem actual_parameterScalar_zero_equivariant
    (h : (actualEnd F ζ hζ C R P H U a).parabolicGroup)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f 0 s
      (KPCuspSiegel.action F h.val z) =
    (KPCuspGenuineMonodromy.chi F ζ hζ ((actualEnd F ζ hζ C R P H U a).rho h) : ℂ) *
      KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f 0 s z := by
  let e := KPCuspCharts.toArchHomeomorph F (geometry F ζ hζ C R P H U a).positive_dimension
  obtain ⟨p, rfl⟩ := e.surjective z
  change KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f 0 s
    (KPCuspSiegel.action F h.val (KPCuspCharts.toArch F p)) =
    (KPCuspGenuineMonodromy.chi F ζ hζ ((actualEnd F ζ hζ C R P H U a).rho h) : ℂ) *
      KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f 0 s
        (KPCuspCharts.toArch F p)
  obtain ⟨A, hA, hc⟩ := (parabolic F ζ hζ C R P H U a).upper h h.property
  rw [(geometry F ζ hζ C R P H U a).actual_action h A hA hc]
  rw [parameterScalar_zero_coordinates, parameterScalar_zero_coordinates]
  have hp := (geometry F ζ hζ C R P H U a).crossAction_formula h A hA hc p.1
  have hv := actualMeanZeroSheet_crossAction F ζ hζ C R P H U a ι hι f hf s hs
    p.2 p.1.2 h p.1.1
  rw [hp] at hv
  exact hv

end Algebra

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMeanZeroSection

end
