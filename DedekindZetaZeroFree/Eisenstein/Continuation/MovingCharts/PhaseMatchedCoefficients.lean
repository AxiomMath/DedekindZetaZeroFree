module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothSections.RightDifferentialHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMovingLocal

open KPContLocalNorm

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem section_lift_chart
    (Q : KPContActualSphericalRightFieldIdentification.GroupChart F ζ hζ U R P H) :
    ∃ V : Set (Space (KPContActualSphericalRightFieldIdentification.groupDimension F)),
      IsOpen V ∧ (0 : Space (KPContActualSphericalRightFieldIdentification.groupDimension F)) ∈ V ∧
      V ⊆ Q.T.carrier ∧
    ∃ A : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H,
    ∃ ρ : Space (KPContActualSphericalRightFieldIdentification.groupDimension F) →
      Space (KPCuspLogShape.dimension F * 3),
      (∀ y, ρ y = (KPContActualChartRestrictionDensity.coordinates F).symm
        (KPContActualSphericalRightFieldIdentification.baseCoordinates F (Q.π y))) ∧
      A.component = Q.component ∧
      A.phase = KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U Q.phase ∧
      ContDiffOn ℝ (⊤ : ℕ∞) ρ V ∧ Set.MapsTo ρ V A.ball.carrier ∧
      (∀ y ∈ V,
        KPContActualCommonDiskRightHolomorphy.baseProjection F ζ hζ U (Q.groupLift y) =
          KPContActualChartRestrictionDensity.basePoint F ζ hζ U R P H A.component (ρ y)) ∧
      ∀ u : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H,
      ∀ y ∈ V,
        KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u (Q.groupLift y) =
          KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A (ρ y) := by
  let ρ : Space (KPContActualSphericalRightFieldIdentification.groupDimension F) →
      Space (KPCuspLogShape.dimension F * 3) := fun y =>
    (KPContActualChartRestrictionDensity.coordinates F).symm
      (KPContActualSphericalRightFieldIdentification.baseCoordinates F (Q.π y))
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ Q.T.carrier := by
    exact (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_symm_contDiff
      (KPCuspLogShape.dimension F)).comp_contDiffOn
        ((KPContActualSphericalRightFieldIdentification.baseCoordinates F).contDiff.comp_contDiffOn
          Q.π_smooth)
  obtain ⟨A, hcomp, _, hphase, hcenter⟩ :=
    KPContActualSmoothLineGluing.exists_canonicalChartBall F ζ hζ U R P H Q.component
      (KPContActualSphericalRightFieldIdentification.baseCoordinates F (Q.π 0))
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U Q.phase)
  let V := Q.T.carrier ∩ ρ ⁻¹' A.ball.carrier
  have hVT : V ⊆ Q.T.carrier := Set.inter_subset_left
  refine ⟨V, hρ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball Metric.isOpen_ball,
    ⟨Q.zero_mem, hcenter⟩, hVT, A, ρ, fun _ => rfl, hcomp, hphase,
    hρ.mono hVT, fun _ hy => hy.2, ?_, ?_⟩
  · intro y hy
    unfold KPContActualCommonDiskRightHolomorphy.baseProjection
    rw [Q.actual_base_chart y (hVT hy)]
    simp only [KPContSectorPhaseComponentCharts.coveredChart_mk]
    unfold KPContActualChartRestrictionDensity.basePoint
    dsimp only [ρ]
    rw [hcomp, Homeomorph.apply_symm_apply,
      ← KPContSectorCoveredQuotientVocabulary.z_mk,
      KPContSectorCoveredQuotientVocabulary.q_z,
      KPContSectorCoveredQuotientVocabulary.q_mk, (H.atlas U).components_formula]
    rfl
  · intro u y hy
    have hh := Q.global_scalar_pullback
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H u) y (hVT hy)
    change KPContActualCommonDiskRightHolomorphy.lift F ζ hζ U R P H u (Q.groupLift y) = _ at hh
    rw [hh]
    unfold KPContActualSmoothLineGluing.coefficient
    rw [hcomp, hphase, KPContActualChartRestrictionDensity.frameCoefficient_class]
    simp only [ρ, Homeomorph.apply_symm_apply, KPContRightJets.scalarLift,
      KPContActualSphericalRightFieldIdentification.GroupChart.frame]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMovingLocal

end
