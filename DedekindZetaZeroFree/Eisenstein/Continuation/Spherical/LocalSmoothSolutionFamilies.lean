module

public import DedekindZetaZeroFree.Analysis.Elliptic.WeightedSmoothRepresentatives
public import DedekindZetaZeroFree.Analysis.Elliptic.WeightedSolutionJetContinuity
public import DedekindZetaZeroFree.Geometry.LineBundles.ContinuousCovariance
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.WeakChartEquations
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RightInvariantFieldCoordinates
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothResolventHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualLocalSolutionFamily

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def localFrameCoefficient {i : Fin (H.atlas U).componentCount} {x : SymmetricSpace F}
    {chart : OrbifoldChart F ζ hζ U R P H i x}
    (w : KPContActualSphericalRightFieldIdentification.LocalSection
      F ζ hζ U R P H i x chart)
    (m : PhaseSheets F ζ hζ U) (p : Space (KPCuspLogShape.dimension F * 3)) : ℂ :=
  (liftFrame F ζ hζ U (coordinates F p)
    (Quotient.lift (fun ε => phaseTransport F ζ hζ U ε (w.coefficient (coordinates F p)))
      (by
        intro a b hab
        have hmem : KPCuspGenuineMonodromy.central F ζ hζ (b⁻¹ * a) ∈ U.toOpenSubgroup := by
          have h1 := QuotientGroup.leftRel_apply.mp hab
          have hmem' : KPCuspGenuineMonodromy.central F ζ hζ (a⁻¹ * b) ∈ U.toOpenSubgroup := by
            simpa [KPContSectorPhaseComponentCharts.centralLevel] using h1
          have heq : KPCuspGenuineMonodromy.central F ζ hζ (b⁻¹ * a) =
              (KPCuspGenuineMonodromy.central F ζ hζ (a⁻¹ * b))⁻¹ := by
            simp only [map_inv, map_mul]
            group
          rw [heq]
          exact U.toOpenSubgroup.inv_mem hmem'
        exact phaseTransport_level_ambiguity F ζ hζ U a b hmem
          (w.coefficient (coordinates F p))) m) : ℂ)

set_option maxHeartbeats 1000000 in

structure Promotion (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (chart : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x chart)
    (Ω : Set ℂ) (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U) where
  representative : ℂ → Space (KPCuspLogShape.dimension F * 3) → ℂ
  smooth : ∀ s ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (representative s) A.carrier
  represents : ∀ s ∈ Ω, representative s =ᵐ[volume.restrict A.carrier]
    (fun p => restriction F ζ hζ U R P H i x chart m A hA (u s) p)
  unique : ∀ s ∈ Ω, ∀ f : Space (KPCuspLogShape.dimension F * 3) → ℂ,
    ContDiffOn ℝ (⊤ : ℕ∞) f A.carrier →
    (f =ᵐ[volume.restrict A.carrier]
      (fun p => restriction F ζ hζ U R P H i x chart m A hA (u s) p)) →
    Set.EqOn f (representative s) A.carrier

  stabilizer : ∀ s ∈ Ω,
    ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x,
    ∀ p ∈ A.carrier ∩ overlapCoordinate F ζ hζ U R P H i σ.val ⁻¹' A.carrier,
      representative s (overlapCoordinate F ζ hζ U R P H i σ.val p) =
        (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) *
          representative s p
  holomorphic : KPCutoffSource.ChartSmoothHolomorphicOn A representative Ω

  disks : ∀ (c : ℂ) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω →
    ∃ b : ℕ → Space (KPCuspLogShape.dimension F * 3) → ℂ,
      (∀ j, b j =ᵐ[volume.restrict A.carrier]
        (fun p => restriction F ζ hζ U R P H i x chart m A hA
          ((cauchyPowerSeries u c r j) (fun _ => 1)) p)) ∧
      SmoothPowerSeriesOn A c r b representative ∧
      (∀ j (f : Space (KPCuspLogShape.dimension F * 3) → ℂ),
        ContDiffOn ℝ (⊤ : ℕ∞) f A.carrier →
        (f =ᵐ[volume.restrict A.carrier]
          (fun p => restriction F ζ hζ U R P H i x chart m A hA
            ((cauchyPowerSeries u c r j) (fun _ => 1)) p)) →
        Set.EqOn f (b j) A.carrier)

theorem representative_family_core
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (SF : KPContActualFriedrichsWeakChart.SolutionFamily
      F ζ hζ U R P H μG hμG hR realization)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (chart : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x chart)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (a : ℂ → ℂ) (ha : DifferentiableOn ℂ a Ω)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U) (hu : DifferentiableOn ℂ u Ω)
    (forcing : ℂ → KPContActualSphericalRightFieldIdentification.LocalSection
      F ζ hζ U R P H i x chart)
    (hforcing_smooth : KPCutoffSource.ChartSmoothHolomorphicOn A
      (fun s => localFrameCoefficient F ζ hζ U R P H (forcing s) m) Ω)
    (hforcing_sobolev : ∀ B : LocalBall (KPCuspLogShape.dimension F * 3),
      KPContLocalCubeEmbedding.closedCarrier B ⊆ A.carrier →
      KPCutoffSource.ChartSobolevHolomorphicOn B
        (fun s => localFrameCoefficient F ζ hζ U R P H (forcing s) m) Ω)
    (hdom : ∀ s ∈ Ω, u s ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization).domain)
    (hsource : ∀ s (hs : s ∈ Ω),
      localFrameCoefficient F ζ hζ U R P H (forcing s) m =ᵐ[volume.restrict A.carrier]
        (fun p => restriction F ζ hζ U R P H i x chart m A hA
          ((KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization)
            ⟨u s, hdom s hs⟩ - a s • u s) p)) :
    ∃ f : ℂ → Space (KPCuspLogShape.dimension F * 3) → ℂ,
      (∀ s ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (f s) A.carrier ∧
        (f s =ᵐ[volume.restrict A.carrier]
          (fun p => restriction F ζ hζ U R P H i x chart m A hA (u s) p)) ∧
        (∀ g : Space (KPCuspLogShape.dimension F * 3) → ℂ,
          ContDiffOn ℝ (⊤ : ℕ∞) g A.carrier →
          (g =ᵐ[volume.restrict A.carrier]
            (fun p => restriction F ζ hζ U R P H i x chart m A hA (u s) p)) →
          Set.EqOn g (f s) A.carrier)) ∧
      SmoothCompactOpenHolomorphicOn A f Ω ∧
      (∀ s ∈ Ω, ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x,
        ∀ p ∈ A.carrier ∩ overlapCoordinate F ζ hζ U R P H i σ.val ⁻¹' A.carrier,
          f s (overlapCoordinate F ζ hζ U R P H i σ.val p) =
            (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) *
              f s p) := by
  classical
  let RA := restriction F ζ hζ U R P H i x chart m A hA
  let h := fun s => localFrameCoefficient F ζ hζ U R P H (forcing s) m
  let D := SF.coefficients A
  have hweak : ∀ s ∈ Ω, ∃ w : IntegerSobolev A 1,
      KPContLocalEnergy.value w = RA (u s) ∧ ∃ g : BallL2 A,
        (h s =ᵐ[volume.restrict A.carrier] (fun p => g p)) ∧
          KPContLocalEnergy.WeakEquation D.data (a s) w g := by
    intro s hs
    refine ⟨SF.xi i x chart m A hA ⟨u s, hdom s hs⟩ (a s),
      SF.value_restriction i x chart m A hA ⟨u s, hdom s hs⟩ (a s),
      SF.rhs i x chart m A hA ⟨u s, hdom s hs⟩ (a s), ?_,
      SF.weak_equation i x chart m A hA ⟨u s, hdom s hs⟩ (a s)⟩
    simpa only [SF.rhs_restriction] using hsource s hs
  have hex : ∀ s ∈ Ω, ∃ f : Space (KPCuspLogShape.dimension F * 3) → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f A.carrier ∧
        (f =ᵐ[volume.restrict A.carrier] (fun p => RA (u s) p)) := by
    intro s hs
    obtain ⟨w, hw, g, hg, heq⟩ := hweak s hs
    obtain ⟨f, hf, hrep⟩ := CoefficientRestriction.weighted_smooth_representative A D.data
      D.lowerDensity_pos D.lowerEllipticity_pos D.smooth_near_closed
      (a s) w g (h s) (hforcing_smooth.1 s hs) hg heq
    exact ⟨f, hf, by simpa only [hw] using hrep⟩
  let f : ℂ → Space (KPCuspLogShape.dimension F * 3) → ℂ := fun s =>
    if hs : s ∈ Ω then (hex s hs).choose else 0
  have hf : ∀ s ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (f s) A.carrier ∧
      (f s =ᵐ[volume.restrict A.carrier] (fun p => RA (u s) p)) := by
    intro s hs
    simpa only [f, dif_pos hs] using (hex s hs).choose_spec
  have hjets := CoefficientRestriction.weighted_solution_jet_continuity A D.data
    D.lowerDensity_pos D.lowerEllipticity_pos D.smooth_near_closed Ω hΩ a ha.continuousOn
    (fun s => RA (u s)) (RA.continuous.comp_continuousOn hu.continuousOn)
    h hforcing_smooth hforcing_sobolev hweak f hf
  have hhol := KPContLocalHolomorphyUpgrade.CauchyAssembly.holomorphy_of_jet_continuity
    A RA Ω hΩ u hu f hf hjets
  refine ⟨f, ?_, hhol.1, ?_⟩
  · intro s hs
    refine ⟨(hf s hs).1, (hf s hs).2, ?_⟩
    intro g hg hgae
    exact KPContLocalHolomorphyUpgrade.CauchyAssembly.eqOn_of_ae_eq_of_contDiffOn
      hg (hf s hs).1 (hgae.trans (hf s hs).2.symm)
  · intro s hs σ
    let τ := overlapCoordinate F ζ hζ U R P H i σ.val
    have hτ : Continuous τ := by
      letI := KPFiniteAdelicCuspEnds.canonicalAction_continuousConstSMul F
      exact (coordinates F).symm.continuous.comp
        ((continuous_const_smul (σ.val : KPCuspArithmetic.PGL2 F)).comp
          (coordinates F).continuous)
    have hrep : f s =ᵐ[volume.restrict A.carrier]
        (fun p => KPContLocalEnergy.value
          (SF.xi i x chart m A hA ⟨u s, hdom s hs⟩ (a s)) p) := by
      simpa only [SF.value_restriction] using (hf s hs).2
    exact CoefficientRestriction.continuous_covariance_of_ae A τ hτ
      (overlapCoordinate_quasiMeasurePreserving F ζ hζ U R P H i σ.val)
      _ (f s) (hf s hs).1.continuousOn hrep _
      (SF.stabilizer i x chart m A hA ⟨u s, hdom s hs⟩ (a s) σ)

end DedekindZetaZeroFree.KPContActualLocalSolutionFamily

namespace DedekindZetaZeroFree

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContActualLocalSolutionFamily

theorem kp_cont_actual_local_solution_family
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (chart : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x chart)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (a : ℂ → ℂ) (ha : DifferentiableOn ℂ a Ω)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U) (hu : DifferentiableOn ℂ u Ω)
    (forcing : ℂ → KPContActualSphericalRightFieldIdentification.LocalSection
      F ζ hζ U R P H i x chart)
    (hforcing_smooth : KPCutoffSource.ChartSmoothHolomorphicOn A
      (fun s => localFrameCoefficient F ζ hζ U R P H (forcing s) m) Ω)
    (hforcing_sobolev : ∀ B : LocalBall (KPCuspLogShape.dimension F * 3),
      KPContLocalCubeEmbedding.closedCarrier B ⊆ A.carrier →
      KPCutoffSource.ChartSobolevHolomorphicOn B
        (fun s => localFrameCoefficient F ζ hζ U R P H (forcing s) m) Ω)
    (hdom : ∀ s ∈ Ω, u s ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization).domain)
    (hsource : ∀ s (hs : s ∈ Ω),
      localFrameCoefficient F ζ hζ U R P H (forcing s) m =ᵐ[volume.restrict A.carrier]
        (fun p => restriction F ζ hζ U R P H i x chart m A hA
          ((KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization)
            ⟨u s, hdom s hs⟩ - a s • u s) p)) :
    Nonempty (Promotion F ζ hζ U R P H i x chart m A hA Ω u) := by
  classical
  obtain ⟨SF⟩ := kp_cont_actual_friedrichs_weak_chart F ζ hζ U R P H μG hμG hR realization
  obtain ⟨f, hf, hSCO, hcov⟩ := representative_family_core F ζ hζ U R P H μG hμG hR
    realization SF i x chart m A hA Ω hΩ a ha u hu forcing hforcing_smooth hforcing_sobolev
    hdom hsource
  refine ⟨⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun s hs => (hf s hs).1
  · exact fun s hs => (hf s hs).2.1
  · exact fun s hs g hg hgae => (hf s hs).2.2 g hg hgae
  · exact hcov
  · exact KPContSmoothPromotion.power_series_jet_holomorphy A Ω hΩ f hSCO
  · intro c r hr hclosed
    have hf' : ∀ s ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (f s) A.carrier ∧
        (f s =ᵐ[volume.restrict A.carrier]
          (fun p => restriction F ζ hζ U R P H i x chart m A hA (u s) p)) :=
      fun s hs => ⟨(hf s hs).1, (hf s hs).2.1⟩
    have hjets := KPContLocalHolomorphyUpgrade.CauchyAssembly.smooth_holomorphic_jet_continuous A Ω f hSCO
    obtain ⟨coeff, hspec, hsmooth⟩ :=
      KPContLocalHolomorphyUpgrade.CauchyAssembly.cauchy_coefficients_of_jet_continuity A
        (restriction F ζ hζ U R P H i x chart m A hA) Ω u hu f hf' hjets c r hr hclosed
    exact ⟨coeff, fun j => (hspec j).1, hsmooth, fun j g hg hgae => (hspec j).2 g hg hgae⟩

end DedekindZetaZeroFree

end
