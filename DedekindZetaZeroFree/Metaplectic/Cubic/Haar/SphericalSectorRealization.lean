module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.HaarLocalFiniteness
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.LineSectionIsometry

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFixedSectorRealization

open KPContSectorCoveredQuotientVocabulary KPContSectorQuotientRelationsComparison
open KPContSectorFixedPushforwardSupport KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

structure LevelRealization : Prop where

  actual_projection : piTilde F ζ hζ U = e F ζ hζ U ∘ coveredActualMap F ζ hζ U
  quotient_projection : IsQuotientMap (piTilde F ζ hζ U)
  covered_pushforward : coveredMeasure F ζ hζ R U =
    Measure.map (piTilde F ζ hζ U) R.quotientHaar

  support : LevelSupport F ζ hζ R P U

  local_finiteness : KPContSectorFixedMeasureLocalFiniteness.LevelLocalFiniteness
    F ζ hζ R P H U
  central_measure_preserving : ∀ ε : rootsOfUnity 3 F,
    MeasurePreserving (z F ζ hζ U ε) (coveredMeasure F ζ hζ R U)
      (coveredMeasure F ζ hζ R U)
  sector_closed : IsClosed (KPContSectorClosedLpSubspace.H F ζ hζ R U :
    Set (KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U))
  sector_complete : CompleteSpace (KPContSectorClosedLpSubspace.H F ζ hζ R U)

  sector_membership : ∀ u : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U,
    u ∈ KPContSectorClosedLpSubspace.H F ζ hζ R U ↔
      ∀ ε : rootsOfUnity 3 F,
        (u : CoveredSpherical F ζ hζ U → ℂ) ∘ z F ζ hζ U ε =ᵐ[
          coveredMeasure F ζ hζ R U]
            (chi F ζ hζ ε : ℂ) • (u : CoveredSpherical F ζ hζ U → ℂ)

  line_l2 : KPContSectorLineL2Isometry.RealizationIdentities F ζ hζ U R P H

  sector_line_norm : ∀ u : KPContSectorClosedLpSubspace.H F ζ hζ R U,
    ∃ s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H,
      KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H u =
        KPContSectorLineL2Isometry.mk F ζ hζ U R P H s ∧
      ‖u‖ ^ 2 = (KPContSectorLineL2Isometry.normIntegral F ζ hζ U R P H s.val).toReal

  norm_integrals : ∀ f : GenuineCoveredScalars F ζ hζ U, Measurable f.val →
    KPContSectorFixedLineNormIntegrals.NormIdentities F ζ hζ U R P H f

  orbit_stabilizer : ∀ v : CoveredSpherical F ζ hζ U,
    Nat.card (MulAction.orbit (rootsOfUnity 3 F) v) *
      Nat.card (MulAction.stabilizer (rootsOfUnity 3 F) v) = 3
  fiber_repetitions : ∀ v w : CoveredSpherical F ζ hζ U,
    q F ζ hζ U w = q F ζ hζ U v →
      Nat.card {ε : rootsOfUnity 3 F // z F ζ hζ U ε v = w} =
        Nat.card (MulAction.stabilizer (rootsOfUnity 3 F) v)

  finite_fiber_average : ∀ (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) v,
    KPContSectorFiniteOrbitIntegral.centralAverage F ζ hζ U ψ v =
      KPContSectorFiniteOrbitIntegral.distinctOrbitAverage F ζ hζ U ψ v
  scalar_descent : ∀ (f : GenuineCoveredScalars F ζ hζ U)
      (x : SymmetricSpace F) (c : FiniteCover F ζ hζ),
    (J F ζ hζ U f).val (x,c) =
      f.val (Quotient.mk (coveredRelation F ζ hζ U) (x,c))

  group_lift : ∀ (f : GenuineCoveredScalars F ζ hζ U)
      (a : KPSmoothActualFlowData.GInfinity F) (c : FiniteCover F ζ hζ),
    f.val (piTilde F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        (c : ActualCover F ζ hζ)))) =
          (J F ζ hζ U f).val (archBasepoint F a,c)

  smooth_realization : ∀ f : smoothCovered F ζ hζ U,
    (smoothS F ζ hζ U R P H f).val = S F ζ hζ U R P H f.val
  smooth_iff : ∀ f : GenuineCoveredScalars F ζ hζ U,
    IsSmoothCovered F ζ hζ U f ↔
      IsSmoothSections F ζ hζ U R P H (S F ζ hζ U R P H f)
  smooth_actual_charts : ∀ s : Sections F ζ hζ U R P H,
    IsSmoothSections F ζ hζ U R P H s ↔
      IsSmoothOrbifoldCuspSections F ζ hζ U R P H s

  phase_formula : ∀ (f : GenuineCoveredScalars F ζ hζ U)
      (i : Fin (H.atlas U).componentCount) (ε : rootsOfUnity 3 F)
      (x : SymmetricSpace F),
    f.val (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H
      ⟨i, Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε,x)⟩) =
        (chi F ζ hζ ε : ℂ) * (S F ζ hζ U R P H f i).val x
  chart_exists : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F),
    Nonempty (KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
  chart_isotropy_finite : ∀ (i : Fin (H.atlas U).componentCount)
      (x : SymmetricSpace F)
      (_O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x),
    Finite (MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) x)

  frame_unitary : ∀ (x : SymmetricSpace F) (v : Coefficient F ζ hζ U),
    ‖liftFrame F ζ hζ U x v‖ = ‖v‖
  frame_equivariant : ∀ (i : Fin (H.atlas U).componentCount)
      (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
      (x : SymmetricSpace F) (v : Coefficient F ζ hζ U),
    liftFrame F ζ hζ U ((γ : KPCuspArithmetic.PGL2 F) • x)
      (phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ) v) =
        phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ)
          (liftFrame F ζ hζ U x v)

  chart_restriction : ∀ (f : GenuineCoveredScalars F ζ hζ U)
      (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
      (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) (y : O.neighborhood),
    f.val (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
      (Quotient.mk _ (m,y))).val =
        (phaseCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) i m y.val : ℂ)
  cusp_restriction : ∀ (f : GenuineCoveredScalars F ζ hζ U)
      (i : Fin (H.atlas U).componentCount)
      (j : Fin ((H.atlas U).cuspAtlas i).cuspCount) (p : KPCuspCharts.Cross F) (t : ℝ),
    (cuspCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) i j (p,t) : ℂ) =
      (J F ζ hζ U f).val
        (((H.atlas U).cuspAtlas i).representative j • KPCuspCharts.toArch F (p,t),
          (H.atlas U).representative i)

  cusp_transition : ∀ (s : Sections F ζ hζ U R P H)
      (i : Fin (H.atlas U).componentCount)
      (j : Fin ((H.atlas U).cuspAtlas i).cuspCount)
      (g : KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
        (((H.atlas U).cuspAtlas i).cusp j) (((H.atlas U).cuspAtlas i).representative j))
      (p : KPCuspCharts.Cross F) (t : ℝ),
    let γ := KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
      (((H.atlas U).cuspAtlas i).cusp j) (((H.atlas U).cuspAtlas i).representative j) g
    cuspCoefficient F ζ hζ U R P H s i j
      ((((H.atlas U).cuspAtlas i).geometry j).crossAction g p,t) =
        phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ)
          (cuspCoefficient F ζ hζ U R P H s i j (p,t)) ∧
    ‖cuspCoefficient F ζ hζ U R P H s i j
      ((((H.atlas U).cuspAtlas i).geometry j).crossAction g p,t)‖ =
        ‖cuspCoefficient F ζ hζ U R P H s i j (p,t)‖

  cusp_atlas_overlap : ∀ (s : Sections F ζ hζ U R P H)
      (i : Fin (H.atlas U).componentCount)
      (j : Fin ((H.atlas U).cuspAtlas i).cuspCount),
    let D := ((H.atlas U).cuspAtlas i).parabolic j
    let G := ((H.atlas U).cuspAtlas i).geometry j
    ∀ (a b : Fin G.atlas.chartCount)
      (u : G.atlas.shapeLift a) (v : G.atlas.shapeLift b),
      (QuotientAddGroup.mk u.val : KPCuspCharts.Base F H.totallyComplex
        D.E D.integralUnits) = QuotientAddGroup.mk v.val →
      ∃ g : KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
        (((H.atlas U).cuspAtlas i).cusp j) (((H.atlas U).cuspAtlas i).representative j),
        v.val = u.val + KPCuspLogShape.logarithm F H.totallyComplex D.E
          D.integralUnits (Additive.ofMul (D.ratio g)) ∧
        (∀ z : KPCuspCharts.Torus F D.L,
          G.atlas.lift (z,u.val) = G.atlas.lift (G.torusAction (D.ratio g) z,v.val)) ∧
        (∀ (p : KPCuspCharts.Cross F) (t : ℝ),
          ‖cuspCoefficient F ζ hζ U R P H s i j (G.crossAction g p,t)‖ =
            ‖cuspCoefficient F ζ hζ U R P H s i j (p,t)‖)
  support_image : ∀ f : GenuineCoveredScalars F ζ hζ U,
    tsupport (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f)) =
      q F ζ hζ U '' tsupport f.val
  compact_support : ∀ f : GenuineCoveredScalars F ζ hζ U,
    HasCompactSupport f.val ↔
      HasCompactSupport (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f))

end DedekindZetaZeroFree.KPContActualFixedSectorRealization

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorQuotientRelationsComparison
open KPContSectorFixedPushforwardSupport KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPMsFixedHaarDisintegration

end DedekindZetaZeroFree

end
