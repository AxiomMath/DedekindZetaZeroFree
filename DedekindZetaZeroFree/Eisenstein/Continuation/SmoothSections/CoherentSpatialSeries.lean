module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightTranslations.MovingCompactJetBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualCoherentSpatialSeries

open KPContLocalNorm KPContSectorSmoothFramesSupport
open KPContActualCommonDiskRightHolomorphy

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

 theorem coefficient_phase (u : Sections F ζ hζ U R P H)
    (A : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H)
    (ε : rootsOfUnity 3 F)
    (hε : A.phase = KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε) :
    KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A =
      fun x => (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        (u A.component).val (KPContActualChartRestrictionDensity.coordinates F x) := by
  funext x
  unfold KPContActualSmoothLineGluing.coefficient
  rw [hε, KPContActualChartRestrictionDensity.frameCoefficient_class,
    KPContSectorLineL2Isometry.scalarRepresentative_eq_symm,
    LinearEquiv.apply_symm_apply]

def coefficientMap (A : KPContActualSmoothLineGluing.ChartBall F ζ hζ U R P H) :
    Sections F ζ hζ U R P H →ₗ[ℂ] (Space (KPCuspLogShape.dimension F * 3) → ℂ) where
  toFun u := KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u A
  map_add' u v := by
    obtain ⟨ε, hε⟩ := QuotientGroup.mk'_surjective
      (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ U) A.phase
    rw [coefficient_phase F ζ hζ U R P H (u + v) A ε hε.symm,
      coefficient_phase F ζ hζ U R P H u A ε hε.symm,
      coefficient_phase F ζ hζ U R P H v A ε hε.symm]
    funext x
    exact mul_add _ _ _
  map_smul' c u := by
    obtain ⟨ε, hε⟩ := QuotientGroup.mk'_surjective
      (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ U) A.phase
    rw [coefficient_phase F ζ hζ U R P H (c • u) A ε hε.symm,
      coefficient_phase F ζ hζ U R P H u A ε hε.symm]
    funext x
    change _ * (c * _) = c * (_ * _)
    ring

private theorem compactJet_le {d m : ℕ} (B : LocalBall d)
    (K : Set (Space d)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (u : Space d → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ α : MultiIndex d m, ∀ x : K,
      ‖coordinateDerivative α u x‖ ≤ δ) :
    compactJetSeminorm m B K hK hKB u hu ≤ δ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro α
  exact (ContinuousMap.norm_le _ hδ).mpr (hb α)

theorem coherentSeries_moving_jets
    (W : ℂ → smoothSections F ζ hζ U R P H)
    (b : ℕ → smoothSections F ζ hζ U R P H) (c : ℂ) (ρ : ℝ)
    (hseries : CoherentSeries F ζ hζ U R P H W b c ρ)
    (C : Set (G F ζ hζ)) (hC : IsCompact C)
    (X : Set (ArchCoordinates F)) (hX : IsCompact X) (hXd : X ⊆ archDomain F)
    (D : Combination F) (n : ℕ) :
    ∀ r : ℝ, 0 ≤ r → r < ρ → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ L ≥ N, ∀ s ∈ Metric.closedBall c r, ∀ g ∈ C, ∀ x ∈ X,
        ‖iteratedFDeriv ℝ n
          (fun y => rightCombination F ζ hζ D
            (lift F ζ hζ U R P H
              ((∑ j ∈ Finset.range L, (s - c) ^ j • b j) - W s).val)
            (g * archChart F ζ hζ y)) x‖ < ε := by
  intro r hr hrρ ε hε
  obtain ⟨cover, M, hM, hbnd⟩ :=
    ActualMovingCompactGeometry.actual_moving_compact_joint_jet_bound
      F ζ hζ U R P H C hC X hX hXd D n
  let δ := ε / (M * (cover.count + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlocal (j : Fin cover.count) := hseries (cover.chart j)
  choose N hN using fun j : Fin cover.count =>
    (hlocal j).2.2 (cover.compact j) (cover.isCompact j) (cover.contained j)
      (n + KPContRightJets.combinationOrder D) r hr hrρ δ hδ
  refine ⟨Finset.univ.sup N, ?_⟩
  intro L hL s hs g hg x hx
  let u : smoothSections F ζ hζ U R P H :=
    (∑ j ∈ Finset.range L, (s - c) ^ j • b j) - W s
  have hcoeff (j : Fin cover.count) :
      KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u.val (cover.chart j) =
        fun y => (∑ q ∈ Finset.range L, (s - c) ^ q *
          KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H (b q).val (cover.chart j) y) -
          KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H (W s).val (cover.chart j) y := by
    change coefficientMap F ζ hζ U R P H (cover.chart j) u.val = _
    simp only [u, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
      map_sub, map_sum, map_smul]
    funext y
    simp [coefficientMap, Finset.sum_apply]
  have hu (j : Fin cover.count) : ContDiffOn ℝ (⊤ : ℕ∞)
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u.val (cover.chart j))
      (cover.chart j).ball.carrier := by
    rw [hcoeff j]
    exact (ContDiffOn.sum (fun q _ => contDiffOn_const.mul ((hlocal j).1 q))).sub
      ((hlocal j).2.1 s (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hs).trans_lt hrρ)))
  have hp (j : Fin cover.count) : compactJetSeminorm
      (n + KPContRightJets.combinationOrder D) (cover.chart j).ball
      (cover.compact j) (cover.isCompact j) (cover.contained j)
      (KPContActualSmoothLineGluing.coefficient F ζ hζ U R P H u.val (cover.chart j))
      (hu j) ≤ δ := by
    apply compactJet_le _ _ _ _ _ _ hδ.le
    intro α y
    rw [hcoeff j]
    exact le_of_lt (hN j L ((Finset.le_sup (Finset.mem_univ j)).trans hL) s hs α y)
  have hbound := hbnd u.val hu g hg x hx
  apply lt_of_le_of_lt hbound
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hp j)) hM.le)
  have hden : 0 < M * (cover.count + 1) := by positivity
  have heq : M * (cover.count + 1) * δ = ε := by
    dsimp [δ]
    field_simp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualCoherentSpatialSeries

end
