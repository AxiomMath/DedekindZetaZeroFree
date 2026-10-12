module

public import DedekindZetaZeroFree.Eisenstein.Continuation.IncomingCuspModes.Realization

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

 def inverseLinear (F : Type) [Field F] [NumberField F] (hd : 0 < KPCuspLogShape.dimension F) :
    KPArch.Space (KPCuspLogShape.dimension F) →ₗ[ℝ] KPCuspCharts.Coordinates F where
  toFun := (KPCuspCharts.toArchHomeomorph F hd).symm
  map_add' z w := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        ext i
        simp [KPCuspCharts.toArchHomeomorph, KPCuspLogShape.shapeCoordinates,
          KPCuspLogShape.meanHeight, Finset.sum_add_distrib]
        ring
    · simp [KPCuspCharts.toArchHomeomorph, KPCuspLogShape.meanHeight, Finset.sum_add_distrib]
      ring
  map_smul' c z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        ext i
        simp [KPCuspCharts.toArchHomeomorph, KPCuspLogShape.shapeCoordinates,
          KPCuspLogShape.meanHeight, Finset.mul_sum]
        rw [← Finset.mul_sum]
        ring
    · simp [KPCuspCharts.toArchHomeomorph, KPCuspLogShape.meanHeight]
      rw [← Finset.mul_sum]
      ring

private theorem inverse_smooth (F : Type) [Field F] [NumberField F] (hd : 0 < KPCuspLogShape.dimension F) :
    ContDiff ℝ (⊤ : ℕ∞) (KPCuspCharts.toArchHomeomorph F hd).symm :=
  (inverseLinear F hd).toContinuousLinearMap.contDiff

private theorem action_smooth (F : Type) [Field F] [NumberField F]
    (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : KPCuspGenuineMonodromy.SymmetricSpace F => γ • x) := by
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  rw [← hG]
  have he : (fun x : KPCuspGenuineMonodromy.SymmetricSpace F =>
      (Matrix.ProjGenLinGroup.mk G : KPCuspArithmetic.PGL2 F) • x) = KPCuspSiegel.glAction F G := by
    funext x; exact KPCuspSiegel.action_mk F G x
  rw [he]
  exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
    (fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F k).embedding G)).of_le le_top

theorem actual_end_local_smooth_lift
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (level F ζ hζ C R P H U) R P H T)
    (a : Cusps F ζ hζ C R P H U)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (y : KPCuspGenuineMonodromy.SymmetricSpace F)
    (hy : Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U))
      (y, (H.atlas (level F ζ hζ C R P H U)).representative i) ∈
        ends F ζ hζ C R P H U buffer a) :
    ∃ V : Set (KPCuspGenuineMonodromy.SymmetricSpace F), IsOpen V ∧ y ∈ V ∧
      ∃ ε : rootsOfUnity 3 F,
      ∃ z : KPCuspGenuineMonodromy.SymmetricSpace F → KPCuspCharts.Coordinates F,
        ContDiffOn ℝ (⊤ : ℕ∞) z V ∧
        ∀ y' ∈ V, buffer.τ < (z y').2 ∧
          coveredPoint F ζ hζ C R P H U a ε (z y') =
            Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
              (level F ζ hζ C R P H U))
              (y', (H.atlas (level F ζ hζ C R P H U)).representative i) := by
  let Vlevel := level F ζ hζ C R P H U
  let A := H.atlas Vlevel
  have hbase : KPContSectorCoveredQuotientVocabulary.q F ζ hζ Vlevel
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ Vlevel)
        (y, A.representative i)) ∈
      KPContActualCollarBuffer.endSet F ζ hζ Vlevel R P H buffer.τ a := hy
  rw [← buffer.lift_range a] at hbase
  obtain ⟨p, hp, hpbase⟩ := hbase
  have hq : KPContSectorCoveredQuotientVocabulary.q F ζ hζ Vlevel
      (coveredPoint F ζ hζ C R P H U a 1 p) =
      KPContSectorCoveredQuotientVocabulary.q F ζ hζ Vlevel
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ Vlevel)
        (y, A.representative i)) := by
    change Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ Vlevel)
      (_, _) = _
    simpa only [coveredPoint, map_one, one_mul,
      KPContSectorSmoothFramesSupport.cuspPoint,
      KPContFlatCuspIncomingEvaluation.atlas, KPContActualCollarBuffer.chartLift] using hpbase
  obtain ⟨ε, hε⟩ := (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ Vlevel _ _).mp hq
  have hpoint : coveredPoint F ζ hζ C R P H U a ε p =
      Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ Vlevel)
        (y, A.representative i) := by
    have ht := hε.symm
    unfold coveredPoint at ht
    simp only [map_one, one_mul] at ht
    change KPContSectorCoveredQuotientVocabulary.z F ζ hζ Vlevel ε
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ Vlevel)
        (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ Vlevel R P H a.1 a.2 p,
          A.representative a.1)) = _ at ht
    rw [KPContSectorCoveredQuotientVocabulary.z_mk] at ht
    exact ht
  obtain ⟨γ, u, harch, hfin⟩ := Quotient.exact hpoint
  let σ := ((H.atlas Vlevel).cuspAtlas a.1).representative a.2
  let δ := γ * σ
  let z := fun y' : KPCuspGenuineMonodromy.SymmetricSpace F =>
    (KPCuspCharts.toArchHomeomorph F buffer.positive_dimension).symm (δ⁻¹ • y')
  have hz : ContDiff ℝ (⊤ : ℕ∞) z :=
    (inverse_smooth F buffer.positive_dimension).comp (action_smooth F δ⁻¹)
  have hδ : y = δ • KPCuspCharts.toArch F p := by
    simpa only [coveredPoint, KPContSectorSmoothFramesSupport.cuspPoint, mul_smul,
      σ, δ] using harch
  have hzy : z y = p := by
    dsimp [z]
    rw [hδ, inv_smul_smul]
    exact (KPCuspCharts.toArchHomeomorph F buffer.positive_dimension).symm_apply_apply p
  refine ⟨{y' | buffer.τ < (z y').2}, ?_, ?_, ε, z, hz.contDiffOn, ?_⟩
  · exact isOpen_lt continuous_const hz.continuous.snd
  · change buffer.τ < (z y).2
    rwa [hzy]
  · intro y' hy'
    refine ⟨hy', Quotient.sound ?_⟩
    refine ⟨γ, u, ?_, hfin⟩
    change y' = γ • (σ • KPCuspCharts.toArch F (z y'))
    rw [← mul_smul]
    change y' = δ • (KPCuspCharts.toArchHomeomorph F buffer.positive_dimension) (z y')
    dsimp only [z]
    rw [(KPCuspCharts.toArchHomeomorph F buffer.positive_dimension).apply_symm_apply,
      smul_inv_smul]

end DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

end
