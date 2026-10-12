module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.CommutatorHilbertHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory Topology Filter

namespace DedekindZetaZeroFree

 def jetPullback {n : ℕ} (L : Set (KPContLocalNorm.Space n)) (f : C(L, ℂ)) :
    KPContLocalNorm.Space n → ℂ :=
  fun x => if hx : x ∈ L then f ⟨x, hx⟩ else 0

theorem kp_cont_actual_commutator_chart_sobolev_holomorphy
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (_hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (_hΩ : Ω ⊆ KPContinuation.spectralDomain) (_hopen : IsOpen Ω)
    (f : ℂ → S) (_hf : DifferentiableOn ℂ f Ω)
    (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T) :
    ∀ D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ,
    ∀ i : Fin (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)).componentCount,
    ∀ q : KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U i,
    ∀ B : KPContLocalNorm.LocalBall (KPContActualCutoffChartJetHolomorphy.dimension F),
      Metric.closedBall B.center B.radius ⊆
        KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U q →
      KPCutoffSource.ChartSobolevHolomorphicOn B
        (KPContActualCutoffChartJetHolomorphy.pullback F ζ hζ C R P H U
          ι buffer Ω f χ D q true) Ω := by
  intro D i q B hBsub
  unfold KPCutoffSource.ChartSobolevHolomorphicOn
  intro k
  let L : Set (KPContLocalNorm.Space (KPContActualCutoffChartJetHolomorphy.dimension F)) :=
    Metric.closedBall B.center B.radius
  have hLc : IsCompact L := isCompact_closedBall B.center B.radius
  have hLdom : L ⊆ KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U q :=
    hBsub
  have hBsub' : B.carrier ⊆ L := Metric.ball_subset_closedBall
  have hBmeas : MeasurableSet B.carrier := Metric.isOpen_ball.measurableSet
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  obtain ⟨j, hjdiff, hjval, _⟩ :=
    (kp_cont_actual_cutoff_chart_jet_holomorphy F ζ hζ C R P H U _hR buffer ι _hι
      _hStage Ω _hΩ _hopen f _hf χ D i q B hBsub).compact_jets true L hLc hLdom k
  haveI : IsFiniteMeasure (volume.restrict B.carrier) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne

  have hgcont : ∀ f : C(L, ℂ), ContinuousOn (jetPullback L f) L := by
    intro f
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : L.domRestrict (jetPullback L f) = f := by
      funext x
      simp only [Set.domRestrict_apply, jetPullback, dif_pos x.2, Subtype.eta]
    rw [hEq]
    exact f.continuous
  have hmeas : ∀ f : C(L, ℂ), AEStronglyMeasurable (jetPullback L f)
      (volume.restrict B.carrier) :=
    fun f => (hgcont f).aestronglyMeasurable_of_subset_isCompact hLc hBmeas hBsub'
  have hbound : ∀ f : C(L, ℂ),
      ∀ᵐ x ∂(volume.restrict B.carrier), ‖jetPullback L f x‖ ≤ ‖f‖ := by
    intro f
    refine ae_restrict_of_forall_mem hBmeas ?_
    intro x hx
    have hxL : x ∈ L := hBsub' hx
    simp only [jetPullback, dif_pos hxL]
    exact ContinuousMap.norm_coe_le_norm f ⟨x, hxL⟩
  have hgmem : ∀ f : C(L, ℂ), MemLp (jetPullback L f) 2 (volume.restrict B.carrier) :=
    fun f => MemLp.of_bound (hmeas f) ‖f‖ (hbound f)

  let phiLin : C(L, ℂ) →ₗ[ℂ] KPContLocalNorm.BallL2 B :=
    { toFun := fun f => (hgmem f).toLp (jetPullback L f)
      map_add' := by
        intro f₁ f₂
        apply Lp.ext
        filter_upwards [(hgmem (f₁ + f₂)).coeFn_toLp, (hgmem f₁).coeFn_toLp,
          (hgmem f₂).coeFn_toLp,
          Lp.coeFn_add ((hgmem f₁).toLp (jetPullback L f₁))
            ((hgmem f₂).toLp (jetPullback L f₂))] with x h12 h1 h2 hadd
        rw [h12, hadd]
        simp only [Pi.add_apply, h1, h2]
        by_cases hx : x ∈ L <;> simp [jetPullback, hx]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(hgmem (c • f)).coeFn_toLp, (hgmem f).coeFn_toLp,
          Lp.coeFn_smul c ((hgmem f).toLp (jetPullback L f))] with x hcf hf hsmul
        rw [hcf]
        rw [show ⇑((RingHom.id ℂ) c • (hgmem f).toLp (jetPullback L f)) x =
            c • ⇑((hgmem f).toLp (jetPullback L f)) x from hsmul]
        simp only [hf]
        by_cases hx : x ∈ L <;> simp [jetPullback, hx] }
  let c₀ : ℝ := ((measureUnivNNReal (volume.restrict B.carrier)) ^
    ((2 : ℝ≥0∞).toReal)⁻¹ : ℝ≥0)
  let phi : C(L, ℂ) →L[ℂ] KPContLocalNorm.BallL2 B := phiLin.mkContinuous c₀ (by
    intro f
    have hle : ‖(hgmem f).toLp (jetPullback L f)‖ ≤ c₀ * ‖f‖ := by
      have h := Lp.norm_le_of_ae_bound (p := 2) (C := ‖f‖) (norm_nonneg f)
        (by
          filter_upwards [(hgmem f).coeFn_toLp, hbound f] with x hx hb
          rw [hx]; exact hb)
      simpa [c₀] using h
    simpa [phiLin, LinearMap.mkContinuous_apply] using hle)
  refine ⟨fun s α => phi (j s α), ?_, ?_⟩
  ·
    apply differentiableOn_pi.2
    intro α
    have h1 : DifferentiableOn ℂ (fun s => (j s) α) Ω :=
      ((ContinuousLinearMap.proj α : (KPContLocalNorm.MultiIndex
          (KPContActualCutoffChartJetHolomorphy.dimension F) k → C(L, ℂ)) →L[ℂ]
          C(L, ℂ)).differentiable.comp_differentiableOn hjdiff)
    exact phi.differentiable.comp_differentiableOn h1
  · intro s hs α
    have hg_s : ∀ᵐ x ∂(volume.restrict B.carrier),
        jetPullback L (j s α) x =
          KPContLocalNorm.coordinateDerivative α
            (KPContActualCutoffChartJetHolomorphy.pullback F ζ hζ C R P H U
              ι buffer Ω f χ D q true s) x := by
      refine ae_restrict_of_forall_mem hBmeas ?_
      intro x hx
      have hxL : x ∈ L := hBsub' hx
      simp only [jetPullback, dif_pos hxL]
      exact hjval s hs α ⟨x, hxL⟩
    refine ⟨MemLp.ae_eq hg_s (hgmem (j s α)), ?_⟩
    have h1 : (fun x => phi (j s α) x) =ᵐ[volume.restrict B.carrier]
        jetPullback L (j s α) := by
      have hphi : phi (j s α) = (hgmem (j s α)).toLp (jetPullback L (j s α)) := by
        simp [phi, phiLin, LinearMap.mkContinuous_apply]
      rw [hphi]
      exact (hgmem (j s α)).coeFn_toLp
    exact h1.trans hg_s

end DedekindZetaZeroFree

end
