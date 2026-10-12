module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas
public import DedekindZetaZeroFree.Eisenstein.Continuation.PoleClearedSmoothResolvent

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContSmoothPromotion

open MeasureTheory
open KPContLocalNorm KPContLocalOrbifold

section SameOperator
variable {X S T V I : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (μ : Measure X)
    (ι : S →ₗ[ℂ] Lp ℂ 2 μ) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hscalar : DenseRange ι) (hcotangent : DenseRange j)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w)))

local notation "Δ" => KPTestFriedrichs.laplacian ι hι j hj A B hscalar hcotangent hgreen

structure OperatorAtlas (n : ℕ) where
  chart : I → LineChart n
  smooth : Submodule ℂ (X → ℂ)
  pullback : I → (X → ℂ) →ₗ[ℂ] (Space n → ℂ)
  restriction : ∀ i, Lp ℂ 2 μ →L[ℂ] BallL2 (chart i).outer
  chartProjection : I → Space n → X
  chartProjection_continuous : ∀ i, ContinuousOn (chartProjection i) (chart i).outer.carrier
  chartImage : I → Set X
  chartImage_eq : ∀ i, chartImage i = chartProjection i '' (chart i).outer.carrier
  chartImage_open : ∀ i, IsOpen (chartImage i)
  chart_cover : (⋃ i, chartImage i) = Set.univ

  measure_comparison : ∀ i (f : X → ℂ), f ∈ smooth → MemLp f 2 μ →
    chartL2Norm (chart i) (chart i).outer (pullback i f) ≤
      Real.sqrt (∫ x in chartImage i, ‖f x‖ ^ 2 ∂μ)
  smooth_iff : ∀ f : X → ℂ, f ∈ smooth ↔
    ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (pullback i f) (chart i).outer.carrier ∧
      Equivariant (chart i) (chart i).outer.carrier (pullback i f)
  restriction_represents : ∀ (f : X → ℂ), f ∈ smooth →
    ∀ (u : Lp ℂ 2 μ), (f =ᵐ[μ] (fun x => u x)) →
      ∀ i, (pullback i f) =ᵐ[volume.restrict (chart i).outer.carrier]
        (fun x => restriction i u x)

  testRepresentative : S →ₗ[ℂ] smooth
  test_represents : ∀ s, (testRepresentative s : X → ℂ) =ᵐ[μ]
    (fun x => ι s x)

  domain_weak_equation : ∀ u : (Δ).domain, ∀ i,
    ∃ w : IntegerSobolev (chart i).outer 1,
      KPContLocalEnergy.Represents w (fun x => restriction i (u : Lp ℂ 2 μ) x) ∧
      AEEquivariant (chart i) (chart i).outer (fun x => KPContLocalEnergy.value w x) ∧
      KPContLocalEnergy.WeakEquation (chart i).coefficients 0 w
        (restriction i (Δ u))

  smooth_descent : ∀ (u : Lp ℂ 2 μ) (f : I → Space n → ℂ),
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (f i) (chart i).outer.carrier) →
    (∀ i, Equivariant (chart i) (chart i).outer.carrier (f i)) →
    (∀ i, f i =ᵐ[volume.restrict (chart i).outer.carrier]
      (fun x => restriction i u x)) →
    ∃ W : X → ℂ, W ∈ smooth ∧ (W =ᵐ[μ] (fun x => u x)) ∧
      (∀ i, Set.EqOn (pullback i W) (f i) (chart i).outer.carrier) ∧
      (∀ W' : X → ℂ, W' ∈ smooth → (W' =ᵐ[μ] (fun x => u x)) → W' = W)

end SameOperator

private theorem polynomial_limit_holomorphic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (z₀ : ℂ) (r : ℝ)
    (a : ℕ → E) (f : ℂ → E)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ r,
      ‖(∑ q ∈ Finset.range M, (z - z₀) ^ q • a q) - f z‖ < ε) :
    DifferentiableOn ℂ f (Metric.ball z₀ r) := by
  have ht : TendstoUniformlyOn
      (fun M z => ∑ q ∈ Finset.range M, (z - z₀) ^ q • a q) f
      Filter.atTop (Metric.ball z₀ r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    exact Filter.eventually_atTop.mpr ⟨N, fun M hM z hz => by
      rw [dist_eq_norm, norm_sub_rev]
      exact hN M hM z (Metric.ball_subset_closedBall hz)⟩
  apply ht.tendstoLocallyUniformlyOn.differentiableOn _ Metric.isOpen_ball
  apply Filter.Eventually.of_forall
  intro M
  exact DifferentiableOn.fun_sum (fun q _ =>
    ((differentiableOn_id.sub_const z₀).pow q).smul_const (a q))

theorem power_series_jet_holomorphy {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (hO : IsOpen O) (u : ℂ → Space n → ℂ)
    (hu : SmoothCompactOpenHolomorphicOn B u O) :
    KPCutoffSource.ChartSmoothHolomorphicOn B u O := by
  classical
  have hs : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (u z) B.carrier :=
    fun z hz => KPContLocalHolomorphyUpgrade.smooth_forcing_at hu hz
  refine ⟨hs, ?_⟩
  intro K hK hKB m
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let j : ℂ → CompactJets K m := fun z =>
    if hz : z ∈ O then compactJet B K hKB (u z) (hs z hz) else 0
  have hj : ∀ z ∈ O, ∀ α, ∀ x : K,
      j z α x = coordinateDerivative α (u z) x := by
    intro z hz α x
    dsimp [j]
    rw [dif_pos hz]
    rfl
  refine ⟨j, ?_, hj⟩
  intro z₀ hz₀
  obtain ⟨ρ, hρ, hball, a, ha⟩ := hu z₀ hz₀
  let aj : ℕ → CompactJets K m := fun q => compactJet B K hKB (a q) (ha.1 q)
  have hhalf : 0 < ρ / 2 := by positivity
  have hconv : ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ (ρ / 2),
      ‖(∑ q ∈ Finset.range M, (z - z₀) ^ q • aj q) - j z‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := ha.2.2 K hK hKB m (ρ / 2) hhalf.le
      (by linarith) (ε / 2) (by positivity)
    refine ⟨N, fun M hM z hz => ?_⟩
    have hzρ : z ∈ Metric.ball z₀ ρ := Metric.closedBall_subset_ball (by linarith) hz
    have hzO := hball hzρ
    apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro α
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro x
    have hb := hN M hM z hz α x
    have he := KPContLocalHolomorphyUpgrade.CauchyAssembly.coordinate_derivative_taylor_remainder
      B a ha.1 (u z) (ha.2.1 z hzρ) (z - z₀) M α (hKB x.property)
    rw [he] at hb
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, hj z hzO]
    change ‖(∑ q ∈ Finset.range M, (z - z₀) ^ q * coordinateDerivative α (a q) x) -
      coordinateDerivative α (u z) x‖ ≤ ε / 2
    exact hb.le
  exact (polynomial_limit_holomorphic z₀ (ρ / 2) aj j hconv).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball] using hhalf)) |>.differentiableWithinAt

end DedekindZetaZeroFree.KPContSmoothPromotion

end
