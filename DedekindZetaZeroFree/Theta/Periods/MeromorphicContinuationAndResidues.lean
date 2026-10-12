module

public import DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
open scoped Topology Classical NumberField
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualPeriodContinuation

variable {G₀ H J : Type*} [TopologicalSpace G₀] [AddCommGroup H] [Module ℂ H]
variable (D₀ : J → H →ₗ[ℂ] C(G₀, ℂ))

theorem powerSeries_uniform (z₀ : ℂ) (ρ : ℝ) (a : ℕ → H) (f : ℂ → H)
    (ha : KPGlobalEisensteinData.SmoothPowerSeriesOn D₀ z₀ ρ a f)
    (j : J) (g : G₀) (r : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ) :
    TendstoUniformlyOn
      (fun M z => ∑ q ∈ Finset.range M, (z - z₀) ^ q * D₀ j (a q) g)
      (fun z => D₀ j (f z) g) atTop (Metric.closedBall z₀ r) := by
  let i : KPGlobalEisensteinData.DifferentialCompact G₀ J :=
    ⟨{g}, isCompact_singleton, j⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := ha i r hr hrρ ε hε
  filter_upwards [eventually_ge_atTop N] with M hM
  intro z hz
  have hbound : ‖D₀ j ((∑ q ∈ Finset.range M, (z - z₀) ^ q • a q) - f z) g‖ ≤
      KPGlobalEisensteinData.smoothSeminorm D₀ i
        ((∑ q ∈ Finset.range M, (z - z₀) ^ q • a q) - f z) :=
    (KPGlobalEisensteinData.derivativeRestriction D₀ i _).norm_coe_le_norm ⟨g, rfl⟩
  have h := lt_of_le_of_lt hbound (hN M hM z hz)
  simpa only [map_sub, map_sum, map_smul, ContinuousMap.sub_apply,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    dist_eq_norm, norm_sub_rev] using h

theorem powerSeries_analytic (z₀ : ℂ) (ρ : ℝ) (a : ℕ → H) (f : ℂ → H)
    (ha : KPGlobalEisensteinData.SmoothPowerSeriesOn D₀ z₀ ρ a f)
    (j : J) (g : G₀) :
    AnalyticOnNhd ℂ (fun z => D₀ j (f z) g) (Metric.ball z₀ ρ) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  apply TendstoLocallyUniformlyOn.differentiableOn
    (F := fun M : ℕ => fun z : ℂ => ∑ q ∈ Finset.range M, (z - z₀) ^ q * D₀ j (a q) g)
    (φ := atTop) _ _ Metric.isOpen_ball
  · apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro z hz
    obtain ⟨r, hzr, hrρ⟩ := exists_between (Metric.mem_ball.mp hz)
    have hr : 0 < r := lt_of_le_of_lt dist_nonneg hzr
    refine ⟨Metric.closedBall z₀ r, ?_,
      powerSeries_uniform D₀ z₀ ρ a f ha j g r hr.le hrρ⟩
    exact mem_of_superset (nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hzr))
      Metric.ball_subset_closedBall
  · exact Eventually.of_forall (fun M => by
      fun_prop)

theorem holomorphic_analytic (f : ℂ → H) (O : Set ℂ)
    (hf : KPGlobalEisensteinData.SmoothHolomorphicOn D₀ f O) (j : J) (g : G₀) :
    AnalyticOnNhd ℂ (fun z => D₀ j (f z) g) O := by
  intro z hz
  obtain ⟨ρ, hρ, hb, a, ha⟩ := hf z hz
  exact powerSeries_analytic D₀ z ρ a f ha j g z (Metric.mem_ball_self hρ)

theorem meromorphic_scalar (f : ℂ → H) (O : Set ℂ)
    (hf : KPRankOneContinuation.SmoothMeromorphicOn D₀ f O) (j : J) (g : G₀) :
    MeromorphicOn (fun z => D₀ j (f z) g) O := by
  intro z₀ hz₀
  obtain ⟨ρ, m, a, cleared, hρ, hb, ha, hc⟩ := hf z₀ hz₀
  have han : AnalyticAt ℂ (fun z => D₀ j (cleared z) g) z₀ :=
    powerSeries_analytic D₀ z₀ ρ a cleared ha j g z₀ (Metric.mem_ball_self hρ)
  have hm : MeromorphicAt
      (fun z => (D₀ j (cleared z) g) / (z - z₀) ^ m) z₀ :=
    han.meromorphicAt.div ((MeromorphicAt.id z₀).sub (MeromorphicAt.const z₀ z₀) |>.pow m)
  apply hm.congr
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hρ),
    self_mem_nhdsWithin] with z hz hne
  have hn : z ≠ z₀ := hne
  rw [hc z hz hn, map_smul, ContinuousMap.smul_apply, smul_eq_mul]
  exact mul_div_cancel_left₀ _ (pow_ne_zero m (sub_ne_zero.mpr hn))

theorem meromorphic_identity_germ {f k : ℂ → ℂ} {O : Set ℂ}
    (hf : MeromorphicOn f O) (hk : MeromorphicOn k O)
    (hO : IsPreconnected O) {z₁ z₀ : ℂ} (hz₁ : z₁ ∈ O) (hz₀ : z₀ ∈ O)
    (hagree : f =ᶠ[𝓝[≠] z₁] k) : f =ᶠ[𝓝[≠] z₀] k := by
  have hsub : MeromorphicOn (fun z => f z - k z) O := fun z hz => (hf z hz).sub (hk z hz)
  have hzero : ∀ᶠ z in 𝓝[≠] z₁, f z - k z = 0 := hagree.mono (fun z hz => sub_eq_zero.mpr hz)
  have htop : meromorphicOrderAt (fun z => f z - k z) z₁ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr hzero
  have hz : ∀ᶠ z in 𝓝[≠] z₀, f z - k z = 0 := meromorphicOrderAt_eq_top_iff.mp
    (hsub.meromorphicOrderAt_eq_top_of_isPreconnected hO hz₁ hz₀ htop)
  exact hz.mono (fun z hz => sub_eq_zero.mp hz)

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualPeriodContinuation

end
