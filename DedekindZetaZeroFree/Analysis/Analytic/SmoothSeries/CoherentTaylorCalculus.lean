module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
open scoped Classical Topology BigOperators NNReal ENNReal
open Filter MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CoherentTaylorCalculus
open KPGlobalEisensteinData
variable {G V J : Type*} [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable (D : J → V →ₗ[ℂ] C(G,ℂ))

private theorem series_uniform {z₀ : ℂ} {ρ : ℝ} {a : ℕ → V} {f : ℂ → V}
    (ha : SmoothPowerSeriesOn D z₀ ρ a f)
    (i : DifferentialCompact G J) {r : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) :
    TendstoUniformlyOn
      (fun M z => ∑ k ∈ Finset.range M, (z-z₀)^k • derivativeRestriction D i (a k))
      (fun z => derivativeRestriction D i (f z)) atTop (Metric.closedBall z₀ r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := ha i r hr hrρ ε hε
  filter_upwards [eventually_ge_atTop N] with M hM
  intro z hz
  have h := hN M hM z hz
  change ‖derivativeRestriction D i
    ((∑ k ∈ Finset.range M, (z-z₀)^k • a k) - f z)‖ < ε at h
  simpa only [map_sub, map_sum, map_smul, dist_eq_norm, norm_sub_rev] using h

private theorem series_terms_zero {z₀ : ℂ} {ρ : ℝ} {a : ℕ → V} {f : ℂ → V}
    (ha : SmoothPowerSeriesOn D z₀ ρ a f)
    (i : DifferentialCompact G J) {r : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) :
    Tendsto (fun k => ‖derivativeRestriction D i (a k)‖ * r^k) atTop (𝓝 0) := by
  let z := z₀ + (r:ℂ)
  have hz : z ∈ Metric.closedBall z₀ r := by simp [z, dist_eq_norm, abs_of_nonneg hr]
  have ht := (series_uniform D ha i hr hrρ).tendsto_at hz
  have hs := ht.comp (tendsto_add_atTop_nat 1)
  have hd := hs.sub ht
  have he (k : ℕ) : (∑ j ∈ Finset.range (k+1), (z-z₀)^j • derivativeRestriction D i (a j)) -
      (∑ j ∈ Finset.range k, (z-z₀)^j • derivativeRestriction D i (a j)) =
      (z-z₀)^k • derivativeRestriction D i (a k) := by rw [Finset.sum_range_succ]; abel
  have heq : (fun k => (∑ j ∈ Finset.range (k+1), (z-z₀)^j • derivativeRestriction D i (a j)) -
      (∑ j ∈ Finset.range k, (z-z₀)^j • derivativeRestriction D i (a j))) =
      (fun k => (z-z₀)^k • derivativeRestriction D i (a k)) := funext he
  change Tendsto (fun k => (∑ j ∈ Finset.range (k+1), (z-z₀)^j • derivativeRestriction D i (a j)) -
      (∑ j ∈ Finset.range k, (z-z₀)^j • derivativeRestriction D i (a j))) atTop
      (𝓝 (derivativeRestriction D i (f z) - derivativeRestriction D i (f z))) at hd
  rw [heq, sub_self] at hd
  have hn := hd.norm
  simpa [z, norm_smul, norm_pow, abs_of_nonneg hr, mul_comm] using hn

 def compactSeries (i : DifferentialCompact G J) (a : ℕ → V) :
    FormalMultilinearSeries ℂ ℂ C(i.compact,ℂ) :=
  fun k => ContinuousMultilinearMap.mkPiRing ℂ (Fin k) (derivativeRestriction D i (a k))

private theorem series_radius {z₀ : ℂ} {ρ : ℝ} {a : ℕ → V} {f : ℂ → V}
    (ha : SmoothPowerSeriesOn D z₀ ρ a f) (_hρ : 0 < ρ) (i : DifferentialCompact G J) :
    ENNReal.ofReal ρ ≤ (compactSeries D i a).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  rw [ENNReal.coe_lt_ofReal] at hr
  have ht := series_terms_zero D ha i r.coe_nonneg hr
  apply (compactSeries D i a).le_radius_of_tendsto (l := 0)
  simpa only [compactSeries, ContinuousMultilinearMap.norm_mkPiRing] using ht

 theorem series_onBall {z₀ : ℂ} {ρ : ℝ} {a : ℕ → V} {f : ℂ → V}
    (ha : SmoothPowerSeriesOn D z₀ ρ a f) (hρ : 0 < ρ) (i : DifferentialCompact G J) :
    HasFPowerSeriesOnBall (fun z => derivativeRestriction D i (f z))
      (compactSeries D i a) z₀ (ENNReal.ofReal ρ) := by
  refine ⟨series_radius D ha hρ i, by positivity, ?_⟩
  intro y hy
  have hyr : ‖y‖ < ρ := by
    rw [Metric.eball_ofReal, Metric.mem_ball, dist_zero_right] at hy
    exact hy
  obtain ⟨r,hr,hrρ⟩ := exists_between hyr
  have hr0 : 0 ≤ r := norm_nonneg y |>.trans hr.le
  have hz : z₀+y ∈ Metric.closedBall z₀ r := by simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hr.le
  have ht := (series_uniform D ha i hr0 hrρ).tendsto_at hz
  have hy' : y ∈ Metric.eball 0 (compactSeries D i a).radius :=
    Metric.eball_subset_eball (series_radius D ha hρ i) hy
  have hs := FormalMultilinearSeries.summable_norm_apply (compactSeries D i a) hy'
  apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
  simpa only [compactSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    add_sub_cancel_left] using ht

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CoherentTaylorCalculus

end
