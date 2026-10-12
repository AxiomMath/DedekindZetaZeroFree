module

public import Mathlib.Analysis.Complex.LocallyUniformLimit

@[expose] public section

noncomputable section
open Topology Filter
open scoped Topology

namespace DedekindZetaZeroFree.KPContCompactBanachSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem disk_series_holomorphic (f : ℂ → E) (a : ℕ → E)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hseries : ∀ t : ℝ, 0 ≤ t → t < r → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall c t,
        ‖(∑ j ∈ Finset.range M, (z-c)^j • a j) - f z‖ < ε) :
    DifferentiableOn ℂ f (Metric.ball c r) ∧
      ∀ z ∈ Metric.ball c r, HasSum (fun j => (z-c)^j • a j) (f z) := by
  let F : ℕ → ℂ → E := fun M z => ∑ j ∈ Finset.range M, (z-c)^j • a j
  have hu (t : ℝ) (ht : 0 ≤ t) (htr : t < r) :
      TendstoUniformlyOn F f atTop (Metric.closedBall c t) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N,hN⟩ := hseries t ht htr ε hε
    filter_upwards [eventually_ge_atTop N] with M hM z hz
    rw [dist_eq_norm_sub, norm_sub_rev]
    exact hN M hM z hz
  have hl : TendstoLocallyUniformlyOn F f atTop (Metric.ball c r) := by
    intro u hu' z hz
    have hz' : dist z c < r := hz
    obtain ⟨t,hzt,htr⟩ := exists_between hz'
    have ht : 0 ≤ t := (dist_nonneg).trans hzt.le
    refine ⟨Metric.closedBall c t, mem_nhdsWithin_of_mem_nhds ?_, (hu t ht htr) u hu'⟩
    exact mem_of_superset (Metric.isOpen_ball.mem_nhds hzt) Metric.ball_subset_closedBall
  constructor
  · apply hl.differentiableOn _ Metric.isOpen_ball
    filter_upwards with M
    apply Differentiable.differentiableOn
    apply Differentiable.fun_sum
    intro j hj
    exact ((differentiable_id.sub_const c).pow j).smul_const (a j)
  · intro z hz
    have ht : 0 ≤ dist z c := dist_nonneg
    have htr : dist z c < r := hz
    obtain ⟨t,hzt,htr'⟩ := exists_between htr
    have ht' : 0 < t := lt_of_le_of_lt ht hzt
    have hs : Tendsto (fun n => F n (c + t)) atTop (𝓝 (f (c+t))) :=
      (hu t ht'.le htr').tendsto_at
        (by simp [Complex.dist_eq,Complex.norm_real,abs_of_pos ht'])
    have hterm : Tendsto (fun n => (t : ℂ)^n • a n) atTop (𝓝 0) := by
      have hh := (hs.comp (tendsto_add_atTop_nat 1)).sub hs
      simpa [F,Finset.sum_range_succ] using hh
    obtain ⟨B,hB⟩ := (hterm.norm).bddAbove_range
    have hb (n : ℕ) : ‖(t : ℂ)^n • a n‖ ≤ B := hB (Set.mem_range_self n)
    have hn : Summable (fun n => ‖(z-c)^n • a n‖) := by
      have hratio : ‖z-c‖ / t < 1 :=
        (div_lt_one ht').mpr (by simpa [dist_eq_norm] using hzt)
      have hratio0 : 0 ≤ ‖z-c‖ / t := div_nonneg (norm_nonneg _) ht'.le
      have hgeom : Summable (fun n => B * (‖z-c‖ / t)^n) :=
        (summable_geometric_of_lt_one hratio0 hratio).mul_left B
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeom
      intro n
      have hh := mul_le_mul_of_nonneg_right (hb n) (pow_nonneg hratio0 n)
      rw [norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht',div_pow] at hh
      rw [norm_smul,norm_pow]
      have heq : t^n * ‖a n‖ * (‖z-c‖^n / t^n) = ‖z-c‖^n * ‖a n‖ := by
        field_simp
      rw [heq] at hh
      simpa only [div_pow] using hh
    apply (hasSum_iff_tendsto_nat_of_summable_norm hn).mpr
    exact (hu (dist z c) ht htr).tendsto_at (by simp)

theorem compact_pointwise_series {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : ℂ → C(X,ℂ)) (a : ℕ → C(X,ℂ)) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hseries : ∀ t : ℝ, 0 ≤ t → t < r → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall c t, ∀ x : X,
        ‖(∑ j ∈ Finset.range M, (z-c)^j * a j x) - f z x‖ < ε) :
    DifferentiableOn ℂ f (Metric.ball c r) ∧
      (∀ z ∈ Metric.ball c r, HasSum (fun j => (z-c)^j • a j) (f z)) ∧
      (∀ t : ℝ, 0 ≤ t → t < r → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall c t,
          ‖(∑ j ∈ Finset.range M, (z-c)^j • a j) - f z‖ < ε) := by
  have hs : ∀ t : ℝ, 0 ≤ t → t < r → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall c t,
        ‖(∑ j ∈ Finset.range M, (z-c)^j • a j) - f z‖ < ε := by
    intro t ht htr ε hε
    obtain ⟨N,hN⟩ := hseries t ht htr ε hε
    refine ⟨N,fun M hM z hz => (ContinuousMap.norm_lt_iff _ hε).mpr ?_⟩
    intro x
    simpa using hN M hM z hz x
  exact ⟨(disk_series_holomorphic f a c r hr hs).1,
    (disk_series_holomorphic f a c r hr hs).2, hs⟩

end DedekindZetaZeroFree.KPContCompactBanachSeries

end
