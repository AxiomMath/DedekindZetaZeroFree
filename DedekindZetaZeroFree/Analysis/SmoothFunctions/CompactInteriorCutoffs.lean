module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open KPContLocalNorm
open Set Filter Topology MeasureTheory

theorem exists_smooth_cutoff {n : ℕ} (hn : 0 < n)
    (U K : Set (Space n)) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (η : Space n → ℝ) (N : Set (Space n)),
      IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x ∈ N, η x = 1) ∧
      (∀ (j : Fin n) (x : Space n), x ∈ N →
        fderiv ℝ η x (EuclideanSpace.single j 1) = 0) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space n,
        ‖η x‖ ≤ C ∧ ∀ j : Fin n,
          ‖fderiv ℝ η x (EuclideanSpace.single j 1)‖ ≤ C) := by
  classical

  have hball : ∀ x : K, ∃ e : ℝ, 0 < e ∧ Metric.closedBall (x : Space n) (2 * e) ⊆ U := by
    intro x
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds (hKU x.2))
    exact ⟨δ / 4, by linarith,
      (Metric.closedBall_subset_ball (by linarith)).trans hδU⟩
  choose e he_pos heU using hball

  have hcover : K ⊆ ⋃ x : K, Metric.ball (x : Space n) (e x) := by
    intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (he_pos ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball (x : Space n) (e x))
    (fun _ => Metric.isOpen_ball) hcover

  let bump : ∀ x : K, ContDiffBump (x : Space n) := fun x =>
    { rIn := e x, rOut := 2 * e x, rIn_pos := he_pos x, rIn_lt_rOut := by linarith [he_pos x] }
  let N : Set (Space n) := ⋃ x ∈ t, Metric.ball (x : Space n) (e x)
  let η : Space n → ℝ := fun y => 1 - ∏ x ∈ t, (1 - bump x y)
  have hNopen : IsOpen N := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hηone : ∀ y ∈ N, η y = 1 := by
    intro y hy
    rcases mem_iUnion₂.1 hy with ⟨x, hxt, hyx⟩
    have h1 : bump x y = 1 :=
      (bump x).one_of_mem_closedBall (Metric.mem_closedBall.2 (Metric.mem_ball.1 hyx).le)
    have hz : (∏ z ∈ t, (1 - bump z y)) = 0 := Finset.prod_eq_zero hxt (by rw [h1, sub_self])
    simp only [η, hz, sub_zero]
  have hbumpcont : ∀ x : K, ContDiff ℝ (⊤ : ℕ∞) (fun y => bump x y) := fun x => (bump x).contDiff
  have hcontdiff : ContDiff ℝ (⊤ : ℕ∞) η := by
    have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∏ x ∈ t, (1 - bump x y)) := by
      have hfun : (fun y => ∏ x ∈ t, (1 - bump x y)) =
          (∏ x ∈ t, fun y => 1 - bump x y) := by
        funext y
        rw [Finset.prod_apply]
      rw [hfun]
      refine Finset.induction_on t ?_ ?_
      · have : (∏ x ∈ (∅ : Finset K), (fun y => 1 - bump x y)) = (1 : Space n → ℝ) := by simp
        rw [this]
        exact contDiff_const
      · intro a s has ih
        rw [Finset.prod_insert has]
        exact (contDiff_const.sub (hbumpcont a)).mul ih
    simpa only [η] using contDiff_const.sub hprod

  have hsupp : Function.support η ⊆ ⋃ x ∈ t, tsupport (bump x) := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hcon
    refine hy ?_
    have hb0 : ∀ x ∈ t, bump x y = 0 := by
      intro x hxt
      by_contra hne
      exact hcon (mem_iUnion₂.2 ⟨x, hxt, subset_tsupport _ (Function.mem_support.2 hne)⟩)
    simp only [η]
    have : (∏ x ∈ t, (1 - bump x y)) = 1 :=
      Finset.prod_eq_one fun x hx => by rw [hb0 x hx, sub_zero]
    rw [this, sub_self]
  have hSclosed : IsClosed (⋃ x ∈ t, tsupport (bump x)) :=
    t.finite_toSet.isClosed_biUnion fun _ _ => isClosed_tsupport _
  have hSsub : (⋃ x ∈ t, tsupport (bump x)) ⊆ U := by
    intro y hy
    rcases mem_iUnion₂.1 hy with ⟨x, _, hyx⟩
    rw [ContDiffBump.tsupport_eq] at hyx
    exact heU x hyx
  have hcpt : HasCompactSupport η :=
    IsCompact.of_isClosed_subset
      (t.isCompact_biUnion fun x _ => (bump x).hasCompactSupport)
      (isClosed_tsupport η)
      ((closure_mono hsupp).trans (le_of_eq hSclosed.closure_eq))
  have htsubU : tsupport η ⊆ U :=
    (closure_mono hsupp).trans (by rw [hSclosed.closure_eq]; exact hSsub)
  have h01 : ∀ y, 0 ≤ η y ∧ η y ≤ 1 := by
    intro y
    have hle : (∏ x ∈ t, (1 - bump x y)) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => by have := (bump i).le_one (x := y); linarith)
        (fun i _ => by have := (bump i).nonneg (x := y); linarith)
    have hnn : 0 ≤ ∏ x ∈ t, (1 - bump x y) :=
      Finset.prod_nonneg fun i _ => by have := (bump i).le_one (x := y); linarith
    simp only [η]
    exact ⟨by linarith, by linarith⟩
  have hderiv0 : ∀ (j : Fin n) (y : Space n), y ∈ N →
      fderiv ℝ η y (EuclideanSpace.single j 1) = 0 := by
    intro j y hy
    have heq : η =ᶠ[𝓝 y] Function.const (Space n) (1 : ℝ) := by
      filter_upwards [hNopen.mem_nhds hy] with z hz using hηone z hz
    rw [heq.fderiv_eq, fderiv_const]
    simp

  have hderivcont : Continuous (fun x : Space n => fderiv ℝ η x) :=
    hcontdiff.continuous_fderiv (by simp)
  obtain ⟨C2, hC2⟩ := (hcpt.fderiv ℝ).isCompact.exists_bound_of_continuousOn
    hderivcont.continuousOn
  have hC2' : ∀ x : Space n, ‖fderiv ℝ η x‖ ≤ max C2 0 := by
    intro x
    by_cases hx : x ∈ tsupport (fun x : Space n => fderiv ℝ η x)
    · exact (hC2 x hx).trans (le_max_left _ _)
    · have : fderiv ℝ η x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ (Function.mem_support.2 hne))
      rw [this]; simp
  refine ⟨η, N, hNopen, ht, ?_, hcontdiff, hcpt, htsubU, h01, hηone, hderiv0, ?_⟩
  · intro y hy
    rcases mem_iUnion₂.1 hy with ⟨x, _, hyx⟩
    exact heU x (Metric.mem_closedBall.2 (by
      have := Metric.mem_ball.1 hyx
      linarith [he_pos x, this]))
  · refine ⟨max 1 (max C2 0), le_trans (le_max_right C2 0) (le_max_right 1 _), fun x => ⟨?_, fun j => ?_⟩⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]
      exact (h01 x).2.trans (le_max_left _ _)
    · calc ‖fderiv ℝ η x (EuclideanSpace.single j 1)‖
          ≤ ‖fderiv ℝ η x‖ * ‖EuclideanSpace.single j 1‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ η x‖ := by
            rw [EuclideanSpace.norm_single, norm_one, mul_one]
        _ ≤ max C2 0 := hC2' x
        _ ≤ max 1 (max C2 0) := le_max_right _ _

end DedekindZetaZeroFree.KPCompactInteriorH1

end
