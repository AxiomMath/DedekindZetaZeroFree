module

public import DedekindZetaZeroFree.Analysis.WeakH2.LocalizedTranslation

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.WeakH2.CoerciveDifference

open MeasureTheory KPContLocalNorm

set_option maxHeartbeats 800000 in

theorem uniform_concentric_cutoff (n : ℕ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) :
    ∃ G : ℝ, 0 < G ∧ ∀ (inner mid outer : LocalBall n),
      inner.center = outer.center → mid.center = outer.center →
      inner.radius = r → mid.radius = (r + R) / 2 → outer.radius = R →
      ∃ η : TestFunction mid.toOpens ℝ ⊤,
        (∀ x ∈ inner.carrier, η x = 1) ∧
        (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
        (∀ (j : Fin n) (x : Space n),
          ‖coordinateDerivativeList [j] (fun y => (η y : ℂ)) x‖ ≤ G) ∧
        Metric.cthickening ((R - r) / 8) (tsupport (fun x => η x)) ⊆ mid.carrier := by
  let s : ℝ := r + (R - r) / 4
  have hrs : r < s := by dsimp [s]; linarith
  have hs : 0 < s := hr.trans hrs
  let b : ContDiffBump (0 : Space n) := ⟨r, s, hr, hrs⟩
  let f : Space n → ℂ := fun x => (b x : ℂ)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hfc : HasCompactSupport f :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl
  obtain ⟨C, hC⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro inner mid outer hic hmc hir hmr hor
  let g : Space n → ℝ := fun x => b (x - outer.center)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    b.contDiff.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport g :=
    b.hasCompactSupport.comp_homeomorph (Homeomorph.subRight outer.center)
  have hgs : tsupport g = Metric.closedBall outer.center s := by
    change tsupport ((fun x => b x) ∘ Homeomorph.subRight outer.center) = _
    rw [tsupport_comp_eq_preimage, b.tsupport_eq]
    ext x
    simp [Metric.mem_closedBall, dist_eq_norm, b]
  have hsm : s < mid.radius := by rw [hmr]; dsimp [s]; linarith
  let η : TestFunction mid.toOpens ℝ ⊤ :=
    ⟨g, hg, hgc, by
      change tsupport g ⊆ mid.carrier
      rw [hgs]
      intro x hx
      change dist x mid.center < mid.radius
      rw [hmc]
      exact (Metric.mem_closedBall.mp hx).trans_lt hsm⟩
  refine ⟨η, ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply b.one_of_mem_closedBall
    have hx' : dist x outer.center < r := by
      simpa only [LocalBall.carrier, Metric.mem_ball, hic, hir] using hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx'.le
  · intro x
    exact ⟨b.nonneg, b.le_one⟩
  · intro j x
    change ‖fderiv ℝ (fun y => f (y - outer.center)) x
      (EuclideanSpace.single j 1)‖ ≤ max C 1
    simp only [sub_eq_add_neg, fderiv_comp_add_right]
    calc
      ‖fderiv ℝ f (x + -outer.center) (EuclideanSpace.single j 1)‖ ≤
          ‖fderiv ℝ f (x + -outer.center)‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f (x + -outer.center)‖ := by
        simp [EuclideanSpace.norm_single]
      _ ≤ C := hC _
      _ ≤ max C 1 := le_max_left _ _
  · change Metric.cthickening ((R - r) / 8) (tsupport g) ⊆ mid.carrier
    rw [hgs, cthickening_closedBall (by linarith : 0 ≤ (R - r) / 8) hs.le]
    intro x hx
    change dist x mid.center < mid.radius
    rw [hmc, hmr]
    have hx' := Metric.mem_closedBall.mp hx
    dsimp [s] at hx'
    linarith

end DedekindZetaZeroFree.WeakH2.CoerciveDifference

end
