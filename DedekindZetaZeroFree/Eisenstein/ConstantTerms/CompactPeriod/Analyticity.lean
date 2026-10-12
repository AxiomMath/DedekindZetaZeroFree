module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.JointContinuity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod

section CompactIntegral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem compact_integral_analyticOnNhd (μ : Measure X) [IsFiniteMeasure μ]
    (f : ℂ → X → ℂ) (O : Set ℂ) (hO : IsOpen O)
    (hc : Continuous (fun p : O × X => f p.1.val p.2))
    (ha : ∀ x, AnalyticOnNhd ℂ (fun s => f s x) O) :
    AnalyticOnNhd ℂ (fun s => ∫ x, f s x ∂μ) O := by
  suffices DifferentiableOn ℂ (fun s => ∫ x, f s x ∂μ) O from this.analyticOnNhd hO
  have hi (s : ℂ) (hs : s ∈ O) : Integrable (f s) μ := by
    have hcs : Continuous (f s) := hc.comp
      ((continuous_const (y := (⟨s, hs⟩ : O))).prodMk continuous_id)
    simpa using hcs.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ
  let J : O → C(X, ℂ) := fun s =>
    ⟨f s.val, hc.comp (continuous_const.prodMk continuous_id)⟩
  have hJ : Continuous J := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hc
  intro z hz
  obtain ⟨t, ht, htb⟩ := Metric.isOpen_iff.mp hO z hz
  let r : ℝ := t / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsub : Metric.closedBall z r ⊆ O := by
    intro s hs
    apply htb
    have hd : dist s z ≤ r := hs
    change dist s z < t
    dsimp [r] at hd
    linarith
  let Jb : Metric.closedBall z r → C(X, ℂ) := fun s => J ⟨s.val, hsub s.property⟩
  have hJb : Continuous Jb := hJ.comp (continuous_subtype_val.subtype_mk _)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hJb.continuousOn
  have hb (s : ℂ) (hs : s ∈ Metric.closedBall z r) (x : X) : ‖f s x‖ ≤ B := by
    exact (J ⟨s, hsub hs⟩).norm_coe_le_norm x |>.trans (hB ⟨s, hs⟩ (Set.mem_univ _))
  let D : ℂ → X → ℂ := fun s x => deriv (fun w => f w x) s
  have hdm : AEStronglyMeasurable (D z) μ := by
    let ft : ℂ → X → ℂ := fun s => if s ∈ O then f s else f z
    have hft (s : ℂ) : AEStronglyMeasurable (ft s) μ := by
      by_cases hs : s ∈ O
      · simpa [ft, hs] using (hi s hs).aestronglyMeasurable
      · simpa [ft, hs] using (hi z hz).aestronglyMeasurable
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] z)
      (f := fun s x => slope (fun w => ft w x) z s)
    · intro s
      exact ((hft s).sub (hft z)).const_smul ((s-z)⁻¹)
    · apply ae_of_all μ
      intro x
      have he : (fun w => ft w x) =ᶠ[𝓝 z] (fun w => f w x) := by
        filter_upwards [hO.mem_nhds hz] with w hw
        simp [ft, hw]
      exact (((ha x z hz).differentiableAt.hasDerivAt).congr_of_eventuallyEq he).tendsto_slope
  have hder (s : ℂ) (hs : s ∈ Metric.ball z (r / 2)) (x : X) :
      ‖D s x‖ ≤ B / (r / 2) := by
    have hss : Metric.closedBall s (r / 2) ⊆ Metric.closedBall z r :=
      Metric.closedBall_subset_closedBall' (by have := Metric.mem_ball.mp hs; linarith)
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (((ha x).mono (hss.trans hsub)).differentiableOn.diffContOnCl_ball Set.Subset.rfl)
      (fun w hw => hb w (hss (Metric.sphere_subset_closedBall hw)) x)
  have hnear : Metric.ball z (r / 2) ⊆ O :=
    (Metric.ball_subset_ball (by linarith)).trans (Metric.ball_subset_closedBall.trans hsub)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := D) (bound := fun _ => B / (r / 2))
    (Metric.ball_mem_nhds z (by positivity : 0 < r / 2))
    (eventually_of_mem (Metric.ball_mem_nhds z (by positivity : 0 < r / 2))
      (fun s hs => (hi s (hnear hs)).aestronglyMeasurable))
    (hi z hz) hdm (ae_of_all μ fun x s hs => hder s hs x)
    (integrable_const _) (ae_of_all μ fun x s hs =>
      (ha x s (hnear hs)).differentiableAt.hasDerivAt)
  exact hd.2.differentiableAt.differentiableWithinAt
end CompactIntegral

open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

theorem upper_cleared_analyticOnNhd (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) :
    AnalyticOnNhd ℂ (fun s => upper R Q.dq (T.cleared v s) g)
      (Metric.ball (0 : ℂ) T.radius) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  exact compact_integral_analyticOnNhd Q.dq _ _ Metric.isOpen_ball
    (cleared_quotient_joint_continuous T v g)
    (fun q => T.analytic v _)

end DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod

end
