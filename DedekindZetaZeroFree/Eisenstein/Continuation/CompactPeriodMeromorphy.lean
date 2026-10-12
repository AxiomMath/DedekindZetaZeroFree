module

public import DedekindZetaZeroFree.Analysis.Meromorphic.GlobalGermUniqueness
public import DedekindZetaZeroFree.Eisenstein.Whittaker.CompactRepresentativePeriods

@[expose] public section

noncomputable section
open scoped Classical Topology BigOperators
open Filter
namespace DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.FiniteCompactAssembly

 theorem finite_compact_numerator
    {I : Type*} [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (O : Set ℂ) (B : ∀ i, J i → ℂ → ℂ)
    (A N : ∀ i, J i → ℂ → V)
    (hB : ∀ i j, AnalyticOnNhd ℂ (B i j) O)
    (hA : ∀ i j, MeromorphicOn (A i j) O)
    (r : ∀ i, J i → ℝ) (hr : ∀ i j, 0 < r i j)
    (_hb : ∀ i j, Metric.ball (0 : ℂ) (r i j) ⊆ O)
    (hN : ∀ i j, AnalyticOnNhd ℂ (N i j) (Metric.ball (0 : ℂ) (r i j)))
    (he : ∀ i j, ∀ s ∈ Metric.ball (0 : ℂ) (r i j), s ≠ 0 → N i j s = s • A i j s)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hb₀ : Metric.ball (0 : ℂ) r₀ ⊆ O) :
    MeromorphicOn (fun s => ∑ i, ∑ j, B i j s • A i j s) O ∧
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) r₀ ∧
        AnalyticOnNhd ℂ (fun s => ∑ i, ∑ j, B i j s • N i j s) (Metric.ball (0 : ℂ) ρ) ∧
        ∀ s ∈ Metric.ball (0 : ℂ) ρ, s ≠ 0 →
          (∑ i, ∑ j, B i j s • N i j s) = s • (∑ i, ∑ j, B i j s • A i j s) := by
  have hall : ∀ᶠ s in 𝓝 (0 : ℂ),
      s ∈ Metric.ball (0 : ℂ) r₀ ∧ ∀ i j, s ∈ Metric.ball (0 : ℂ) (r i j) := by
    apply Filter.Eventually.and (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr i j))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨?_, ρ, hρ, fun s hs => (hρsub hs).1, ?_, ?_⟩
  · intro s hs
    apply MeromorphicAt.fun_sum
    intro i _
    apply MeromorphicAt.fun_sum
    intro j _
    exact ((hB i j) s hs).meromorphicAt.fun_smul (hA i j s hs)
  · intro s hs
    apply Finset.univ.analyticAt_fun_sum
    intro i _
    apply Finset.univ.analyticAt_fun_sum
    intro j _
    exact ((hB i j) s (hb₀ (hρsub hs).1)).smul (hN i j s ((hρsub hs).2 i j))
  · intro s hs hn
    simp_rw [he _ _ s ((hρsub hs).2 _ _) hn, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _

open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.GlobalScalarPin renaming germ_eq_of_open_agreement → germ_eq_of_open_agreement

 theorem native_center_eq_same_clearing
    (E c M Q S T : ℂ → ℂ) (U W V : Set ℂ)
    (hU : IsPreconnected U) (hW : IsPreconnected W)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) (hVW : V ⊆ W)
    (hzU : (0 : ℂ) ∈ U) (hzW : (0 : ℂ) ∈ W)
    (hE : MeromorphicOn E U) (hS : MeromorphicOn S W)
    (hM : MeromorphicOn M Set.univ) (hQ : AnalyticOnNhd ℂ Q W) (hQ0 : Q 0 = 1)
    (hEc : Set.EqOn E M V) (hSc : Set.EqOn S (fun s => Q s * M s) V)
    (hc : AnalyticAt ℂ c 0) (hT : AnalyticAt ℂ T 0)
    (hclear : c =ᶠ[𝓝[≠] (0 : ℂ)] fun s => s * E s)
    (hnum : T =ᶠ[𝓝[≠] (0 : ℂ)] fun s => s * S s) :
    T 0 = c 0 := by
  have hEg := germ_eq_of_open_agreement E M U V hU hV hne hVU hE
    (fun s _ => hM s (Set.mem_univ s)) hEc 0 hzU
  have hSg := germ_eq_of_open_agreement S (fun s => Q s * M s) W V
    hW hV hne hVW hS
    (fun s hs => ((hQ s hs).meromorphicAt).mul (hM s (Set.mem_univ s))) hSc 0 hzW
  have he : T =ᶠ[𝓝[≠] (0 : ℂ)] fun s => Q s * c s := by
    filter_upwards [hEg, hSg, hclear, hnum] with s he hs hc ht
    rw [ht, hs, hc, he]
    ring
  have hQc : ContinuousAt (fun s => Q s * c s) 0 := (hQ 0 hzW).continuousAt.mul hc.continuousAt
  have he0 := ((hT.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hQc).mp he).eq_of_nhds
  simpa only [hQ0, one_mul] using he0

open MeasureTheory

 theorem extension_evaluates_native_pullback
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (q : C(X, Y)) (hq : Function.Surjective q) (μ : Measure Y) [IsFiniteMeasure μ]
    (L : C(X, ℂ) →L[ℂ] ℂ)
    (hL : ∀ f : C(Y, ℂ), L (f.comp q) = ∫ y, f y ∂μ)
    (A : C(X, ℂ)) (c : Y → ℂ) (he : ∀ x, A x = c (q x)) :
    L A = ∫ y, c y ∂μ := by
  have hc : Continuous c := by
    apply (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous).continuous_iff.mpr
    exact A.continuous.congr he
  let f : C(Y, ℂ) := ⟨c, hc⟩
  have hA : A = f.comp q := ContinuousMap.ext he
  rw [hA, hL]
  rfl

end DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.FiniteCompactAssembly

end
