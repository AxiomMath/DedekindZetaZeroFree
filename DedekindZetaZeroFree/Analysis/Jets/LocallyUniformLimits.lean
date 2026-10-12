module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesJetLimits
open Filter Topology
variable {ι E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
lemma taylorSeries_locallyUniform_limit (l : Filter ι) [l.NeBot]
    (U : Set E) (hU : IsOpen U) (F : ι → E → V)
    (P : ι → E → FormalMultilinearSeries ℝ E V)
    (G : E → V) (Q : E → FormalMultilinearSeries ℝ E V)
    (hP : ∀ i, HasFTaylorSeriesUpToOn (⊤ : ℕ∞) (F i) (P i) U)
    (hF : ∀ x ∈ U, Tendsto (fun i => F i x) l (𝓝 (G x)))
    (hQ : ∀ n : ℕ, TendstoLocallyUniformlyOn (fun i x => P i x n) (fun x => Q x n) l U) :
    HasFTaylorSeriesUpToOn (⊤ : ℕ∞) G Q U := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hzero : Tendsto (fun i => (P i x 0).curry0) l (𝓝 ((Q x 0).curry0)) :=
      (continuousMultilinearCurryFin0 ℝ E V).continuous.tendsto _ |>.comp ((hQ 0).tendsto_at hx)
    have he : (fun i => (P i x 0).curry0) = fun i => F i x := by
      funext i
      exact (hP i).zero_eq x hx
    rw [he] at hzero
    exact tendsto_nhds_unique hzero (hF x hx)
  · intro n hn x hx
    have hp : ∀ i x, x ∈ U → HasFDerivAt (fun y => P i y n) (P i x (n+1)).curryLeft x := by
      intro i x hx
      exact ((hP i).fderivWithin n hn x hx).hasFDerivAt (hU.mem_nhds hx)
    have hconv : TendstoLocallyUniformlyOn (fun i x => (P i x (n+1)).curryLeft)
        (fun x => (Q x (n+1)).curryLeft) l U := by
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).toContinuousLinearEquiv.toContinuousLinearMap.uniformContinuous.comp_tendstoLocallyUniformlyOn (hQ (n+1))
    exact (hasFDerivAt_of_tendstoLocallyUniformlyOn hU hconv hp
      (fun x hx => (hQ n).tendsto_at hx) hx).hasFDerivWithinAt
  · intro n hn
    exact (hQ n).continuousOn (Filter.Eventually.of_forall (fun i => (hP i).cont n hn)).frequently

end DedekindZetaZeroFree.KPCplxPrincipalSeriesJetLimits
