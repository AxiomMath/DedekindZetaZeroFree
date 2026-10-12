module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactAverages.TaylorJets

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageJets
open MeasureTheory Set Filter Topology
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.CompactJets renaming hasFDerivAt_average_general → hasFDerivAt_average_general
set_option backward.isDefEq.respectTransparency false in

theorem hasTaylor_average
    {H E K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (s : Set H) (hs : IsOpen s) (f : H → K → E)
    (p : H → K → FormalMultilinearSeries ℝ H E)
    (hp : ∀ k, HasFTaylorSeriesUpToOn (⊤ : ℕ∞) (fun x => f x k) (fun x => p x k) s)
    (hc : ∀ m, ContinuousOn (fun q : H × K => p q.1 q.2 m) (s ×ˢ univ)) :
    HasFTaylorSeriesUpToOn (⊤ : ℕ∞) (fun x => ∫ k, f x k ∂μ)
      (fun x m => ∫ k, p x k m ∂μ) s := by
  let q : H → FormalMultilinearSeries ℝ H E := fun x m => ∫ k, p x k m ∂μ
  constructor
  · intro x hx
    have hc0 : Continuous (fun k => p x k 0) := by
      rw [← continuousOn_univ]
      exact (hc 0).comp (show ContinuousOn (fun k : K => (x, k)) univ from
        (continuous_const.prodMk continuous_id).continuousOn) (by intro k hk; exact ⟨hx, hk⟩)
    have hi := hc0.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
    change (∫ k, p x k 0 ∂μ) 0 = _
    rw [ContinuousMultilinearMap.integral_apply hi]
    apply integral_congr_ae
    filter_upwards with k
    exact (hp k).zero_eq x hx
  · intro m hm x hx
    letI : NormedAddCommGroup (H [×m]→L[ℝ] E) := ContinuousMultilinearMap.normedAddCommGroup
    letI : NormedAddCommGroup (H [×m+1]→L[ℝ] E) := ContinuousMultilinearMap.normedAddCommGroup
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => H) E
    have hd : ∀ y ∈ s, ∀ k, HasFDerivAt (fun z => p z k m)
        (p y k (m + 1)).curryLeft y := by
      intro y hy k
      exact ((hp k).fderivWithin m hm y hy).hasFDerivAt (hs.mem_nhds hy)
    have hc' : ContinuousOn (fun z : H × K => (p z.1 z.2 (m + 1)).curryLeft)
        (s ×ˢ univ) := L.continuous.comp_continuousOn (hc (m + 1))
    have h := hasFDerivAt_average_general μ s hs (fun y k => p y k m)
      (fun y k => (p y k (m + 1)).curryLeft) (hc m) hc' hd x hx
    have he : (∫ k, (p x k (m + 1)).curryLeft ∂μ) =
        (∫ k, p x k (m + 1) ∂μ).curryLeft := by
      have hcp : Continuous (fun k => p x k (m + 1)) := by
        rw [← continuousOn_univ]
        exact (hc (m + 1)).comp (show ContinuousOn (fun k : K => (x, k)) univ from
          (continuous_const.prodMk continuous_id).continuousOn)
          (by intro k hk; exact ⟨hx, hk⟩)
      have hi := hcp.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
      let L' : (H [×m+1]→L[ℝ] E) ≃L[ℝ] (H →L[ℝ] H [×m]→L[ℝ] E) :=
        L.toContinuousLinearEquiv
      exact ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ)
        (E := H [×m+1]→L[ℝ] E) (F := H →L[ℝ] H [×m]→L[ℝ] E)
        L' (φ := fun k => p x k (m + 1))
    rw [he] at h
    exact h.hasFDerivWithinAt
  · intro m _
    exact continuousOn_integral_of_compact_support isCompact_univ (hc m) (by simp)

end DedekindZetaZeroFree.FourierContinuation.ResidualAverageJets

end
