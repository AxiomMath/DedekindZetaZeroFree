module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.HolomorphicFamilies.SmoothHolomorphyFromInteriorEstimates

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade

open MeasureTheory
open KPContLocalNorm KPContLocalCubeEmbedding

theorem smooth_forcing_at {n : ℕ} {B : LocalBall n} {O : Set ℂ} {h : ℂ → Space n → ℂ}
    (hh : SmoothCompactOpenHolomorphicOn B h O) {z : ℂ} (hz : z ∈ O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (h z) B.carrier := by
  obtain ⟨ρ, hρ, _, coeff, hc⟩ := hh z hz
  exact hc.2.1 z (by simp [Metric.mem_ball, hρ])

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade

end
