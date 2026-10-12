module

public import DedekindZetaZeroFree.Analysis.SpectralTheory.Resolvents.BelowThresholdMeromorphy
public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSphericalL2Formula

open MeasureTheory Filter Topology

def ClearedHilbertGerm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (v : ℂ → H) (Ω : Set ℂ) (s₀ : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.ball s₀ r ⊆ Ω ∧
    ∃ w : ℂ → H, DifferentiableOn ℂ w (Metric.ball s₀ r) ∧
      ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • v s

section Formula
variable {X A H S : Type*} [MeasurableSpace X] [Fintype A]
    [AddCommGroup H] [Module ℂ H] [AddCommGroup S] [Module ℂ S]

end Formula

def ClearedSmoothGerm {X I : Type*}
    (n : I → ℕ) (balls : ∀ i, KPContLocalNorm.LocalBall (n i))
    (pullback : ∀ i, (X → ℂ) →ₗ[ℂ] (KPContLocalNorm.Space (n i) → ℂ))
    (automorphic : Submodule ℂ (X → ℂ))
    (E : ℂ → X → ℂ) (Ω : Set ℂ) (s₀ : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.ball s₀ r ⊆ Ω ∧
    ∃ w : ℂ → X → ℂ,
      (∀ s ∈ Metric.ball s₀ r, w s ∈ automorphic) ∧
      (∀ i, KPCutoffSource.ChartSmoothHolomorphicOn (balls i)
        (fun s => pullback i (w s)) (Metric.ball s₀ r)) ∧
      ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → w s = (s - s₀) • E s

end DedekindZetaZeroFree.KPSphericalL2Formula

end
