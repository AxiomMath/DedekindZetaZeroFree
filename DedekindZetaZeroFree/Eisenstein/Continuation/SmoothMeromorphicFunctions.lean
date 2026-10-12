module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SpectralCoordinateAndPoleOrders

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneContinuation
open MeasureTheory KPGlobalEisensteinData
open scoped Topology

variable {G H J : Type*} [TopologicalSpace G] [AddCommGroup H] [Module ℂ H]

def SmoothMeromorphicOn (D : J → H →ₗ[ℂ] C(G, ℂ))
    (f : ℂ → H) (O : Set ℂ) : Prop :=
  ∀ z₀ ∈ O, ∃ (ρ : ℝ) (m : ℕ) (a : ℕ → H) (cleared : ℂ → H),
    0 < ρ ∧ Metric.ball z₀ ρ ⊆ O ∧
    SmoothPowerSeriesOn D z₀ ρ a cleared ∧
    ∀ z ∈ Metric.ball z₀ ρ, z ≠ z₀ → cleared z = (z - z₀) ^ m • f z

end DedekindZetaZeroFree.KPRankOneContinuation

end
