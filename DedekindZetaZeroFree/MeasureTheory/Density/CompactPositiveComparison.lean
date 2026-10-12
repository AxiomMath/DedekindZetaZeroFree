module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

theorem compact_positive_density_lower_bound {E : Type*} [TopologicalSpace E]
    {S K : Set E} {ρ : E → ℝ} (hK : IsCompact K) (hKS : K ⊆ S)
    (hρ : ContinuousOn ρ S) (hpos : ∀ x ∈ S, 0 < ρ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ ρ x := by
  exact hK.exists_forall_le' (hρ.mono hKS) (fun x hx => hpos x (hKS hx))

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
