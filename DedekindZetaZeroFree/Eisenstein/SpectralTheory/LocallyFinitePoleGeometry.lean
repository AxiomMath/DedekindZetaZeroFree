module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SpectralCoordinateAndPoleOrders

@[expose] public section

noncomputable section
open scoped Topology
open Filter
namespace DedekindZetaZeroFree.ResidueContinuity.ScalarSourcePoleGeometry

def IsolatedPoles (O P : Set ℂ) : Prop :=
  ∀ z ∈ O, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ O ∧
    ∀ s ∈ Metric.ball z r, s ∈ P → s = z

theorem IsolatedPoles.mono {O P Q : Set ℂ} (hP : IsolatedPoles O P)
    (hQP : Q ⊆ P) : IsolatedPoles O Q := by
  intro z hz
  obtain ⟨r, hr, hb, hi⟩ := hP z hz
  exact ⟨r, hr, hb, fun s hs hq => hi s hs (hQP hq)⟩

theorem IsolatedPoles.union {O P Q : Set ℂ}
    (hP : IsolatedPoles O P) (hQ : IsolatedPoles O Q) :
    IsolatedPoles O (P ∪ Q) := by
  intro z hz
  obtain ⟨r, hr, hb, hi⟩ := hP z hz
  obtain ⟨t, ht, -, hj⟩ := hQ z hz
  refine ⟨min r t, lt_min hr ht,
    (Metric.ball_subset_ball (min_le_left _ _)).trans hb, ?_⟩
  intro s hs hp
  rcases hp with hp | hp
  · exact hi s (Metric.ball_subset_ball (min_le_left _ _) hs) hp
  · exact hj s (Metric.ball_subset_ball (min_le_right _ _) hs) hp

end DedekindZetaZeroFree.ResidueContinuity.ScalarSourcePoleGeometry

end
