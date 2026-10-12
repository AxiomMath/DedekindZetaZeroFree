module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CharacterCasimirEigenidentity
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HaarDerivativeTransfer

@[expose] public section

section

namespace DedekindZetaZeroFree
namespace KPCompactHarmonic

open MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator InnerProductSpace

abbrev U2 := Matrix.unitaryGroup (Fin 2) ℂ

noncomputable def symmetricPowerTrace (n : ℕ) (g : U2) : ℂ :=
  match n with
  | 0 => 1
  | 1 => Matrix.trace g.val
  | n + 2 => Matrix.trace g.val * symmetricPowerTrace (n + 1) g -
      Matrix.det g.val * symmetricPowerTrace n g

noncomputable def rankOneCharacter (ℓ : ℕ) (g : U2) : ℂ :=
  symmetricPowerTrace (2 * ℓ) g / Matrix.det g.val ^ ℓ

private theorem compactU2 : CompactSpace U2 := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_unitary, ?_⟩
  apply (Metric.isBounded_iff_subset_closedBall 0).mpr
  refine ⟨1, ?_⟩
  intro g hg
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq (CStarRing.norm_coe_unitary ⟨g, hg⟩)

attribute [local instance] compactU2

end KPCompactHarmonic
end DedekindZetaZeroFree

end
