module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.U2CharacterConvolutionOrthogonality

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.CharacterExpansion

open MeasureTheory

open scoped Matrix.Norms.L2Operator InnerProductSpace

theorem cover_compactSpace : CompactSpace RawU2 := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_unitary
  · apply (Metric.isBounded_iff_subset_closedBall 0).mpr
    refine ⟨1, ?_⟩
    intro g hg
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (CStarRing.norm_coe_unitary ⟨g, hg⟩)

end DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.CharacterExpansion
