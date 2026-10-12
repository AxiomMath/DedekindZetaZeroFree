module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.AdelicRestrictedProductTopology

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.FullSplitProduct.RestrictedDensity

open NumberField IsDedekindDomain
open scoped Classical

theorem isClosed_range_kStar {F : Type} [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (p : HeightOneSpectrum (𝓞 F))
    (hw : ringChar (KPTameCompact.O F p ⧸ KPTameCompact.p F p) ≠ 3) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ p
      (KPAdelicCoverRestrictedProduct.depth F ζ hζ p)
    IsClosed (Set.range (KPGoodCompactSplitting.kStar F ζ hζ p hw)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ p
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ p)
  haveI : T2Space (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr p)) :=
    (KPLocalChartTopology.finite_topological_group F ζ hζ p _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ p)).1
  exact (KPGoodCompactSplitting.kStar_compact_image F ζ hζ p hw _
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ p)).isClosed

theorem isClosed_bot_localCover {F : Type} [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : KPHilbert.Place F) :
    letI := KPAdelicCoverRestrictedProduct.localTopology F ζ hζ v
    IsClosed ((⊥ : Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ v)) :
      Set (KPLocalCover.CubicGL2Raw F ζ hζ v)) := by
  letI := KPAdelicCoverRestrictedProduct.localTopology F ζ hζ v
  have h1 : IsClosed ({1} : Set (KPLocalCover.CubicGL2Raw F ζ hζ v)) := by
    rcases v with w | p
    · haveI : T2Space (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :=
        (KPLocalChartTopology.complex_topological_cover F ζ hζ w).1
      exact isClosed_singleton
    · haveI : T2Space (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr p)) :=
        (KPLocalChartTopology.finite_topological_group F ζ hζ p _
          (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ p)).1
      exact isClosed_singleton
  simpa [Subgroup.coe_bot] using h1

end DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.FullSplitProduct.RestrictedDensity

end
