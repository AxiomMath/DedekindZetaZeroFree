module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.AngularHaarDisintegration

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem spherical_core_isCompact
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) :
    IsCompact (KPMsFixedHaarDisintegration.cuspEnds A Y)ᶜ := by

  have hcomp : ∀ i : Fin A.componentCount,
      IsCompact ((Set.univ : Set (KPCuspSiegel.OrbitQuotient F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)))) \
        (⋃ a : Fin (A.cuspAtlas i).cuspCount,
          KPFiniteCuspAtlas.endSet F
            (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
            ((A.cuspAtlas i).representative a)
            (KPMsFixedHaarDisintegration.logHeight (F := F) Y))) := by
    intro i
    obtain ⟨hc, ho⟩ :=
      KPCuspMonodromy.projected_finite_level_compact_open F ζ hζ U
    obtain ⟨n, q, σ, _hn, _hσ, _hcover, hcov⟩ :=
      KPFiniteAdelicCuspEnds.finite_adelic_cusp_cover_with_compact_complement F hF
        (U.toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ))
        hc ho (KPCuspGenuineMonodromy.finiteBase F ζ hζ (A.representative i))
    simpa only [KPFiniteCuspAtlas.endSet] using
      KPFiniteAdelicCuspEnds.compact_complement_of_cusp_representatives F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
        σ (A.cuspAtlas i).cusp (A.cuspAtlas i).representative
        (A.cuspAtlas i).representative_formula (A.cuspAtlas i).exhaustive hcov
        (KPMsFixedHaarDisintegration.logHeight (F := F) Y)

  have hglue := KPFiniteAdelicCuspEnds.compact_core_of_finite_components
    A.components (fun i => KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
    (fun i y => A.components_formula i y)
    (fun i => Fin (A.cuspAtlas i).cuspCount)
    (fun i a => KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
      ((A.cuspAtlas i).representative a)
      (KPMsFixedHaarDisintegration.logHeight (F := F) Y))
    hcomp

  have hset : (KPMsFixedHaarDisintegration.cuspEnds A Y)ᶜ =
      (Set.univ : Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U)) \
        (⋃ i : Fin A.componentCount, ⋃ a : Fin (A.cuspAtlas i).cuspCount,
          KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) ''
            KPFiniteCuspAtlas.endSet F
              (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
              ((A.cuspAtlas i).representative a)
              (KPMsFixedHaarDisintegration.logHeight (F := F) Y)) := by
    rw [KPMsFixedHaarDisintegration.cuspEnds, Set.compl_eq_univ_sdiff]
    congr 1
    rw [Set.iUnion_sigma]
  rw [hset]
  exact hglue

end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry

end
