module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.SphericalCoreCompactness
public import DedekindZetaZeroFree.Adeles.Quotients.SphericalProjectionProperness
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RationalQuotientCompactMass

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped Classical NumberField Topology ENNReal
namespace DedekindZetaZeroFree.KPMsGreenFlux.TruncatedL2Geometry
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

theorem endSet_isOpen (j : Cusps A) (Y : ℝ) : IsOpen (endSet A j Y) := by
  have hmap : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)) := by
    have heq : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) =
        A.components ∘ Sigma.mk j.1 := by
      funext x
      exact (A.components_formula j.1 x).symm
    rw [heq]
    exact A.components.isOpenMap.comp isOpenMap_sigmaMk
  exact hmap _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ _)

theorem cuspEnds_isOpen (Y : ℝ) : IsOpen (KPMsFixedHaarDisintegration.cuspEnds A Y) := by
  apply isOpen_iUnion
  intro j
  exact endSet_isOpen A j Y

theorem quotientCore_compl_eq_preimage
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ) (Y : ℝ) :
    (quotientCore A P Y)ᶜ = (P.projection U) ⁻¹'
      KPMsFixedHaarDisintegration.cuspEnds A Y := by
  ext x
  simp only [quotientCore, Set.mem_compl_iff, Set.mem_setOf_eq,
    KPMsFixedHaarDisintegration.cuspEnds, Set.mem_preimage, Set.mem_iUnion]
  simp only [not_forall, not_not]
  rfl

end DedekindZetaZeroFree.KPMsGreenFlux.TruncatedL2Geometry

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical NumberField Topology ENNReal
namespace DedekindZetaZeroFree.KPMsGreenFlux.TruncatedL2Geometry
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

theorem quotientCore_compact_measurable_finite
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) :
    IsCompact (quotientCore A P Y) ∧ MeasurableSet (quotientCore A P Y) ∧
      R.quotientHaar (quotientCore A P Y) < ⊤ := by
  letI : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  have he : quotientCore A P Y = (P.projection U) ⁻¹'
      (KPMsFixedHaarDisintegration.cuspEnds A Y)ᶜ := by
    rw [Set.preimage_compl, ← quotientCore_compl_eq_preimage A P Y, compl_compl]
  have hc := KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry.spherical_core_isCompact A Y hY
  have hk : IsCompact (quotientCore A P Y) := by
    rw [he]
    exact KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry.spherical_projection_compact_preimage P U _ hc
  refine ⟨hk, ?_, ?_⟩
  · rw [he]
    exact (cuspEnds_isOpen A Y).isClosed_compl.measurableSet.preimage (P.continuous U).measurable
  · exact lt_top_iff_ne_top.mpr
      (KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry.quotientHaar_compact_ne_top R _ hk)

end DedekindZetaZeroFree.KPMsGreenFlux.TruncatedL2Geometry

end

end
