module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShapes.OffsetWeightedCoarea
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.MaassSelberg.GreenIdentityAndConstantFlux

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField ENNReal NNReal Topology
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeWeightedShape.Source
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)

abbrev nativeFamily := KPMsActualNativeHaarFamily.family F ζ hζ R P

open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming weighted_section_finite → weighted_section_finite

end DedekindZetaZeroFree.KPMsNativeWeightedShape.Source
namespace DedekindZetaZeroFree.KPMsNativeWeightedShapeSource

open KPMsActualAngularSource KPMsNativeOffsetMass

structure NativeAngularHaarData
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (S : NativeRecipe F ζ hζ R P) extends NativeMassFamily F ζ hζ R P S where

  shape : ∀ V : Level F ζ hζ,
    Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)
  shape_measurable : ∀ V, Measurable (shape V)

  shape_measure : ∀ V,
    Measure.map (shape V) (finiteMarginal F ζ hζ R P S V toNativeMassFamily) =
      weightedBeta F ζ hζ R P S V

  shape_on_source_frame : ∀ (V : Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V) (Y : ℝ),
    OffsetAdmissible F ζ hζ R P S V Y →
    ∀ (x : KPSmoothLocalQuotientCharts.X F ζ hζ),
    x ∈ cuspShell F ζ hζ R P S V j Y →
    ∀ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
      (t : ℝ) (ε : rootsOfUnity 3 F)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
    actualFrame F ζ hζ R P S V j Y x =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val →
    KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t)) →
    shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)
      (fullCoordinate F ζ hζ R P S V j Y x)) =
      (⟨j, QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F
        (nativeFamily F ζ hζ R P).totallyComplex
        (nativeDisintegration F ζ hζ R P S V).radial.slot
        ⟨(cuspOffset F ζ hζ R P S V j).val *
            Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),
          mul_pos (cuspOffset F ζ hζ R P S V j).property (Real.exp_pos _)⟩)⟩ :
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))

theorem actual_native_weighted_shape
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ) :
    Nonempty (NativeAngularHaarData F ζ hζ R P (nativeRecipe F ζ hζ R P)) := by
  obtain ⟨M⟩ := exists_native_offset_mass_family F ζ hζ R P (nativeRecipe F ζ hζ R P)
  obtain ⟨shape, hshape, hframe⟩ := OffsetShapeDescent.native_shape_descent
    F ζ hζ R P (nativeRecipe F ζ hζ R P)
  refine ⟨{
    toNativeMassFamily := M
    shape := shape
    shape_measurable := hshape
    shape_on_source_frame := hframe
    shape_measure := ?_ }⟩
  intro V
  obtain ⟨Y, _, hY⟩ := exists_offset_admissible F ζ hζ R P (nativeRecipe F ζ hζ R P) V
  rw [finiteMarginal, M.from_source V Y hY,
    Measure.map_map (hshape V)
      (KPMsActualAngularShellSource.fullToLevel_measurable _ _)]
  exact OffsetShapeCoarea.native_shape_measure F ζ hζ R P
    (nativeRecipe F ζ hζ R P) shape hshape hframe V Y hY

end DedekindZetaZeroFree.KPMsNativeWeightedShapeSource

end
