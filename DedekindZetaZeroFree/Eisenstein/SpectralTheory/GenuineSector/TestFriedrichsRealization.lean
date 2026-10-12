module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.CompactWeakFormDomain

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorTestFriedrichs

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

structure Properties : Prop where

  smooth_tests : KPContActualSectorSmoothTestModules.Properties
    (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H)

  embeddings : KPContActualSectorTestEmbeddings.Properties
    (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H)
  scalar_dense : DenseRange
    (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
  cotangent_dense : DenseRange
    (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))

  differential : KPContActualSectorTestDifferentialDescent.Properties
    (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H)

  global_green : KPContActualSectorGlobalGreen.Properties
    (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H)

  friedrichs : KPContActualSectorFriedrichsSynthesis.Properties
    F ζ hζ U R P H μG hμG hR realization

  weak_localization : KPContActualSectorFormWeakLocalization.Properties
    F ζ hζ U R P H μG hμG hR realization

  compact_weak_converse : KPContActualSectorCompactWeakFormConverse.Properties
    F ζ hζ U R P H μG hμG hR realization

end DedekindZetaZeroFree.KPContActualSectorTestFriedrichs

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_test_friedrichs
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorTestFriedrichs.Properties F ζ hζ U R P H μG hμG hR realization :=
  { smooth_tests :=
      kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization
    embeddings :=
      kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
    scalar_dense :=
      KPContActualSectorFriedrichsSynthesis.scalarDense F ζ hζ U R P H μG hμG hR realization
    cotangent_dense :=
      KPContActualSectorFriedrichsSynthesis.cotangentDense F ζ hζ U R P H μG hμG hR realization
    differential :=
      kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H realization
    global_green :=
      kp_cont_actual_sector_global_green F ζ hζ μG hμG U R hR P H realization
    friedrichs :=
      kp_cont_actual_sector_friedrichs_synthesis F ζ hζ μG hμG U R hR P H realization
    weak_localization :=
      kp_cont_actual_sector_form_weak_localization F ζ hζ μG hμG U R hR P H realization
    compact_weak_converse :=
      kp_cont_actual_sector_compact_weak_form_converse F ζ hζ μG hμG U R hR P H realization }

end DedekindZetaZeroFree

end
