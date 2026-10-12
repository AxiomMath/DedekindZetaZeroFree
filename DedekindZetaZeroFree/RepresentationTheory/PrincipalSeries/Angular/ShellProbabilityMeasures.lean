module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShapes.WeightedHaarDisintegration

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeOffsetComparison
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeWeightedShapeSource

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)

structure NativeMeasuredSource extends
    NativeAngularHaarData F ζ hζ R P (nativeRecipe F ζ hζ R P)

theorem exists_native_measured_source : Nonempty (NativeMeasuredSource F ζ hζ R P) := by
  obtain ⟨M⟩ := actual_native_weighted_shape F ζ hζ R P
  exact ⟨⟨M⟩⟩

variable {F ζ hζ R P}

def fullMass (M : NativeMeasuredSource F ζ hζ R P) : ℝ≥0∞ := M.full Set.univ

def fullNu (M : NativeMeasuredSource F ζ hζ R P) :
    Measure (FullOmega F ζ hζ (nativeDatum F ζ hζ)) :=
  fullProbability F ζ hζ R P (nativeRecipe F ζ hζ R P) M.toNativeMassFamily

def nu (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ) :
    Measure (Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)) :=
  finiteProbability F ζ hζ R P (nativeRecipe F ζ hζ R P) V M.toNativeMassFamily

def normalizedShapeBeta (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ) :
    Measure (KPMsFixedHaarDisintegration.Omega
      (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V)) :=
  (fullMass M)⁻¹ • weightedBeta F ζ hζ R P (nativeRecipe F ζ hζ R P) V

theorem fullMass_pos (M : NativeMeasuredSource F ζ hζ R P) : 0 < fullMass M := M.positive

theorem fullMass_ne_top (M : NativeMeasuredSource F ζ hζ R P) : fullMass M ≠ ⊤ := by
  letI := M.finite
  exact measure_ne_top M.full Set.univ

theorem nu_probability (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ) :
    IsProbabilityMeasure (nu M V) :=
  finiteProbability_probability F ζ hζ R P (nativeRecipe F ζ hζ R P) V M.toNativeMassFamily

theorem nu_from_full (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ) :
    Measure.map (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V))
      (fullNu M) = nu M V := rfl

theorem shape_measure (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ) :
    Measure.map (M.shape V) (nu M V) = normalizedShapeBeta M V := by
  rw [nu, finiteProbability_eq_normalized,
    Measure.map_smul _ (M.shape_measurable V).aemeasurable, M.shape_measure]
  rfl

theorem normalizedShapeBeta_probability
    (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ) :
    IsProbabilityMeasure (normalizedShapeBeta M V) := by
  rw [← shape_measure M V]
  letI := nu_probability M V
  infer_instance

theorem full_from_source (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ)
    (Y : ℝ) (hY : OffsetAdmissible F ζ hζ R P (nativeRecipe F ζ hζ R P) V Y) :
    M.full = fullShell F ζ hζ R P (nativeRecipe F ζ hζ R P) V Y :=
  M.from_source V Y hY

end DedekindZetaZeroFree.KPMsNativeOffsetComparison

end
