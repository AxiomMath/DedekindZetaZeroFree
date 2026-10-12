module

public import DedekindZetaZeroFree.Theta.Periods.RationalOrbitFrequencies

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem continuous_pregroupingSheet_integrable (N : TraceHaarTransport R)
    (w : InfinitePlace F) (l : PositiveAxis) (f : Sheet R.A l → ℂ) (hf : Continuous f) :
    letI := N.groupHaar_isHaar;
    Integrable f (pregroupingSheetHaar R.A w N.groupHaar l) := by
  letI := N.groupHaar_isHaar
  letI := kernelHaar_isHaarMeasure R.A w N.groupHaar
  rw [pregroupingSheetHaar_eq_map]
  apply (sheetTranslation R.A w l).measurableEmbedding.integrable_map_iff.mpr
  exact ((hf.comp (sheetTranslation R.A w l).continuous).continuousOn.integrableOn_compact
    (μ := kernelHaar R.A w N.groupHaar) (pregroupingDomain R.A).compact_closure).mono_set
      subset_closure

theorem frequency_sheet_integrable (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (ξ : ThetaReflectionData.Frequency R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    Integrable (fun z : Sheet R.A l => ‖digitWeight R m d *
      frequencyValue R Q T v ξ (signedArgument R m b z.val d)‖)
      (pregroupingSheetHaar R.A P.v₀ N.groupHaar l) := by
  letI := N.groupHaar_isHaar
  have hc : Continuous (fun z : Sheet R.A l => digitWeight R m d *
      frequencyValue R Q T v ξ (signedArgument R m b z.val d)) :=
    continuous_const.mul ((frequencyValue_continuous R T v ξ).comp
      ((DigitMasks.signedArgument_continuous R m b d).comp continuous_subtype_val))
  exact (continuous_pregroupingSheet_integrable R N P.v₀ l _ hc).norm

theorem orbit_sheet_integrable (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (l : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    Integrable (fun z : Sheet R.A l => ‖digitWeight R m d *
      orbitFrequencyValue R Q T v i (signedArgument R m b z.val d)‖)
      (pregroupingSheetHaar R.A P.v₀ N.groupHaar l) := by
  letI := N.groupHaar_isHaar
  have hc : Continuous (fun z : Sheet R.A l => digitWeight R m d *
      orbitFrequencyValue R Q T v i (signedArgument R m b z.val d)) :=
    continuous_const.mul ((orbitFrequencyValue_continuous R T v i).comp
      ((DigitMasks.signedArgument_continuous R m b d).comp continuous_subtype_val))
  exact (continuous_pregroupingSheet_integrable R N P.v₀ l _ hc).norm

end DedekindZetaZeroFree.OrbitFrequencies

end
