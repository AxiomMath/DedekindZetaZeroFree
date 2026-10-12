module

public import DedekindZetaZeroFree.Theta.Unfolding.FactorizationAndMellinNormalizationData
public import DedekindZetaZeroFree.Adeles.Haar.LocalFactorization

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical ENNReal
open NumberField MeasureTheory IsDedekindDomain
namespace DedekindZetaZeroFree.TraceHaarTransport
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩
local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf)ˣ := by
  constructor
  change (borel (SLocalProduct F A.Sf)).comap Units.val = borel _
  rw [← borel_comap, ← (ProbeSheet.units_val_isEmbedding A).isInducing.eq_induced]

def balancedSplit (A : SArithmeticData F)
    (p : ThetaProfileHaarSheets.PositiveAxis × A.G1) : A.G :=
  p.2.val * A.radialSection p.1.val p.1.property

theorem continuous_balancedSplit (A : SArithmeticData F) : Continuous (balancedSplit A) := by
  exact (continuous_subtype_val.comp continuous_snd).mul
    (A.continuous_radialSection.comp continuous_fst)

def sectionRatio (A : SArithmeticData F) (v : InfinitePlace F)
    (x : ThetaProfileHaarSheets.PositiveAxis) : A.G1 :=
  ⟨ThetaProfileHaarSheets.normSection A v x / A.radialSection x.val x.property, by
    change A.norm _ = 1
    rw [ProbeSheet.norm_div, ThetaProfileHaarSheets.norm_normSection,
      A.norm_radialSection, div_self x.property.ne']⟩

theorem split_ratio (A : SArithmeticData F) (v : InfinitePlace F)
    (x : ThetaProfileHaarSheets.PositiveAxis) (z : A.G1) :
    ThetaProfileHaarSheets.normSplit A v (x,z) = balancedSplit A (x,z * sectionRatio A v x) := by
  change _ * z.val = (z.val * (_ / _)) * _
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem map_balancedSplit (A : SArithmeticData F) (v : InfinitePlace F)
    (dt : Measure A.G1) [dt.IsHaarMeasure] :
    Measure.map (balancedSplit A) (ThetaProfileHaarSheets.positiveHaar.prod dt) =
      Measure.map (ThetaProfileHaarSheets.normSplit A v)
        (ThetaProfileHaarSheets.positiveHaar.prod dt) := by
  letI := ProbeSheet.secondCountable_G1 A
  letI := ProbeSheet.locallyCompact_G1 A
  ext s hs
  rw [Measure.map_apply (continuous_balancedSplit A).measurable hs,
    Measure.map_apply (f := ThetaProfileHaarSheets.normSplit A v)
      (ThetaProfileHaarSheets.normSplit A v).toHomeomorph.measurable hs]
  have hn : Measurable (fun p => ThetaProfileHaarSheets.normSplit A v p) :=
    (ThetaProfileHaarSheets.normSplit A v).toHomeomorph.measurable
  rw [← lintegral_indicator_one (hs.preimage (continuous_balancedSplit A).measurable),
    ← lintegral_indicator_one (hs.preimage hn)]
  change (∫⁻ p, (balancedSplit A ⁻¹' s).indicator
      (fun _ => (1 : ℝ≥0∞)) p ∂ThetaProfileHaarSheets.positiveHaar.prod dt) =
    (∫⁻ p, ((fun p => ThetaProfileHaarSheets.normSplit A v p) ⁻¹' s).indicator
      (fun _ => (1 : ℝ≥0∞)) p ∂ThetaProfileHaarSheets.positiveHaar.prod dt)
  have h1 : Measurable ((balancedSplit A ⁻¹' s).indicator
      (fun _ : ThetaProfileHaarSheets.PositiveAxis × A.G1 => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hs.preimage (continuous_balancedSplit A).measurable)
  have h2 : Measurable (((fun p => ThetaProfileHaarSheets.normSplit A v p) ⁻¹' s).indicator
      (fun _ : ThetaProfileHaarSheets.PositiveAxis × A.G1 => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hs.preimage hn)
  rw [lintegral_prod (μ := ThetaProfileHaarSheets.positiveHaar) (ν := dt) _ h1.aemeasurable,
    lintegral_prod (μ := ThetaProfileHaarSheets.positiveHaar) (ν := dt) _ h2.aemeasurable]
  apply lintegral_congr
  intro x
  simpa only [Set.indicator_apply, Set.mem_preimage, split_ratio] using
    (lintegral_mul_right_eq_self (μ := dt)
      (fun z => s.indicator (fun _ => (1 : ℝ≥0∞)) (balancedSplit A (x,z)))
      (sectionRatio A v x)).symm

 theorem positiveHaar_map_radial :
    Measure.map (Subtype.val : ThetaProfileHaarSheets.PositiveAxis → ℝ)
      ThetaProfileHaarSheets.positiveHaar = ProbeSheet.radialMeasure := by
  rw [ThetaProfileHaarSheets.positiveHaar_map_val, ProbeSheet.radialMeasure,
    restrict_withDensity measurableSet_Ioi]
  simp only [one_div]

theorem balanced_probe_map (R : PrincipalMellin.ActualRecipe S η) :
    Measure.map (ProbeSheet.localUnits R.A)
      (Measure.map (balancedSplit R.A)
        (ThetaProfileHaarSheets.positiveHaar.prod R.probe.domain.measure)) =
      R.probe.multiplicativeMeasure := by
  letI := ProbeSheet.secondCountable_G1 R.A
  letI := ProbeSheet.locallyCompact_G1 R.A
  letI : R.probe.domain.measure.IsHaarMeasure := R.probe.domain.haar
  have hm : Measure.map (Prod.map (Subtype.val : ThetaProfileHaarSheets.PositiveAxis → ℝ) id)
      (ThetaProfileHaarSheets.positiveHaar.prod R.probe.domain.measure) =
      ProbeSheet.radialMeasure.prod R.probe.domain.measure := by
    rw [← Measure.map_prod_map _ _ continuous_subtype_val.measurable measurable_id,
      positiveHaar_map_radial, Measure.map_id]
  rw [R.normalization.disintegration, ← hm,
    Measure.map_map (ProbeSheet.measurable_sheetPoint R.A) (by fun_prop),
    Measure.map_map (ProbeSheet.continuous_localUnits R.A).measurable
      (continuous_balancedSplit R.A).measurable]
  congr 1
  funext p
  simp [balancedSplit, ProbeSheet.sheetPoint, ProbeSheet.ell, p.1.property, map_mul]

 theorem section_integral (R : PrincipalMellin.ActualRecipe S η)
    (x : ThetaProfileHaarSheets.PositiveAxis) (z : R.A.G1) (f : R.A.G → ℂ)
    (hf : Integrable (fun y : R.A.G1 => f (y.val * R.A.radialSection x.val x.property))
      R.probe.domain.measure) :
    (MeasureTheory.integral R.probe.domain.measure
      (fun y : R.A.G1 => f (y.val * z.val * R.A.radialSection x.val x.property))) =
    MeasureTheory.integral R.probe.domain.measure
      (fun y : R.A.G1 => f (y.val * R.A.radialSection x.val x.property)) := by
  letI := ProbeSheet.secondCountable_G1 R.A
  letI := ProbeSheet.locallyCompact_G1 R.A
  letI : R.probe.domain.measure.IsHaarMeasure := R.probe.domain.haar
  have _hi := hf.comp_mul_right (μ := R.probe.domain.measure) z
  exact integral_mul_right_eq_self (μ := R.probe.domain.measure)
    (fun y : R.A.G1 => f (y.val * R.A.radialSection x.val x.property)) z

 theorem finite_trace_mass (p : KPFinitePlace F) :
    localNormalizedHaar F p {x | ‖x‖ ≤ 1} = ENNReal.ofReal (PoissonS.integerVolume F p) := by
  have h := (ProbeFourierPoissonFoundation.productHaar_normalization F {p}).2.1 ⟨p, by simp⟩
  exact h

theorem probe_polar_factors (R : PrincipalMellin.ActualRecipe S η) :
    ∃ (μ : ∀ p : R.A.Sf, Measure (p.val.adicCompletion F)ˣ)
      (ν : InfinitePlace F → Measure Circle),
      (∀ p, (μ p).IsHaarMeasure) ∧ (∀ w, (ν w).IsHaarMeasure) ∧
      ∀ v : InfinitePlace F,
        Measure.map (ThetaProfileHaarSheets.normSplit R.A v)
          (ThetaProfileHaarSheets.positiveHaar.prod R.probe.domain.measure) =
          ThetaPositiveSheetMellin.productHaar R.A μ ν := by
  letI : R.probe.multiplicativeMeasure.IsHaarMeasure := R.probe.multiplicativeHaar
  letI : R.probe.domain.measure.IsHaarMeasure := R.probe.domain.haar
  obtain ⟨μ, ν, hμ, hν, he⟩ :=
    ProbeHaarFactorization.exists_productHaar_localUnits_eq R.A R.probe.multiplicativeMeasure
  refine ⟨μ, ν, hμ, hν, ?_⟩
  intro v
  rw [← map_balancedSplit R.A v]
  apply (ProbeSheet.localUnitsContinuous R.A).toHomeomorph.toMeasurableEquiv.map_measurableEquiv_injective
  exact (balanced_probe_map R).trans he.symm

end DedekindZetaZeroFree.TraceHaarTransport

end
