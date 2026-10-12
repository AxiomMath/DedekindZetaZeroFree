module

public import DedekindZetaZeroFree.Theta.Unfolding.FactorizationAndMellinNormalizationData
public import DedekindZetaZeroFree.Theta.Whittaker.WeightedNormFiberEnvelope

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets
open scoped Classical Topology
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem uniform_power_bound_aux (A : SArithmeticData F)
    (w : InfinitePlace F) (μ : Measure A.G) [μ.IsHaarMeasure]
    (s B M : ℝ) (hs : -(1 / 4 : ℝ) < s) (hBs : s < B) (hM : 0 < M) :
    ∀ (dt : Measure A.G1), dt.IsHaarMeasure →
    Measure.map (normSplit A w) (positiveHaar.prod dt) = μ →
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x : PositiveAxis,
      Integrable (fun y : A.G1 => productPowerMajorant A M B
        (y.val * A.radialSection x.val x.property)) dt ∧
      (∫ y : A.G1, productPowerMajorant A M B
        (y.val * A.radialSection x.val x.property) ∂ dt) ≤ E * x.val ^ (-s) := by
  intro dt hh hd
  letI := hh
  have hk : kernelHaar A w μ = dt := by
    obtain ⟨ν, hν, huniq⟩ := exists_unique_kernelHaar A w μ
    exact (huniq _ ⟨inferInstance, map_product_kernelHaar A w μ⟩).trans
      (huniq _ ⟨hh, hd⟩).symm
  obtain ⟨E, hE, hbound⟩ := product_power_majorant_sheet_bound A w μ M B s hM hs hBs
  refine ⟨E, hE.le, ?_⟩
  intro x
  let f : A.G → ℝ := productPowerMajorant A M B
  have hi' : Integrable (fun y : A.G1 => f (normSection A w x * y.val)) dt := by
    have hp := (integrable_map_equiv
      (sheetTranslation A w x).toMeasurableEquiv
      (fun y : Sheet A x => f y.val)).mp (hbound x).1
    rw [hk] at hp
    exact hp
  let z : A.G1 := ⟨(normSection A w x)⁻¹ * A.radialSection x.val x.property, by
    change A.norm _ = 1
    rw [NormSheetsCoordinates.norm_mul, NormSheetsCoordinates.norm_inv,
      norm_normSection, A.norm_radialSection]
    exact inv_mul_cancel₀ x.property.ne'⟩
  have hz (y : A.G1) :
      normSection A w x * (z * y).val = y.val * A.radialSection x.val x.property := by
    dsimp [z]
    simp [mul_assoc, mul_comm, mul_left_comm]
  have hiu : Integrable (fun y : A.G1 => f (y.val * A.radialSection x.val x.property)) dt := by
    simpa only [Function.comp_def, hz] using
      (measurePreserving_mul_left dt z).integrable_comp_of_integrable hi'
  refine ⟨hiu, ?_⟩
  have heq : (∫ y : A.G1, f (y.val * A.radialSection x.val x.property) ∂ dt) =
      ∫ y : A.G1, f (normSection A w x * y.val) ∂ dt := by
    simpa only [hz] using integral_mul_left_eq_self
      (μ := dt) (fun y : A.G1 => f (normSection A w x * y.val)) z
  rw [heq]
  have hb := (hbound x).2
  rw [sheetHaar_integral_eq, hk] at hb
  exact hb

theorem uniform_power_bound (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (s B M : ℝ) (hs : -(1 / 4 : ℝ) < s)
    (hBs : s < B) (hM : 0 < M) :
    letI : MeasurableSpace R.A.G1 := borel _;
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x : PositiveAxis,
      Integrable (fun y : R.A.G1 => productPowerMajorant R.A M B
        (y.val * R.A.radialSection x.val x.property)) R.probe.domain.measure ∧
      (∫ y : R.A.G1, productPowerMajorant R.A M B
        (y.val * R.A.radialSection x.val x.property) ∂ R.probe.domain.measure) ≤
        E * x.val ^ (-s) := by
  letI := N.groupHaar_isHaar
  let w : InfinitePlace F := Classical.choice inferInstance
  have h := uniform_power_bound_aux R.A w N.groupHaar s B M hs hBs hM
  letI : MeasurableSpace R.A.G1 := Subtype.instMeasurableSpace
  have hmb : (@Subtype.instMeasurableSpace R.A.G (fun y => y ∈ R.A.G1)
      (inferInstance : MeasurableSpace R.A.G)) = borel R.A.G1 := BorelSpace.measurable_eq
  rw [hmb] at h
  exact h R.probe.domain.measure R.probe.domain.haar (N.disintegration w)

end DedekindZetaZeroFree.SheetRescaling

end
