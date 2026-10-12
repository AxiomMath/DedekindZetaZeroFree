module

public import DedekindZetaZeroFree.Theta.Profiles.FrequencySheetIntegrability
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ProbeAndUniformSection

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem complex_uniform_integrable_iff (w : InfinitePlace F) (x : PositiveAxis)
    (f : R.A.G → ℂ) :
    Integrable (fun z : R.A.G1 => f (normSection R.A w x * z.val)) (GaussianSmoothing.probeHaar R) ↔
      Integrable (fun z : R.A.G1 => f (z.val * R.A.radialSection x.val x.property))
        (GaussianSmoothing.probeHaar R) := by
  letI := GaussianSmoothing.probeHaar_isHaar R
  let q := GaussianSmoothing.sectionRatio R.A w x
  have h (z : R.A.G1) : normSection R.A w x * z.val =
      (q * z).val * R.A.radialSection x.val x.property := by
    change _ = (normSection R.A w x / R.A.radialSection x.val x.property * z.val) * _
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  simp_rw [h]
  exact (measurePreserving_mul_left (GaussianSmoothing.probeHaar R) q).integrable_comp_emb
    (Homeomorph.mulLeft q).measurableEmbedding
    (g := fun z : R.A.G1 => f (z.val * R.A.radialSection x.val x.property))

theorem selected_full_sheet_integrable (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (H : SameResidueProfiles R Q T P) (v : R.A.UnitQuotient) (κ : R.A.V)
    (x : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    Integrable (fun y : Sheet R.A x => T.sheetIntegrand P v κ y.val)
      (sheetHaar R.A P.v₀ N.groupHaar x) := by
  letI := N.groupHaar_isHaar
  have hu : Integrable (fun y : R.A.G1 => T.sheetIntegrand P v κ
      (y.val * R.A.radialSection x.val x.property)) (GaussianSmoothing.probeHaar R) := by
    apply (GaussianSmoothing.probeHaar_integrable _).mpr
    simpa only [iteratedDeriv_zero, Real.exp_log x.property] using
      H.absolute_sheet_jets v κ 0 (by omega) x.val x.property
  have ht := (complex_uniform_integrable_iff R P.v₀ x _).mpr hu
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe]
  exact (sheetTranslation R.A P.v₀ x).measurableEmbedding.integrable_map_iff.mpr ht

theorem selected_full_sheet_norm_eq (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (H : SameResidueProfiles R Q T P) (v : R.A.UnitQuotient) (κ : R.A.V)
    (x : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    (∫ y : Sheet R.A x, ‖T.sheetIntegrand P v κ y.val‖
      ∂sheetHaar R.A P.v₀ N.groupHaar x) =
    @integral R.A.G1 ℝ _ _ (borel _) R.probe.domain.measure
      (fun y => ‖T.sheetIntegrand P v κ (y.val * R.A.radialSection x.val x.property)‖) := by
  letI := N.groupHaar_isHaar
  have hi := (selected_full_sheet_integrable R N T P H v κ x).norm
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe,
    (sheetTranslation R.A P.v₀ x).measurableEmbedding.integral_map]
  change (∫ z : R.A.G1, ‖T.sheetIntegrand P v κ (normSection R.A P.v₀ x * z.val)‖
    ∂GaussianSmoothing.probeHaar R) = _
  have ht : Integrable (fun z : R.A.G1 =>
      ‖T.sheetIntegrand P v κ (normSection R.A P.v₀ x * z.val)‖) (GaussianSmoothing.probeHaar R) := by
    rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe] at hi
    exact (sheetTranslation R.A P.v₀ x).measurableEmbedding.integrable_map_iff.mp hi
  rw [GaussianSmoothing.integral_uniform_eq N P.v₀ x (fun y => ‖T.sheetIntegrand P v κ y‖) ht,
    GaussianSmoothing.probeHaar_integral]

theorem selected_full_sheet_norm_bound (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (H : SameResidueProfiles R Q T P) (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v κ (x : PositiveAxis),
      letI := N.groupHaar_isHaar;
      (∫ y : Sheet R.A x, ‖T.sheetIntegrand P v κ y.val‖
        ∂sheetHaar R.A P.v₀ N.groupHaar x) ≤
      K * min (Real.rpow x.val (1 / 8)) (Real.rpow x.val (-B)) := by
  obtain ⟨K, hK, hb⟩ := H.absolute_sheet_bounds B hB 0 (by omega)
  refine ⟨K, hK, ?_⟩
  intro v κ x
  letI := N.groupHaar_isHaar
  rw [selected_full_sheet_norm_eq R N T P H]
  simpa only [iteratedDeriv_zero, Real.exp_log x.property] using hb v κ x.val x.property

end DedekindZetaZeroFree.OrbitFrequencies

end
