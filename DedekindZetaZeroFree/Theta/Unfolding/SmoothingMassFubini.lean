module

public import DedekindZetaZeroFree.Theta.Profiles.FrequencySheetIntegrability

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem sheet_mass_coordinates (N : TraceHaarTransport R) (w : InfinitePlace F)
    (l : PositiveAxis) (f : Sheet R.A l → ℂ) :
    letI := N.groupHaar_isHaar;
    (∫ z : Sheet R.A l, ‖f z‖ ∂pregroupingSheetHaar R.A w N.groupHaar l) =
      ∫ y : R.A.G1, ‖f (sheetTranslation R.A w l y)‖
        ∂((kernelHaar R.A w N.groupHaar).restrict (pregroupingDomain R.A).carrier) := by
  letI := N.groupHaar_isHaar
  rw [pregroupingSheetHaar_eq_map,
    (sheetTranslation R.A w l).measurableEmbedding.integral_map]

theorem smoothing_mass_integrable_of_product (N : TraceHaarTransport R)
    (w : InfinitePlace F) (Z : ℝ) (hZ : 0 < Z)
    (f : (t : PositiveAxis) → Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩ → ℂ)
    (hp : letI := N.groupHaar_isHaar;
      Integrable (fun p : PositiveAxis × R.A.G1 =>
        f p.1 (sheetTranslation R.A w ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2))
        (positiveHaar.prod ((kernelHaar R.A w N.groupHaar).restrict (pregroupingDomain R.A).carrier))) :
    letI := N.groupHaar_isHaar;
    Integrable (fun t : PositiveAxis =>
      ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩, ‖f t z‖
        ∂pregroupingSheetHaar R.A w N.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar := by
  letI := N.groupHaar_isHaar
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  simp_rw [sheet_mass_coordinates R N w]
  exact hp.integral_norm_prod_left

end DedekindZetaZeroFree.OrbitFrequencies

end
