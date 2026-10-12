module

public import DedekindZetaZeroFree.Theta.Unfolding.SmoothingMajorants

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem sheetCoordinate_continuous (v₀ : InfinitePlace F) (Z : ℝ) (hZ : 0 < Z) :
    Continuous (fun p : PositiveAxis × R.A.G1 =>
      (sheetTranslation R.A v₀ ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val) := by
  have hc : Continuous (fun p : PositiveAxis × R.A.G1 =>
      ((⟨p.1.val / Z, div_pos p.1.property hZ⟩ : PositiveAxis), p.2)) :=
    (((continuous_subtype_val.comp continuous_fst).div_const Z).subtype_mk _).prodMk
      continuous_snd
  have h := (normSplit R.A v₀).continuous.comp hc
  have he : (fun p : PositiveAxis × R.A.G1 =>
      (sheetTranslation R.A v₀ ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val) =
      (normSplit R.A v₀) ∘ (fun p : PositiveAxis × R.A.G1 =>
        ((⟨p.1.val / Z, div_pos p.1.property hZ⟩ : PositiveAxis), p.2)) := by
    funext p
    rfl
  rw [he]
  exact h

theorem masked_orbit_product_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) :
    letI := C.transport.groupHaar_isHaar;
    Integrable (fun p : PositiveAxis × R.A.G1 => C.packet.kernel p.1.val *
      orbitSheet R C v m b i ⟨p.1.val / Z, div_pos p.1.property hZ⟩
        (sheetTranslation R.A C.packet.v₀ ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2))
      (positiveHaar.prod ((kernelHaar R.A C.packet.v₀ C.transport.groupHaar).restrict
        (pregroupingDomain R.A).carrier)) := by
  letI := C.transport.groupHaar_isHaar
  have hi := integrable_finset_sum Finset.univ
    (fun d _ => C.absolute.orbit_product_integrable v m b Z hZ i d)
  have hm := (sheetMultiplier_measurable R C.packet v).comp
    (sheetCoordinate_continuous R C.packet.v₀ Z hZ).measurable
  have h := hi.mul_bdd hm.aestronglyMeasurable (c := 1)
    (Filter.Eventually.of_forall (fun p => sheetMultiplier_norm_le R C.packet v _))
  convert h using 1
  funext p
  simp only [orbitSheet, Function.comp_apply, sheetMultiplier, Pi.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem smoothingIntegrand_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (Z : ℝ) (hZ : 0 < Z) (i : OrbitIndex R) :
    Integrable (fun t : PositiveAxis => C.packet.kernel t.val *
      orbitIntegral R C v m b i ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar := by
  letI := C.transport.groupHaar_isHaar
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  have h := (masked_orbit_product_integrable R C v m b Z hZ i).integral_prod_left
  convert h using 1
  funext t
  rw [orbitIntegral, ← integral_const_mul, pregroupingSheetHaar_eq_map,
    (sheetTranslation R.A C.packet.v₀ ⟨t.val / Z, div_pos t.property hZ⟩).measurableEmbedding.integral_map]

end DedekindZetaZeroFree.OrbitExpansion

end
