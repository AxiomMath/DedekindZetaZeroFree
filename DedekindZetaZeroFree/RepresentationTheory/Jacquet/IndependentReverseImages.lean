module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.FrequencyNormalization
public import DedekindZetaZeroFree.CharacterSums.Gauss.TameIntertwiningResidueCharacters
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.FrequencyTransport
public import DedekindZetaZeroFree.Metaplectic.Weil.ReverseIntertwiningPolarizationNaturality

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualWhittaker
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameTransposeLiteralCoefficients KPTameTransposeLiteral
open KPTameValuationCoordinates
open _root_.DedekindZetaZeroFree.ActualReverseMinorFrequencyNormalization renaming exists_actual_conductor_frequency → exists_actual_conductor_frequency
open _root_.DedekindZetaZeroFree.ActualReverseMinorTwoColumns renaming exists_actual_tame_two_columns → exists_actual_tame_two_columns
open _root_.DedekindZetaZeroFree.ActualReverseMinorFrequency renaming actual_reverse_frequency_pair_transport → actual_reverse_frequency_pair_transport
open _root_.DedekindZetaZeroFree.ActualReverseMinorPolarization renaming actual_reverse_pair_transport → actual_reverse_pair_transport
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

 local instance independentReverseImagesPlusSectionAddCommGroup : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance

local instance independentReverseImagesMinusSectionAddCommGroup : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance

private theorem pair_of_arithmetic_inputs
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (a : (LocalField F q)ˣ)
    (hconductor : HasConductorIntegers F q (KPKirillovProjectorGerms.frequencyCharacter F q a))
    [Fintype (Residue F q)]
    (κ : MulChar (Residue F q) ℂ) (hκ : HasPiFirstOrientation F ζ hζ q π κ)
    (ψbar : AddChar (Residue F q) ℂ)
    (hbar : HasConductorOneResidue F q π (KPKirillovProjectorGerms.frequencyCharacter F q a) ψbar) :
    ∃ v₀ v₂ : sectionSpace S.borel P .minus 0,
      LinearIndependent ℂ ![
        rootCoinvariantsMk (IPlus S.borel P) (KPLocalJacquetImage.root S.borel)
          (KPKirillovProjectorGerms.frequencyCharacter F q 1)
          (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₀),
        rootCoinvariantsMk (IPlus S.borel P) (KPLocalJacquetImage.root S.borel)
          (KPKirillovProjectorGerms.frequencyCharacter F q 1)
          (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₂)] := by
  obtain ⟨P₀, hP₀, hn₀⟩ := normalized_tame_extension_exists F ζ hζ q S htame
  have hcircle : Continuous (Circle.toUnits : Circle → ℂˣ) := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · have he : (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ)) =
          fun z : Circle => ((z : ℂ))⁻¹ := by
        funext z
        rw [Units.val_inv_eq_inv_val]
        rfl
      rw [he]
      exact continuous_subtype_val.inv₀ (fun z => Circle.coe_ne_zero z)
  have hψ : Continuous (KPKirillovProjectorGerms.frequencyCharacter F q a) :=
    hcircle.comp ((continuous_localFiniteCharacter F q).comp
      (continuous_const.mul continuous_toAdd))
  have hunitary : ∀ x, ‖(KPKirillovProjectorGerms.frequencyCharacter F q a x : ℂ)‖ = 1 := by
    intro x
    exact Circle.norm_coe _
  obtain ⟨v₀, v₂, hi⟩ := exists_actual_tame_two_columns F ζ hζ q S P₀ hP₀
    μ hμ htame hn₀ π hπ
    (KPKirillovProjectorGerms.frequencyCharacter F q a) hψ hunitary hconductor κ hκ ψbar hbar
  let t : actualTorus F ζ hζ q := ActualFiniteTorus.torusLift F ζ hζ q a
  have ht : S.borel.coordinate t = a := S.coordinate_lift t a (by
    simp [t, ActualFiniteTorus.torusLift, ActualFiniteTorus.normalWord, ActualFiniteTorus.central])
  have hfreq := actual_reverse_frequency_pair_transport F ζ hζ q S P₀
    μ hμ t a 1 (by rw [ht]; simp) v₀ v₂ hi
  obtain ⟨e⟩ := independence_of_polarization S.heisenberg P₀ P
  have hfinal := actual_reverse_pair_transport F ζ hζ q S P₀ P e μ hμ
    (KPLocalJacquetImage.root S.borel) (KPKirillovProjectorGerms.frequencyCharacter F q 1)
    (IMinus S.borel P₀ (S.borel.torus t : ActualCover F ζ hζ q) v₀)
    (IMinus S.borel P₀ (S.borel.torus t : ActualCover F ζ hζ q) v₂) hfreq
  exact ⟨_, _, hfinal⟩

theorem exists_reverse_independent_columns
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ∃ v₀ v₂ : sectionSpace S.borel P .minus 0,
      LinearIndependent ℂ ![
        rootCoinvariantsMk (IPlus S.borel P) (KPLocalJacquetImage.root S.borel)
          (KPKirillovProjectorGerms.frequencyCharacter F q 1)
          (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₀),
        rootCoinvariantsMk (IPlus S.borel P) (KPLocalJacquetImage.root S.borel)
          (KPKirillovProjectorGerms.frequencyCharacter F q 1)
          (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₂)] := by
  letI : Fintype (Residue F q) := Fintype.ofFinite _
  let π := actualFamilyUniformizer F q
  have hπ := actualFamilyUniformizer_spec F q
  obtain ⟨a, hconductor⟩ := exists_actual_conductor_frequency F q
  have hcircle : Continuous (Circle.toUnits : Circle → ℂˣ) := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · have he : (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ)) =
          fun z : Circle => ((z : ℂ))⁻¹ := by
        funext z
        rw [Units.val_inv_eq_inv_val]
        rfl
      rw [he]
      exact continuous_subtype_val.inv₀ (fun z => Circle.coe_ne_zero z)
  have hψ : Continuous (KPKirillovProjectorGerms.frequencyCharacter F q a) :=
    hcircle.comp ((continuous_localFiniteCharacter F q).comp
      (continuous_const.mul continuous_toAdd))
  obtain ⟨κ, hκ, _⟩ := KPLocalTameIntertwiningBlock.actual_pi_first_residue F ζ hζ q htame π
  obtain ⟨ψbar, hbar, _⟩ := KPLocalTameIntertwiningBlock.actual_conductor_one_residue
    F q π hπ (KPKirillovProjectorGerms.frequencyCharacter F q a) hψ hconductor
  exact pair_of_arithmetic_inputs F ζ hζ q S P μ hμ htame π hπ a hconductor κ hκ ψbar hbar

end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualWhittaker

end
