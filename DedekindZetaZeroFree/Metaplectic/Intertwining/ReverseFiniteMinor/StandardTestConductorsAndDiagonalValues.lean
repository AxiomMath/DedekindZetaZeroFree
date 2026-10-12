module

public import DedekindZetaZeroFree.CharacterSums.Gauss.TameInverseRootOuterIntegral
public import DedekindZetaZeroFree.Metaplectic.Weil.TamePolarizationObstruction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.LowShellContinuation
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalFieldUnitMass
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.InducingTransportGeometry

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorConductor
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open KPTameTransposeLiteralCoefficients KPTameTransposeLiteral
open _root_.DedekindZetaZeroFree.TameInverseRootValueAudit renaming eventual_actual_inverse_root_outer_gauss → eventual_actual_inverse_root_outer_gauss
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem eventual_actual_conductor_shell_integral
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    [Fintype (Residue F q)]
    (κ : MulChar (Residue F q) ℂ) (hκ : HasPiFirstOrientation F ζ hζ q π κ)
    (ψbar : AddChar (Residue F q) ℂ) (hbar : HasConductorOneResidue F q π ψ ψbar) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i : Fin 3,
      ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) m f →
      let f₀ := (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f
      (∫ x in conductorOneShell F q π,
        ((actualCanonicalReverseMap F ζ hζ q S P μ hμ f₀).val
          (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 *
          (ψ (Multiplicative.ofAdd (-x)) : ℂ) ∂μ) =
        (rootMass F ζ hζ q μ m : ℂ) *
          ((residueCardinality (LocalField F q) : ℂ) ^ (-(i.val : ℤ) - 2)) *
            g κ ψbar ((i.val : ZMod 3) + 1) := by
  obtain ⟨M, hM⟩ := eventual_actual_inverse_root_outer_gauss F ζ hζ q S P hP htame
    hnormalized μ hμ π hπ ψ hψ κ hκ ψbar hbar
  refine ⟨M, ?_⟩
  intro m hm i f hf
  dsimp only
  rw [KPTameTransposeLiteralShell.conductor_shell_haar_substitution F q μ π hπ]
  simp only [neg_div, neg_neg]
  have hvalue := hM m hm i f hf
  simp only [neg_div] at hvalue
  rw [hvalue]
  have hQ : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Residue F q)).ne'
  have hexp : -(i.val : ℤ) - 2 = 1 + (-(i.val : ℤ) - 3) := by omega
  rw [hexp, zpow_add₀ hQ, zpow_one]
  ring

end DedekindZetaZeroFree.ActualReverseMinorConductor

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorLowShellDiagonal
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open KPRankOneShellContinuation KPRankOneShellRepair KPTameTransposeLiteral
open KPTameTransposeBaseChart
open KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

open _root_.DedekindZetaZeroFree.TameQiConditionalObstruction renaming unitRegion → unitRegion
open _root_.DedekindZetaZeroFree.TameQiConditionalObstruction renaming eventual_all_tests → eventual_all_tests
open _root_.DedekindZetaZeroFree.TameQiConditionalObstruction renaming eventual_cleared_base_value → eventual_cleared_base_value
open _root_.DedekindZetaZeroFree.TameQiConditionalObstruction renaming anchor_monomial → anchor_monomial
open _root_.DedekindZetaZeroFree.ActualReverseMinorLowShell renaming actual_lowShell_continuation_of_numerator → actual_lowShell_continuation_of_numerator
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming testCompact → testCompact
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming testDeformation → testDeformation

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

private theorem eventual_diagonal_chamber_monomial
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ (M : ℕ) (d : ℤ), ∀ m ≥ M, ∀ (i : Fin 3)
      (fᵢ : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m fᵢ →
      ∀ s : ℂ, convergenceHalfPlane .minus s →
      denominator (LocalField F q) .minus s *
        (∫ x in lowShell F q, ∫ u : LocalField F q,
          diagonalDoubleKernel F ζ hζ q S P hP π i fᵢ s x u ∂μ ∂μ) =
        (Finsupp.single (d + (i.val : ℤ))
          ((rootMass F ζ hζ q μ m : ℂ) * (μ.real (unitRegion F q) : ℂ))).sum
          (fun n c => (evaluationUnit (LocalField F q) .minus s : ℂ) ^ n * c) := by
  obtain ⟨D, hD⟩ := eventual_all_tests F ζ hζ q S P hP htame π hπ
  obtain ⟨A, hA⟩ := eventual_cleared_base_value F ζ hζ q S P hP μ htame hnormalized π hπ
  obtain ⟨B, hB⟩ := eventual_minusTest_eq_chartDeformedScalar F ζ hζ q S P hP htame π hπ
  obtain ⟨T, hT⟩ := eventual_u_first_transport F ζ hζ q S P hP μ htame hnormalized π hπ
  obtain ⟨d, hd⟩ := anchor_monomial F ζ hζ q S π
  refine ⟨max D (max A (max B T)), d, ?_⟩
  intro m hm i fᵢ hfᵢ s hs
  have hmD : D ≤ m := (le_max_left _ _).trans hm
  have hmA : A ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmB : B ≤ m := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hmT : T ≤ m := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  obtain ⟨f, hf⟩ := hD m hmD
  have hf0 : IsMinusTest F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π (0, 0)) m (f 0) := by simpa using hf 0
  let c : ℂ := (rootMass F ζ hζ q μ m : ℂ) * (μ.real (unitRegion F q) : ℂ)
  have hbase : denominator (LocalField F q) .minus s *
      (∫ x in lowShell F q, ∫ u : LocalField F q,
        diagonalDoubleKernel F ζ hζ q S P hP π 0 (f 0) s x u ∂μ ∂μ) =
      (evaluationUnit (LocalField F q) .minus s : ℂ) ^ d * c := by
    have he : (∫ x in lowShell F q, ∫ u : LocalField F q,
        diagonalDoubleKernel F ζ hζ q S P hP π 0 (f 0) s x u ∂μ ∂μ) =
        baseChartChamberIntegral F ζ hζ q S P hP μ π m s := by
      unfold diagonalDoubleKernel baseChartChamberIntegral
      simp_rw [hB m hmB _ (f 0) hf0 s]
    rw [he, hA m hmA s hs, hd]
  rw [hT m hmT i (f 0) fᵢ hf0 hfᵢ s hs]
  simp only [Finsupp.sum_single_index, mul_zero]
  change denominator (LocalField F q) .minus s *
    ((evaluationUnit (LocalField F q) .minus s : ℂ) ^ (i.val : ℤ) * _) =
    (evaluationUnit (LocalField F q) .minus s : ℂ) ^ (d + (i.val : ℤ)) * c
  rw [mul_left_comm, hbase, zpow_add₀ (Units.ne_zero _)]
  ring

private theorem unit_region_complex_mass
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) :
    (μ.real (unitRegion F q) : ℂ) =
      1 - (residueCardinality (LocalField F q) : ℂ)⁻¹ := by
  have hm := KPTameTransposeBaseMassSteps.normalized_unit_complement_mass
    (LocalField F q) μ hμ
  change μ.real (unitRegion F q) =
    1 - (residueCardinality (LocalField F q) : ℝ)⁻¹ at hm
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
    Complex.ofReal_natCast] using congrArg Complex.ofReal hm

theorem eventual_actual_lowShell_diagonal_value
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
      (fᵢ : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m fᵢ →
      (∫ x in lowShell F q,
        ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
          ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm fᵢ)).val
          (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 ∂μ) =
        -(rootMass F ζ hζ q μ m : ℂ) / (residueCardinality (LocalField F q) : ℂ) := by
  obtain ⟨M, d, hM⟩ := eventual_diagonal_chamber_monomial
    F ζ hζ q S P hP μ htame hnormalized π hπ
  refine ⟨M, ?_⟩
  intro m hm i fᵢ hfᵢ
  let p : ℤ →₀ ℂ := Finsupp.single (d + (i.val : ℤ))
    ((rootMass F ζ hζ q μ m : ℂ) * (μ.real (unitRegion F q) : ℂ))
  have hp := hM m hm i fᵢ hfᵢ
  have hendpoint := actual_lowShell_continuation_of_numerator F ζ hζ q S P μ hμ
    (eta F ζ hζ q π i)
    ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm fᵢ) p
  have hr (u : LocalField F q) :
      (S.borel.upperRoot (Multiplicative.ofAdd u) : ActualCover F ζ hζ q) =
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u := by
    simpa only [KPRankOneOpenCellKernel.nLift] using (S.openCell P).upper_eq u
  have hrep : ∀ s : ℂ, convergenceHalfPlane .minus s →
      denominator (LocalField F q) .minus s *
        (∫ x in lowShell F q, ∫ u : LocalField F q,
          ((testDeformation F ζ hζ q S P
            ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm fᵢ) s).val
            (kernelW (LocalField F q) S.borel .minus *
              S.borel.upperRoot (Multiplicative.ofAdd u) *
              (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
                KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1 ∂μ ∂μ) =
        p.sum (fun n c => (evaluationUnit (LocalField F q) .minus s : ℂ) ^ n * c) := by
    intro s hs
    simpa only [diagonalDoubleKernel, deformedTest, testDeformation, testCompact, hr, p]
      using hp s hs
  have he := hendpoint hrep
  change (∫ x in lowShell F q, _ ∂μ) = _ at he
  rw [he]
  simp only [p, Finsupp.sum_single_index]
  rw [unit_region_complex_mass F q μ hμ]
  have hQ : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := 𝓀[LocalField F q])).ne'
  have hQ1 : (residueCardinality (LocalField F q) : ℂ) ≠ 1 := by
    have H : 1 < residueCardinality (LocalField F q) := Finite.one_lt_card
    exact_mod_cast H.ne'
  have hden : denominator (LocalField F q) .minus 0 =
      1 - (residueCardinality (LocalField F q) : ℂ) := by
    simp [denominator, KPRankOneRootParameter.r]
  rw [hden]
  field_simp
  <;> ring

end DedekindZetaZeroFree.ActualReverseMinorLowShellDiagonal

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorStandardConductor
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open KPTameTransposeLiteralCoefficients KPTameTransposeLiteral KPTameValuationCoordinates
open _root_.DedekindZetaZeroFree.ActualReverseMinorConductor renaming eventual_actual_conductor_shell_integral → eventual_actual_conductor_shell_integral
open _root_.DedekindZetaZeroFree.ActualReverseMinorLowShellDiagonal renaming eventual_actual_lowShell_diagonal_value → eventual_actual_lowShell_diagonal_value
open _root_.DedekindZetaZeroFree.KPTameTransposeLiteral renaming transport_test → transport_test
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

def standardConductorIntegral (π : (LocalField F q)ˣ)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (i : Fin 3)
    (f : scalarSections F ζ hζ q S P hP .minus) : ℂ :=
  ∫ x in conductorOneShell F q π,
    ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
      ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f)).val
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 *
      (ψ (Multiplicative.ofAdd (-x)) : ℂ) ∂μ

private theorem standardConductorIntegral_smul
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (i : Fin 3) (c : ℂ) (f : scalarSections F ζ hζ q S P hP .minus) :
    standardConductorIntegral F ζ hζ q S P hP μ hμ π ψ i (c • f) =
      c * standardConductorIntegral F ζ hζ q S P hP μ hμ π ψ i f := by
  simp only [standardConductorIntegral, map_smul]
  change (∫ x in conductorOneShell F q π, (c * _) * _ ∂μ) = _
  simp_rw [mul_assoc]
  exact integral_const_mul c _

theorem eventual_actual_standard_conductor_shell_value
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    [Fintype (Residue F q)]
    (κ : MulChar (Residue F q) ℂ) (hκ : HasPiFirstOrientation F ζ hζ q π κ)
    (ψbar : AddChar (Residue F q) ℂ) (hbar : HasConductorOneResidue F q π ψ ψbar) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i : Fin 3,
      ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP
        (eta F ζ hζ q π ⟨(1 - (i.val : ZMod 3)).val, ZMod.val_lt _⟩) m f →
      standardConductorIntegral F ζ hζ q S P hP μ hμ π ψ i f =
        (rootMass F ζ hζ q μ m : ℂ) *
          (residueCardinality (LocalField F q) : ℂ) ^
            (transportExponent i - (i.val : ℤ) - 2) *
          g κ ψbar ((i.val : ZMod 3) + 1) := by
  obtain ⟨M, hM⟩ := eventual_actual_conductor_shell_integral F ζ hζ q S P hP htame
    hnormalized μ hμ π hπ ψ hψ κ hκ ψbar hbar
  refine ⟨M, ?_⟩
  intro m hm i f hf
  obtain ⟨h, heq, hc⟩ := actual_minus_transports F ζ hζ q S P hP π hπ i
  let Q : ℂ := residueCardinality (LocalField F q)
  let c : ℂ := Q ^ transportExponent i
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    exact_mod_cast (Nat.card_pos (α := Residue F q)).ne'
  have hc0 : c ≠ 0 := zpow_ne_zero _ hQ
  have htf : IsMinusTest F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) m (c⁻¹ • f) := by
    rw [heq]
    exact transport_test F ζ hζ q S P hP h _ m f c hc hc0 hf
  have hv := hM m hm i (c⁻¹ • f) htf
  change standardConductorIntegral F ζ hζ q S P hP μ hμ π ψ i (c⁻¹ • f) = _ at hv
  rw [standardConductorIntegral_smul] at hv
  calc
    standardConductorIntegral F ζ hζ q S P hP μ hμ π ψ i f =
        c * (c⁻¹ * standardConductorIntegral F ζ hζ q S P hP μ hμ π ψ i f) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    _ = c * ((rootMass F ζ hζ q μ m : ℂ) * Q ^ (-(i.val : ℤ) - 2) *
        g κ ψbar ((i.val : ZMod 3) + 1)) := by rw [hv]
    _ = _ := by
      change Q ^ transportExponent i * (_ * Q ^ (-(i.val : ℤ) - 2) * _) = _
      have he : transportExponent i - (i.val : ℤ) - 2 =
          transportExponent i + (-(i.val : ℤ) - 2) := by omega
      rw [he, zpow_add₀ hQ]
      ring

private theorem eventual_actual_standard_conductor_diag_two
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    [Fintype (Residue F q)]
    (κ : MulChar (Residue F q) ℂ) (hκ : HasPiFirstOrientation F ζ hζ q π κ)
    (ψbar : AddChar (Residue F q) ℂ) (hbar : HasConductorOneResidue F q π ψ ψbar) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP (eta F ζ hζ q π 2) m f →
      standardConductorIntegral F ζ hζ q S P hP μ hμ π ψ 2 f =
        -(rootMass F ζ hζ q μ m : ℂ) *
          (residueCardinality (LocalField F q) : ℂ) ^ (-2 : ℤ) := by
  obtain ⟨M, hM⟩ := eventual_actual_standard_conductor_shell_value F ζ hζ q S P hP μ hμ
    htame hnormalized π hπ ψ hψ κ hκ ψbar hbar
  refine ⟨M, ?_⟩
  intro m hm f hf
  have hv := hM m hm 2 f
  have hl : (⟨(1 - ((2 : Fin 3).val : ZMod 3)).val, ZMod.val_lt _⟩ : Fin 3) = 2 := by
    decide
  rw [hl] at hv
  have he := hv hf
  have hg : g κ ψbar ((2 : Fin 3).val + 1) = -1 := by
    have hl : (((2 : Fin 3).val : ZMod 3) + 1) = 0 := by decide
    rw [hl]
    exact KPTameGauss.cubicGaussSum_zero κ ψbar hbar.1
  rw [hg] at he
  norm_num [transportExponent] at he ⊢
  convert he using 1

theorem eventual_actual_first_two_shells_diag_two
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    (hconductor : HasConductorIntegers F q ψ)
    [Fintype (Residue F q)]
    (κ : MulChar (Residue F q) ℂ) (hκ : HasPiFirstOrientation F ζ hζ q π κ)
    (ψbar : AddChar (Residue F q) ℂ) (hbar : HasConductorOneResidue F q π ψ ψbar) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP (eta F ζ hζ q π 2) m f →
      let R := (scalarCoordinateEquiv F ζ hζ q S P hP .plus)
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ
          ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f))
      (∫ x in lowShell F q,
        jacquetIntegrand F ζ hζ q S P hP .plus ψ (eta F ζ hζ q π 2) R x ∂μ) +
        standardConductorIntegral F ζ hζ q S P hP μ hμ π ψ 2 f =
          -(rootMass F ζ hζ q μ m : ℂ) *
            ((residueCardinality (LocalField F q) : ℂ)⁻¹ +
              (residueCardinality (LocalField F q) : ℂ) ^ (-2 : ℤ)) := by
  obtain ⟨A, hA⟩ := eventual_actual_lowShell_diagonal_value F ζ hζ q S P hP
    htame hnormalized μ hμ π hπ
  obtain ⟨B, hB⟩ := eventual_actual_standard_conductor_diag_two F ζ hζ q S P hP μ hμ
    htame hnormalized π hπ ψ hψ κ hκ ψbar hbar
  refine ⟨max A B, ?_⟩
  intro m hm f hf
  have ha := hA m ((le_max_left _ _).trans hm) 2 f
  have hd : diagonalLift F ζ hζ q π (((2 : Fin 3).val : ℤ), 0) =
      eta F ζ hζ q π 2 := by
    simp [diagonalLift, eta, KPPGLLocalCover.A, KPStandardLocalRootLifts.A]
  rw [hd] at ha
  have hv := ha hf
  have hi : (∫ x in lowShell F q,
      jacquetIntegrand F ζ hζ q S P hP .plus ψ (eta F ζ hζ q π 2)
        ((scalarCoordinateEquiv F ζ hζ q S P hP .plus)
          (actualCanonicalReverseMap F ζ hζ q S P μ hμ
            ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f))) x ∂μ) =
      (∫ x in lowShell F q,
        ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
          ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f)).val
          (eta F ζ hζ q π 2 * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 ∂μ) := by
    apply setIntegral_congr_fun (valuation (LocalField F q)).isOpen_integer.measurableSet
    intro x hx
    have hneg : -x ∈ (valuation (LocalField F q)).integer :=
      (valuation (LocalField F q)).integer.neg_mem hx
    have hp := (hconductor 1).mpr ((valuation (LocalField F q)).integer.one_mem) ⟨-x, hneg⟩
    simp only [mul_one] at hp
    simp only [jacquetIntegrand, hp, Units.val_one, mul_one]
    rfl
  dsimp only
  rw [hi, hv, hB m ((le_max_right _ _).trans hm) f hf]
  simp only [div_eq_mul_inv]
  ring

include S P hμ in

theorem actual_first_two_shells_diag_two_value_ne_zero
    (m : ℕ) (hm : 0 < m) :
    -(rootMass F ζ hζ q μ m : ℂ) *
      ((residueCardinality (LocalField F q) : ℂ)⁻¹ +
        (residueCardinality (LocalField F q) : ℂ) ^ (-2 : ℤ)) ≠ 0 := by
  have hmass : (rootMass F ζ hζ q μ m : ℂ) ≠ 0 := by
    exact_mod_cast (KPTameTransposeUnitNumeratorSteps.rootMass_pos F ζ hζ q S P μ hμ m hm).ne'
  have hQ : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := Residue F q))
  apply mul_ne_zero (neg_ne_zero.mpr hmass)
  have hpos : 0 < (residueCardinality (LocalField F q) : ℝ)⁻¹ +
      (residueCardinality (LocalField F q) : ℝ) ^ (-2 : ℤ) :=
    add_pos (inv_pos.mpr hQ) (zpow_pos hQ _)
  have he : ((residueCardinality (LocalField F q) : ℂ)⁻¹ +
      (residueCardinality (LocalField F q) : ℂ) ^ (-2 : ℤ)) =
      ((residueCardinality (LocalField F q) : ℝ)⁻¹ +
        (residueCardinality (LocalField F q) : ℝ) ^ (-2 : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [he]
  exact_mod_cast hpos.ne'

end DedekindZetaZeroFree.ActualReverseMinorStandardConductor

end

end
