module

public import DedekindZetaZeroFree.Theta.Whittaker.TameTransposeShellCoefficients
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TorusEquivariantQuotient

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorLiteralAlgebra
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair
open KPTameJacquetTestDuality KPTameTransposeKernelUnfolding KPTameTransposeLiteralCoefficients
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem independent_of_diagonal_pairings
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (x₀ x₂ : X) (ell₀ ell₂ : Module.Dual ℂ X) (a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h00 : ell₀ x₀ = a) (h02 : ell₀ x₂ = 0)
    (h22 : ell₂ x₂ = b) : LinearIndependent ℂ ![x₀, x₂] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have H := congrArg ell₂ h
    exact hb (by simpa [h22] using H)
  · intro c h
    have H := congrArg ell₀ h
    exact ha (by simpa [map_smul, h00, h02] using H.symm)

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

 local instance fullPlusAdd : AddCommGroup (sectionSpace S.borel P .plus 0) :=
  inferInstance

 theorem scalar_coordinates_root
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (Λ : whittakerSpace F ζ hζ q S P hP .plus ψ)
    (x : Multiplicative (LocalField F q)) (v : sectionSpace S.borel P .plus 0) :
    Λ.val (scalarCoordinateEquiv F ζ hζ q S P hP .plus
      (IPlus S.borel P (KPLocalJacquetImage.root S.borel x) v)) =
        (ψ x : ℂ) • Λ.val (scalarCoordinateEquiv F ζ hζ q S P hP .plus v) := by
  have hr : KPLocalJacquetImage.root S.borel x =
      KPLocalSmoothRepresentation.upperRoot F ζ hζ q x :=
    (S.openCell P).upper_eq (Multiplicative.toAdd x)
  have he : scalarCoordinateEquiv F ζ hζ q S P hP .plus
      (IPlus S.borel P (KPLocalSmoothRepresentation.upperRoot F ζ hζ q x) v) =
      scalarAction F ζ hζ q S P hP .plus
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ q x)
        (scalarCoordinateEquiv F ζ hζ q S P hP .plus v) := rfl
  rw [hr, he]
  simpa only [smul_eq_mul] using
    Λ.property x (scalarCoordinateEquiv F ζ hζ q S P hP .plus v)

 def actual_scalar_reverse
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) :
    scalarSections F ζ hζ q S P hP .minus →ₗ[ℂ]
      scalarSections F ζ hζ q S P hP .plus :=
  (scalarCoordinateEquiv F ζ hζ q S P hP .plus).toLinearMap.comp
    ((actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap.comp
      (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm.toLinearMap)

def full_jacquet_dual
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (Λ : whittakerSpace F ζ hζ q S P hP .plus ψ) :
    Module.Dual ℂ (RootCoinvariants (IPlus S.borel P)
      (KPLocalJacquetImage.root S.borel) ψ) :=
  rootCoinvariantsLift (IPlus S.borel P) (KPLocalJacquetImage.root S.borel) ψ
    ⟨Λ.val.comp (scalarCoordinateEquiv F ζ hζ q S P hP .plus).toLinearMap,
      scalar_coordinates_root F ζ hζ q S P hP ψ Λ⟩

end DedekindZetaZeroFree.ActualReverseMinorLiteralAlgebra

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorTwoColumns
open scoped NumberField Classical Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameTransposeLiteralCoefficients KPTameTransposeLiteral
open KPTameValuationCoordinates
open _root_.DedekindZetaZeroFree.ActualReverseMinorStableAssembly renaming eventual_actual_stable_value_eq_two_shells → eventual_actual_stable_value_eq_two_shells
open _root_.DedekindZetaZeroFree.ActualReverseMinorConductorOffSupport renaming eventual_actual_conductor_shell_off_support → eventual_actual_conductor_shell_off_support
open _root_.DedekindZetaZeroFree.ActualReverseMinorStandardConductor renaming eventual_actual_first_two_shells_diag_two → eventual_actual_first_two_shells_diag_two
open _root_.DedekindZetaZeroFree.ActualReverseMinorStandardConductor renaming actual_first_two_shells_diag_two_value_ne_zero → actual_first_two_shells_diag_two_value_ne_zero
open _root_.DedekindZetaZeroFree.ActualReverseMinorStandardConductor renaming standardConductorIntegral → standardConductorIntegral
open _root_.DedekindZetaZeroFree.ActualReverseMinorOffDiagonal renaming actual_lowShell_integral_zero_of_differenceLabel_ne_zero → actual_lowShell_integral_zero_of_differenceLabel_ne_zero
open _root_.DedekindZetaZeroFree.ActualReverseMinorLowShellDiagonal renaming eventual_actual_lowShell_diagonal_value → eventual_actual_lowShell_diagonal_value
open _root_.DedekindZetaZeroFree.ActualReverseMinorLiteralAlgebra renaming full_jacquet_dual → full_jacquet_dual
open _root_.DedekindZetaZeroFree.ActualReverseMinorLiteralAlgebra renaming independent_of_diagonal_pairings → independent_of_diagonal_pairings
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

 local instance plusAdd : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance

local instance minusAdd : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance

private theorem diagonal_eta (π : (LocalField F q)ˣ) (j : Fin 3) :
    diagonalLift F ζ hζ q π ((j.val : ℤ), 0) = eta F ζ hζ q π j := by
  simp [diagonalLift, eta, KPPGLLocalCover.A, KPStandardLocalRootLifts.A]

 def actualScalarReverse :
    scalarSections F ζ hζ q S P hP .minus →ₗ[ℂ] scalarSections F ζ hζ q S P hP .plus :=
  (scalarCoordinateEquiv F ζ hζ q S P hP .plus).toLinearMap.comp
    ((actualCanonicalReverseMap F ζ hζ q S P μ hμ).toLinearMap.comp
      (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm.toLinearMap)

private theorem lowShell_nonoscillatory
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hconductor : HasConductorIntegers F q ψ) (π : (LocalField F q)ˣ) (i : Fin 3)
    (f : scalarSections F ζ hζ q S P hP .minus) :
    (∫ x in lowShell F q,
      jacquetIntegrand F ζ hζ q S P hP .plus ψ (eta F ζ hζ q π i)
        (actualScalarReverse F ζ hζ q S P hP μ hμ f) x ∂μ) =
    (∫ x in lowShell F q,
      ((actualCanonicalReverseMap F ζ hζ q S P μ hμ
        ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f)).val
          (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 ∂μ) := by
  apply setIntegral_congr_fun (valuation (LocalField F q)).isOpen_integer.measurableSet
  intro x hx
  have hneg : -x ∈ (valuation (LocalField F q)).integer :=
    (valuation (LocalField F q)).integer.neg_mem hx
  have hp := (hconductor 1).mpr ((valuation (LocalField F q)).integer.one_mem) ⟨-x, hneg⟩
  simp only [mul_one] at hp
  simp only [jacquetIntegrand, hp, Units.val_one, mul_one]
  rfl

include hP in
theorem exists_actual_tame_two_columns
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    (hunitary : ∀ x, ‖(ψ x : ℂ)‖ = 1)
    (hconductor : HasConductorIntegers F q ψ)
    [Fintype (Residue F q)]
    (κ : MulChar (Residue F q) ℂ) (hκ : HasPiFirstOrientation F ζ hζ q π κ)
    (ψbar : AddChar (Residue F q) ℂ) (hbar : HasConductorOneResidue F q π ψ ψbar) :
    ∃ v₀ v₂ : sectionSpace S.borel P .minus 0,
      LinearIndependent ℂ ![
        rootCoinvariantsMk (IPlus S.borel P) (KPLocalJacquetImage.root S.borel) ψ
          (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₀),
        rootCoinvariantsMk (IPlus S.borel P) (KPLocalJacquetImage.root S.borel) ψ
          (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₂)] := by
  classical
  have hdual := tame_jacquet_test_duality F ζ hζ q S P hP htame π hπ ψ hψ
    hunitary hconductor μ hμ
  obtain ⟨Λplus, hplus, _, _⟩ := hdual .plus
  obtain ⟨_, _, _, Mt, ht⟩ := hdual .minus
  obtain ⟨Md, hd⟩ := eventual_actual_lowShell_diagonal_value F ζ hζ q S P hP
    htame hnormalized μ hμ π hπ
  obtain ⟨Mo, ho⟩ := actual_lowShell_integral_zero_of_differenceLabel_ne_zero
    F ζ hζ q S P hP hnormalized μ hμ htame π hπ 0 (2,0) (by decide)
  obtain ⟨Mc, hc⟩ := eventual_actual_conductor_shell_off_support F ζ hζ q S P hP μ hμ π hπ ψ
  obtain ⟨M2, h2⟩ := eventual_actual_first_two_shells_diag_two F ζ hζ q S P hP μ hμ
    htame hnormalized π hπ ψ hψ hconductor κ hκ ψbar hbar
  have hs (i j : Fin 3) := eventual_actual_stable_value_eq_two_shells F ζ hζ q S P hP
    (scalarCoordinateEquiv F ζ hζ q S P hP) (by intros; rfl)
    htame μ hμ π hπ ψ hψ hconductor i ((j.val : ℤ),0)
  obtain ⟨M00, h00⟩ := hs 0 0
  obtain ⟨M02, h02⟩ := hs 0 2
  obtain ⟨M22, h22⟩ := hs 2 2
  let m := 1 + Mt + Md + Mo + Mc + M2 + M00 + M02 + M22
  have hmt : Mt ≤ m := by omega
  obtain ⟨_, _, _, test, htest, _, _⟩ := ht m hmt
  have hf (j : Fin 3) : IsMinusTest F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π ((j.val : ℤ),0)) m (test j) := by
    rw [diagonal_eta]
    exact htest j
  let R := actualScalarReverse F ζ hζ q S P hP μ hμ
  let Q : ℂ := residueCardinality (LocalField F q)
  let v : ℂ := rootMass F ζ hζ q μ m
  have hv0 : v ≠ 0 := by
    have hp := (ht m hmt).2.2.1
    dsimp [v]
    exact_mod_cast hp.ne'
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    exact_mod_cast (Nat.card_pos (α := Residue F q)).ne'
  have he00 : (Λplus 0).val (R (test 0)) = -v / Q := by
    have hstable := h00 m (by omega) (test 0) (hf 0)
    have hlow := hd m (by omega) 0 (test 0) (hf 0)
    have hcon := hc m (by omega) 0 0 (test 0) (hf 0) (by decide)
    have he := stable_value_unique F ζ hζ q S P hP .plus π ψ μ _ _
      (hplus 0 (R (test 0))) hstable
    change (Λplus 0).val (R (test 0)) =
      (∫ x in lowShell F q, jacquetIntegrand F ζ hζ q S P hP .plus ψ
        (eta F ζ hζ q π 0) (actualScalarReverse F ζ hζ q S P hP μ hμ (test 0)) x ∂μ) + _ at he
    rw [lowShell_nonoscillatory F ζ hζ q S P hP μ hμ ψ hconductor, hlow] at he
    have hcon' : (∫ x in KPTameTransposeKernelUnfoldingRaw.conductorOneShell F q π,
        jacquetIntegrand F ζ hζ q S P hP .plus ψ (eta F ζ hζ q π 0)
          (R (test 0)) x ∂μ) = 0 := hcon
    change (Λplus 0).val (R (test 0)) = -v / Q + _ at he
    erw [hcon', add_zero] at he
    exact he
  have he02 : (Λplus 0).val (R (test 2)) = 0 := by
    have hstable := h02 m (by omega) (test 2) (hf 2)
    have hlow := ho m (by omega) (test 2) (hf 2)
    have hcon := hc m (by omega) 0 2 (test 2) (hf 2) (by decide)
    have he := stable_value_unique F ζ hζ q S P hP .plus π ψ μ _ _
      (hplus 0 (R (test 2))) hstable
    change (Λplus 0).val (R (test 2)) =
      (∫ x in lowShell F q, jacquetIntegrand F ζ hζ q S P hP .plus ψ
        (eta F ζ hζ q π 0) (actualScalarReverse F ζ hζ q S P hP μ hμ (test 2)) x ∂μ) + _ at he
    rw [lowShell_nonoscillatory F ζ hζ q S P hP μ hμ ψ hconductor, hlow] at he
    have hcon' : (∫ x in KPTameTransposeKernelUnfoldingRaw.conductorOneShell F q π,
        jacquetIntegrand F ζ hζ q S P hP .plus ψ (eta F ζ hζ q π 0)
          (R (test 2)) x ∂μ) = 0 := hcon
    change (Λplus 0).val (R (test 2)) = 0 + _ at he
    erw [hcon', add_zero] at he
    exact he
  have he22 : (Λplus 2).val (R (test 2)) = -v * (Q⁻¹ + Q ^ (-2 : ℤ)) := by
    have hstable := h22 m (by omega) (test 2) (hf 2)
    have htwo := h2 m (by omega) (test 2) (by rw [← diagonal_eta]; exact hf 2)
    have he := stable_value_unique F ζ hζ q S P hP .plus π ψ μ _ _
      (hplus 2 (R (test 2))) hstable
    exact he.trans htwo
  refine ⟨(scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm (test 0),
    (scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm (test 2), ?_⟩
  apply independent_of_diagonal_pairings _ _
    (full_jacquet_dual F ζ hζ q S P hP ψ (Λplus 0))
    (full_jacquet_dual F ζ hζ q S P hP ψ (Λplus 2)) (-v / Q) (-v * (Q⁻¹ + Q ^ (-2 : ℤ)))
  · exact div_ne_zero (neg_ne_zero.mpr hv0) hQ
  · exact actual_first_two_shells_diag_two_value_ne_zero F ζ hζ q S P μ hμ m (by omega)
  · exact he00
  · exact he02
  · exact he22

end DedekindZetaZeroFree.ActualReverseMinorTwoColumns

end

end
