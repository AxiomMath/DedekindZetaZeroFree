module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.DiagonalInverseRootSupport

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeLiteral
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

theorem fullDiagonal_torus_sheet_at_coordinate (h : HL F ζ hζ q S P) :
    ∃ e : rootsOfUnity 3 F, (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (S.borel.coordinate h.val) := by
  obtain ⟨⟨e, y⟩, he, _⟩ := (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.1 h.val
  dsimp only at he
  have he' : (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) y := he
  let c : actualTorus F ζ hζ q := (S.openCell P).centralTorus e
  have hc : (c : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e := by
    rw [← S.torus_full]
    exact (S.openCell P).central_eq e
  have ha : ((c⁻¹ * h.val : actualTorus F ζ hζ q) : ActualCover F ζ hζ q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) y := by
    change (c : ActualCover F ζ hζ q)⁻¹ * (h.val : ActualCover F ζ hζ q) = _
    rw [hc, he', inv_mul_cancel_left]
  have hcoord : S.borel.coordinate h.val = y := by
    have hh := S.coordinate_lift (c⁻¹ * h.val) y ha
    simpa only [map_mul, map_inv, c, (S.openCell P).central_coordinate e,
      inv_one, one_mul] using hh
  exact ⟨e, hcoord ▸ he'⟩

theorem fullDiagonal_coordinate_unit_sheet
    (h : HL F ζ hζ q S P)
    (hu : valuation (LocalField F q) (S.borel.coordinate h.val : LocalField F q) = 1) :
    ∃ (e : rootsOfUnity 3 F) (u : (KPTameCompact.O F q)ˣ),
      (h.val : ActualCover F ζ hζ q) =
        KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) := by
  let z : KPTameCompact.O F q := ⟨(S.borel.coordinate h.val : LocalField F q), hu.le⟩
  have hz : IsUnit z :=
    (Valuation.integer.integers (valuation (LocalField F q))).isUnit_iff_valuation_eq_one.mpr hu
  obtain ⟨u, hu⟩ := hz
  have hui : KPTameCompact.unitInclusion F q u = S.borel.coordinate h.val := by
    apply Units.ext
    exact congrArg (fun z : KPTameCompact.O F q => (z : LocalField F q)) hu
  obtain ⟨e, he⟩ := fullDiagonal_torus_sheet_at_coordinate F ζ hζ q S P h
  exact ⟨e, u, hui ▸ he⟩

theorem normalizedExtension_coordinate_unit_chiH_norm
    (hnormalized : RawNormalizedExtension F ζ hζ q S P)
    (ε : Sign) (h : HL F ζ hζ q S P)
    (hu : valuation (LocalField F q) (S.borel.coordinate h.val : LocalField F q) = 1) :
    ‖chiH F ζ hζ q S P hP ε h‖ = 1 := by
  obtain ⟨e, u, he⟩ := fullDiagonal_coordinate_unit_sheet F ζ hζ q S P h hu
  exact normalizedExtension_unit_sheet_chiH_norm F ζ hζ q S P hP hnormalized ε h e u he

end DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps

end
