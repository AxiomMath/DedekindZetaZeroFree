module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.WeightedBruhatEvaluation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeBaseChart

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation
open KPTameTransposeLiteral

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

def chartDeformedScalar (a : ActualCover F ζ hζ q) (m : ℕ) (s : ℂ)
    (g : ActualCover F ζ hζ q) : ℂ :=
  if hg : g ∈ testSupport F ζ hζ q S P a m then
    normPower (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
      (sourceParameter .minus s) *
        chi F ζ hζ q S P hP .minus (Classical.choose hg)
  else 0

def baseChartChamberIntegral (μ : Measure (LocalField F q))
    (π : (LocalField F q)ˣ) (m : ℕ) (s : ℂ) : ℂ :=
  ∫ x in lowShell F q, ∫ u : LocalField F q,
    chartDeformedScalar F ζ hζ q S P hP
      (diagonalLift F ζ hζ q π (0, 0)) m s
      (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (eta F ζ hζ q π (0 : Fin 3) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) ∂μ ∂μ

theorem eventual_minusTest_eq_chartDeformedScalar
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (a : ActualCover F ζ hζ q)
      (f : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP a m f → ∀ (s : ℂ) (g : ActualCover F ζ hζ q),
      ((deformedTest F ζ hζ q S P hP f s).val g).val 1 =
        chartDeformedScalar F ζ hζ q S P hP a m s g := by
  obtain ⟨M, hM⟩ :=
    KPTameTransposeUnitNumeratorReduction.eventual_deformed_minusTest_bruhat_values
      F ζ hζ q S P hP htame π hπ
  refine ⟨M, fun m hm a f hf s g => ?_⟩
  obtain ⟨hv, hz⟩ := hM m hm a f hf s
  by_cases hg : g ∈ testSupport F ζ hζ q S P a m
  · rw [chartDeformedScalar, dif_pos hg]
    set b : BL F ζ hζ q S P := Classical.choose hg with hb
    set k : ActualCover F ζ hζ q := Classical.choose (Classical.choose_spec hg) with hk
    obtain ⟨hkmem, hgeq⟩ := Classical.choose_spec (Classical.choose_spec hg)
    have hv' := hv b k hkmem
    rw [← hgeq] at hv'
    exact hv'
  · rw [chartDeformedScalar, dif_neg hg]
    exact hz g hg

end DedekindZetaZeroFree.KPTameTransposeBaseChart

end
