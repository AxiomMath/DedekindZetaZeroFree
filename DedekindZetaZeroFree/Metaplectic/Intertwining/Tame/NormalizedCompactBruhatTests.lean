module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormalizedResidueCharacterExtensions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMass

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

theorem eventual_base_minus_test_exists
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∃ f : scalarSections F ζ hζ q S P hP .minus,
      IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π (0, 0)) m f := by
  obtain ⟨m₀, hm₀⟩ :=
    KPTameJacquetBruhatTests.BruhatGeometry.eventually_actual_raw_bruhat_geometry
      F ζ hζ q S P hP htame π hπ .minus
  refine ⟨m₀, fun m hm => ?_⟩
  obtain ⟨K, hK, _hcompact, hweyl, hdescent, _⟩ := hm₀ m hm
  obtain ⟨test, htest⟩ :=
    KPTameJacquetBruhatTests.BruhatScalarTests.scalar_characteristic_sections
      F ζ hζ q S P hP .minus π m K hK hweyl hdescent
  have heta : KPTameJacquetBruhatTests.Raw.eta F ζ hζ q π (0 : Fin 3) =
      diagonalLift F ζ hζ q π (0, 0) := by
    simp [KPTameJacquetBruhatTests.Raw.eta, eta, diagonalLift,
      KPPGLLocalCover.A, KPStandardLocalRootLifts.A]
  have h1 : (1 : ActualCover F ζ hζ q) ∈ splitCongruenceSet F ζ hζ q m := by
    refine ⟨1, ?_⟩
    show KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (1 : KPLocalCube.LocalGL2 F q)) = 1
    rw [show KPLocalCover.sectionMap F ζ hζ (Sum.inr q)
      (1 : KPLocalCube.LocalGL2 F q) = 1 from rfl, map_one]
  refine ⟨test 0, (htest.1 0).1, ?_, ?_⟩
  · intro g hg
    obtain ⟨b, k, hk, rfl⟩ := (htest.1 0).2 hg
    exact ⟨b, k, hk, by rw [heta]⟩
  · have h := htest.2.2 0 (1 : ActualCover F ζ hζ q) h1
    rw [← heta]
    simpa using h

end DedekindZetaZeroFree.KPTameTransposeLiteralMass

end
