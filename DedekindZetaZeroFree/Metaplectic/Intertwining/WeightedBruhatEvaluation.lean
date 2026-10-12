module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.InverseRootInnerHaarValues
public import DedekindZetaZeroFree.CharacterSums.Gauss.LocalResidueUnitHaarIntegral
public import DedekindZetaZeroFree.Metaplectic.Intertwining.DiagonalBorelCoordinatesAndCoefficientNorms
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseCompactLaurentAnnulus
public import DedekindZetaZeroFree.Metaplectic.Torus.CubicHeisenbergInducingData

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeUnitNumeratorReduction

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates
open KPTameTransposeLiteral KPRankOneShellContinuation

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

variable (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ξ : (valuation (LocalField F q)).integer) (hξ : IsPrimitiveRoot ξ 3)

theorem eventual_deformed_minusTest_bruhat_values
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (a : ActualCover F ζ hζ q)
      (f : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP a m f → ∀ s : ℂ,
      (∀ (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q),
        k ∈ splitCongruenceSet F ζ hζ q m →
        let g := b * a * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)
        ((deformedTest F ζ hζ q S P hP f s).val g).val 1 =
          normPower (LocalField F q)
            (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
            (sourceParameter .minus s) * chi F ζ hζ q S P hP .minus b) ∧
      (∀ g : ActualCover F ζ hζ q,
        g ∉ testSupport F ζ hζ q S P a m →
        ((deformedTest F ζ hζ q S P hP f s).val g).val 1 = 0) := by
  obtain ⟨M, hM⟩ :=
    KPTameJacquetBruhatTests.BruhatGeometry.eventually_actual_raw_bruhat_geometry
      F ζ hζ q S P hP htame π hπ .minus
  refine ⟨M, fun m hm a f hf s => ?_⟩
  obtain ⟨K, hK, _, hn, _⟩ := hM m hm
  have hw : (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ =
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) :=
    inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q))
  have hcoord : ∀ ε v g, (scalarCoordinateEquiv F ζ hζ q S P hP ε v).val g =
      (v.val g).val 1 := fun _ _ _ => rfl
  constructor
  · intro b k hk
    have hkK : k ∈ K := by
      change k ∈ (K : Set (ActualCover F ζ hζ q))
      rwa [hK]
    have hk' := (hn k).mp hkK
    change _ ∈ (K : Set (ActualCover F ζ hζ q)) at hk'
    rw [hK, hw] at hk'
    have hh := KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.deformedTest_bruhat_scalar_value
      F ζ hζ q S P hP (scalarCoordinateEquiv F ζ hζ q S P hP) hcoord
      a m f hf b k (by
        simpa only [hw, KPTameJacquetBruhatTests.Raw.splitCongruenceSet,
          KPTameJacquetTestDuality.splitCongruenceSet] using hk') s
    exact hh
  · intro g hg
    have hz : f.val g = 0 := by
      by_contra h
      exact hg (hf.2.1 h)
    have hh := KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.deformedTest_scalar_value
      F ζ hζ q S P hP (scalarCoordinateEquiv F ζ hζ q S P hP) hcoord f s g
    change ((deformedTest F ζ hζ q S P hP f s).val g).val 1 = _ at hh
    rw [hh, hz, mul_zero]

end DedekindZetaZeroFree.KPTameTransposeUnitNumeratorReduction

end

end
