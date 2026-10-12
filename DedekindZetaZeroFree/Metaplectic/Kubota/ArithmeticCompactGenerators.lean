module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RootIndependenceAndExactness
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.CubicShellDeformation

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneTameSphericalFactor

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

theorem kernel_generators_mem_of_actual_compact
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hcompact : (S.iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) =
      (actualGoodCompactSplit F ζ hζ q ht).range) :
    S.borel.liftedW ∈ S.iwasawa.compact.toOpenSubgroup ∧
    ∀ x : (valuation (LocalField F q)).integer,
      (S.borel.upperRoot (Multiplicative.ofAdd (x : LocalField F q)) : ActualCover F ζ hζ q) ∈
        S.iwasawa.compact.toOpenSubgroup := by
  constructor
  · change _ ∈ (S.iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q))
    rw [hcompact]
    refine ⟨KPStandardLocalRootLifts.integralA F q (-1) *
      KPStandardLocalRootLifts.integralW F q, ?_⟩
    rw [map_mul, (S.openCell S.polarization).weyl_eq]
    change _ = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) *
        KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q))
    rw [map_mul, KPStandardLocalRootLifts.W_eq_compact F ζ hζ q ht]
    have hA := KPStandardLocalRootLifts.A_eq_compact F ζ hζ q ht (-1)
    have hu : KPTameCompact.unitInclusion F q (-1) = -1 := by
      apply Units.ext
      rfl
    rw [hu] at hA
    rw [hA]
    rfl
  · intro x
    change _ ∈ (S.iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q))
    rw [hcompact]
    refine ⟨KPStandardLocalRootLifts.integralN F q x, ?_⟩
    rw [(S.openCell S.polarization).upper_eq]
    change _ = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) (x : LocalField F q))
    rw [KPStandardLocalRootLifts.N_eq_compact F ζ hζ q ht x]
    rfl

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end
