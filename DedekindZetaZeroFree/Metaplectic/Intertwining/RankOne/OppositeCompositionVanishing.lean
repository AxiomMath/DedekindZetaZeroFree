module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellTestVector
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ConditionalCubicResidueReduction

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneOppositeZero

open scoped Valued
open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPRankOneRootParameter
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
open KPRankOneForwardTestVector

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

set_option backward.isDefEq.respectTransparency false in

theorem both_level_compositions_zero (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (J : CompactOpenLevel G)
    (hJ : (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup)
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation K).integer : Set K) = 1)
    (ζ : (valuation K).integer) (hζ : IsPrimitiveRoot ζ 3)
    (hResidue : KPRankOneCubicResidueReduction.RegularPointResidueOutput K A P I μ)
    (p : LevelLaurentOperator K A P I J .plus)
    (pRev : LevelLaurentOperator K A P I J .minus)
    (hp : IsLevelNumerator K A P I J μ .plus p)
    (hpRev : IsLevelNumerator K A P I J μ .minus pRev) :
    (continuedLevel K A P I J .minus pRev 0).comp
      (continuedLevel K A P I J .plus p 0) = 0 ∧
    (continuedLevel K A P I J .plus p 0).comp
      (continuedLevel K A P I J .minus pRev 0) = 0 := by
  have hq : (residueCardinality K : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos (α := 𝓀[K]) |>.ne'
  have hq1 : (residueCardinality K : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_gt (Finite.one_lt_card (α := 𝓀[K])))
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (t K 0) (by norm_num : 0 < 3)
  have hz0 : z ≠ 0 := by
    intro h
    apply (inv_ne_zero hq)
    simpa [h, t_zero] using hz.symm
  have hr := hResidue 0 z hz0 hz
      (denominator_ne_zero_at_zero K .plus) (denominator_ne_zero_at_zero K .minus)
      J hJ p pRev hp hpRev
  have hζK : IsPrimitiveRoot (ζ : K) 3 := hζ.map_of_injective
    (Subring.subtype_injective (valuation K).integer)
  have hc := KPRankoneCubicScalarSum.finiteScalar_eq K (ζ : K) hζK
    (KPRankOneCubicResidueReduction.integerMass K μ) (KPCubicHaar.abs K (3 : K))
    z (t K 0) hz0 hz (by simp [t_zero, inv_eq_one, hq1])
  have hc0 : KPRankOneCubicResidueReduction.residueScalar K μ z = 0 := by
    change KPRankoneCubicScalarSum.finiteScalar K _ _ z = 0
    rw [hc]
    change (_ : ℂ) * ((1 - (residueCardinality K : ℂ)⁻¹ * t K 0) *
      (1 - (residueCardinality K : ℂ)⁻¹ * (t K 0)⁻¹) / _) = 0
    simp [t_zero, hq]
  constructor
  · rw [hr.1, hc0]
    exact zero_smul ℂ _
  · rw [hr.2, hc0]
    exact zero_smul ℂ _

end
end DedekindZetaZeroFree.KPRankOneOppositeZero
