module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.NormalizedLevelNumerator
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.GlobalContinuationFromLevelIntegrals
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ContinuedOperatorFamilies

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneForwardTestVector

open scoped Valued NumberField
open Classical MeasureTheory ValuativeRel KPLocalPrincipalSeries KPRankOneRootParameter
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
open NumberField IsDedekindDomain KPLocalExceptionalConstruction

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

theorem r_zero : r K 0 = 1 := by simp [r]

theorem t_zero : t K 0 = (residueCardinality K : ℂ)⁻¹ := by
  simp [t, r_zero]

end
end DedekindZetaZeroFree.KPRankOneForwardTestVector
