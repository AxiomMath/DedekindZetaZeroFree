module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.StandardIntegralAndLevelContinuation

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneGenericComposition

open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneRootParameter KPRankOneShellContinuation
open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

abbrev rationalLevel (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (J : CompactOpenLevel G) (ε : Sign) :=
  RatFunc ℂ ⊗[ℂ] compactLevel A P I ε J

def rationalDenominator (ε : Sign) (v : RatFunc ℂ) : RatFunc ℂ :=
  if ε = .plus then 1 - RatFunc.C (residueCardinality K : ℂ)⁻¹ * v ^ 6
  else 1 - RatFunc.C (residueCardinality K : ℂ) * v⁻¹ ^ 6

def rationalStandard
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J : CompactOpenLevel G) (ε : Sign)
    (p : LevelLaurentOperator K A P I J ε) (v : RatFunc ℂ) :
    rationalLevel K A P I J (sourceSign ε) →ₗ[RatFunc ℂ]
      rationalLevel K A P I J (targetSign ε) :=
  (rationalDenominator K ε v)⁻¹ •
    p.sum (fun n M =>
      ((if ε = .plus then v else v⁻¹) ^ n) • LinearMap.baseChange (RatFunc ℂ) M)

end
end DedekindZetaZeroFree.KPRankOneGenericComposition
