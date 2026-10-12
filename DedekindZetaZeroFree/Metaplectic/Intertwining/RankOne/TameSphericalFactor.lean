module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.UnramifiedSphericalImage
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RootParameterCompactPicture

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneTameSphericalFactor

open scoped Valued
open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPRankOneRootParameter
open KPLocalStoneVonNeumann KPLocalGoodSphericalImage

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

def haarMass (μ : Measure K) : ℝ :=
  (μ ((valuation K).integer : Set K)).toReal

def forwardFactorInRoot (μ : Measure K) (z : ℂ) : ℂ :=
  (haarMass K μ : ℂ) *
    (1 - (residueCardinality K : ℂ)⁻¹ *
      ((residueCardinality K : ℂ)⁻¹ * z ^ 6)) /
    (1 - (residueCardinality K : ℂ)⁻¹ * z ^ 6)

def forwardFactor (μ : Measure K) (s : ℂ) : ℂ :=
  forwardFactorInRoot K μ (r K s)

def IsSphericalVector
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign)
    (φ : compactPicture A P I ε) : Prop :=
  (∀ s : ℂ,
    ((compactTrivialization A P I ε s φ).val 1).val 1 = 1) ∧
  ∀ (s : ℂ) (k : I.compact.toOpenSubgroup),
    principalSeries A P ε s (k : G)
      (compactTrivialization A P I ε s φ) =
        compactTrivialization A P I ε s φ

end
end DedekindZetaZeroFree.KPRankOneTameSphericalFactor
