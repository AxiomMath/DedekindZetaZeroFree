module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RationalCompactPicture
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubicCharacterScalarSum

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneCubicResidueReduction

open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneRootParameter KPRankOneShellContinuation KPRankOneGenericComposition
open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

def integerMass (dx : Measure K) : ℝ :=
  (dx ((valuation K).integer : Set K)).toReal

def rationalResidueScalar (dx : Measure K) : RatFunc ℂ :=
  RatFunc.C (((integerMass K dx ^ 2 * KPCubicHaar.abs K (3 : K) : ℝ) : ℂ) / 9) *
    (∑ᶠ ξ : CubicUnitCharacters.Character K,
      ∑ᶠ ζ : CubicCharacters.Mu3,
        KPRankoneCubicScalarSum.betaFactor K ξ
          (RatFunc.C ((ζ : ℂˣ) : ℂ) * RatFunc.X ^ 2))

def residueScalar (dx : Measure K) (z : ℂ) : ℂ :=
  KPRankoneCubicScalarSum.finiteScalar K (integerMass K dx)
    (KPCubicHaar.abs K (3 : K)) z

def RegularPointResidueOutput
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (dx : Measure K) : Prop :=
  ∀ (s z : ℂ), z ≠ 0 → z ^ 3 = t K s →
    denominator K .plus s ≠ 0 → denominator K .minus s ≠ 0 →
    ∀ (J : CompactOpenLevel G),
      (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup →
      ∀ (p : LevelLaurentOperator K A P I J .plus)
        (pRev : LevelLaurentOperator K A P I J .minus),
      IsLevelNumerator K A P I J dx .plus p →
      IsLevelNumerator K A P I J dx .minus pRev →
      (continuedLevel K A P I J .minus pRev s).comp
        (continuedLevel K A P I J .plus p s) = residueScalar K dx z • LinearMap.id ∧
      (continuedLevel K A P I J .plus p s).comp
        (continuedLevel K A P I J .minus pRev s) = residueScalar K dx z • LinearMap.id

end
end DedekindZetaZeroFree.KPRankOneCubicResidueReduction
