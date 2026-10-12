module

public import DedekindZetaZeroFree.Adeles.Lattices.TraceCovolumeHaarCancellation
public import DedekindZetaZeroFree.Adeles.Quotients.CompactOpenLevelTori

@[expose] public section

namespace DedekindZetaZeroFree.QuotientProbability
noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

local instance quotientProbability_finiteMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance quotientProbability_adeleMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
local instance quotientProbability_quotientMeasurable (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := borel _

def finiteLevelInfiniteHaar (F : Type) [Field F] [NumberField F] :
    Measure (mixedEmbedding.mixedSpace F) :=
  ENNReal.ofReal (PoissonArch.haarScalar F) • volume

def additiveProductHaar (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) : Measure (AdeleRing (𝓞 F) F) :=
  Measure.map
    (fun x : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) :
        AdeleRing (𝓞 F) F))
    ((finiteLevelInfiniteHaar F).prod μf)

def additiveQuotientMeasureFromDomain (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) (Ω : Set (AdeleRing (𝓞 F) F)) :
    Measure (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) :=
  Measure.map (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
    ((additiveProductHaar F μf).restrict Ω)

def finiteLevelProductDomain {F : Type} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (D : Set (mixedEmbedding.mixedSpace F)) : Set (AdeleRing (𝓞 F) F) :=
  {a | InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 ∈ D ∧ a.2 ∈ K}

end
end DedekindZetaZeroFree.QuotientProbability
