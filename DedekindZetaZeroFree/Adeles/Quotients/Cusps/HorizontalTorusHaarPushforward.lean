module

public import DedekindZetaZeroFree.Adeles.Lattices.Cusps.ParabolicTranslations
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdditiveAdelicQuotientDomains

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
variable (F : Type) [Field F] [NumberField F]

def mixedToHorizontal : mixedEmbedding.mixedSpace F →+ KPCuspCharts.Horizontal F where
  toFun x := fun i => x.2 ((Fintype.equivFin {w : InfinitePlace F // w.IsComplex}).symm i)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem mixedToHorizontal_embedding (x : F) :
    mixedToHorizontal F (mixedEmbedding F x) = KPCuspCharts.embedding F x := rfl

theorem mixedToHorizontal_continuous : Continuous (mixedToHorizontal F) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : mixedEmbedding.mixedSpace F => x.2 _)
  exact (continuous_apply _).comp continuous_snd

theorem mixedToHorizontal_surjective : Function.Surjective (mixedToHorizontal F) := by
  intro y
  refine ⟨(fun _ => 0, fun w => y ((Fintype.equivFin {w : InfinitePlace F // w.IsComplex}) w)), ?_⟩
  ext i
  simp [mixedToHorizontal]

variable (K : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
variable (L : AddSubgroup F)
variable (h : (finiteLevelLattice K).toAddSubgroup ≤
  (KPCuspCharts.translationLattice F L).comap (mixedToHorizontal F))

def mixedHorizontalQuotientMap :
    mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup →+
      KPCuspCharts.Torus F L :=
  QuotientAddGroup.map _ _ (mixedToHorizontal F) h

@[simp] theorem mixedHorizontalQuotientMap_mk (x : mixedEmbedding.mixedSpace F) :
    mixedHorizontalQuotientMap F K L h (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (mixedToHorizontal F x) := rfl

theorem mixedHorizontalQuotientMap_continuous :
    Continuous (mixedHorizontalQuotientMap F K L h) := by
  apply (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (mixedToHorizontal_continuous F)

theorem mixedHorizontalQuotientMap_surjective :
    Function.Surjective (mixedHorizontalQuotientMap F K L h) := by
  apply QuotientAddGroup.map_surjective_of_surjective
  exact QuotientAddGroup.mk_surjective.comp (mixedToHorizontal_surjective F)

theorem mixedHorizontalQuotientMap_probabilityHaar
    [BorelSpace (mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup)]
    [BorelSpace (KPCuspCharts.Torus F L)]
    [LocallyCompactSpace (KPCuspCharts.Torus F L)]
    (ν : Measure (mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (μ : Measure (KPCuspCharts.Torus F L)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] :
    Measure.map (mixedHorizontalQuotientMap F K L h) ν = μ := by
  have hc := mixedHorizontalQuotientMap_continuous F K L h
  letI : (Measure.map (mixedHorizontalQuotientMap F K L h) ν).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure ν _ hc
      (mixedHorizontalQuotientMap_surjective F K L h)
  letI : IsProbabilityMeasure (Measure.map (mixedHorizontalQuotientMap F K L h) ν) :=
    (Measure.isProbabilityMeasure_map_iff hc.measurable.aemeasurable).mpr inferInstance
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
