module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspKernelTorus.ProbabilityMeasure
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.HorizontalTorusHaarPushforward

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)

theorem actual_fiberMeasure_isAddHaarMeasure :
    (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a).IsAddHaarMeasure := by
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
  unfold KPContActualChamberOutgoingAdapter.fiberMeasure
  dsimp only
  apply Measure.IsAddHaarMeasure.smul
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · apply ENNReal.inv_ne_top.mpr
    exact (isOpen_univ.measure_pos (μ := Measure.addHaar) Set.univ_nonempty).ne'

theorem finiteLevelLattice_le_horizontal_of_rational_kernel
    (K : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
    (L : AddSubgroup F)
    (hr : ∀ r : F, algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) r ∈ K → r ∈ L) :
    (finiteLevelLattice K).toAddSubgroup ≤
      (KPCuspCharts.translationLattice F L).comap (mixedToHorizontal F) := by
  intro x hx
  obtain ⟨r, hrK, rfl⟩ := (mem_finiteLevelLattice_iff K x).mp hx
  change mixedToHorizontal F (mixedEmbedding F r) ∈ KPCuspCharts.translationLattice F L
  rw [mixedToHorizontal_embedding]
  exact AddSubgroup.mem_map.mpr ⟨r, hr r hrK, rfl⟩

theorem actual_kernelTorus_probabilityHaar_transport
    (K : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
    (hc : IsCompact (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
    (ho : IsOpen (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
    (h : (finiteLevelLattice K).toAddSubgroup ≤
      (KPCuspCharts.translationLattice F
        (KPCuspGenuineMonodromy.kernelLattice
          (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a)
          (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a)
          (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a))).comap (mixedToHorizontal F))
    (ν : Measure (mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :
    Measure.map (mixedHorizontalQuotientMap F K _ h) ν =
      KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
  letI := finiteLevelLattice_discrete K hc ho
  letI : DiscreteTopology (finiteLevelLattice K).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (finiteLevelLattice K))
  letI : IsClosed ((finiteLevelLattice K).toAddSubgroup : Set (mixedEmbedding.mixedSpace F)) :=
    AddSubgroup.isClosed_of_discrete
  letI : BorelSpace (mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup) :=
    AddCosetSpace.borelSpace
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
  letI := actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  exact mixedHorizontalQuotientMap_probabilityHaar F K _ h ν _

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
