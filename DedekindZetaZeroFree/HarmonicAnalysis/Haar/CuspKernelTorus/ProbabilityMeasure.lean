module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingSheetEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberOutgoingAdapter

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "Cusps" => KPContFlatCuspIncomingEvaluation.Cusps
local notation "geometry" => KPContFlatCuspIncomingEvaluation.geometry
local notation "KernelTorus" => KPContFlatCuspIncomingEvaluation.KernelTorus

variable (a : Cusps F ζ hζ C R P H U)

theorem kernelTorus_borelSpace : BorelSpace (KernelTorus F ζ hζ C R P H U a) := by
  obtain ⟨hd, -⟩ := (geometry F ζ hζ C R P H U a).lattice
  let N : AddSubgroup (KPCuspCharts.Horizontal F) :=
    KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice
        (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a)
        (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a)
        (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a))
  have hle : N ≤ KPCuspCharts.translationLattice F
      (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a).L :=
    AddSubgroup.map_mono
      (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).kernel_le
  letI : DiscreteTopology (N : Set (KPCuspCharts.Horizontal F)) :=
    DiscreteTopology.of_subset hd hle
  haveI : IsClosed (N : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  haveI : N.Normal := AddSubgroup.normal_of_isAddCommutative N
  haveI : T3Space (KPCuspCharts.Horizontal F ⧸ N) := QuotientAddGroup.instT3Space N
  exact AddCosetSpace.borelSpace

def fiberMeasure : Measure (KernelTorus F ζ hζ C R P H U a) := by
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := kernelTorus_borelSpace F ζ hζ C R P H U a
  let μ : Measure (KernelTorus F ζ hζ C R P H U a) := Measure.addHaar
  exact (μ Set.univ)⁻¹ • μ

theorem fiber_probability : IsProbabilityMeasure (fiberMeasure F ζ hζ C R P H U a) := by
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := kernelTorus_borelSpace F ζ hζ C R P H U a
  unfold fiberMeasure
  exact MeasureTheory.isProbabilityMeasureSMul

end DedekindZetaZeroFree.KPContActualChamberOutgoingAdapter

end
