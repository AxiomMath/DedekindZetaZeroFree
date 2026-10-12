module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
set_option linter.style.haveILetI false
namespace DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration

theorem finite_stage_intersection_closed
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
    (A T : Submodule ℂ V) [FiniteDimensional ℂ T]
    (S : Submodule ℂ V) (hAT : A ≤ T) :
    IsClosed ((A ⊓ S : Submodule ℂ V) : Set V) := by
  haveI : FiniteDimensional ℂ (A ⊓ S : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le (le_trans inf_le_left hAT)
  exact Submodule.closed_of_finiteDimensional (A ⊓ S)

end DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration

end
