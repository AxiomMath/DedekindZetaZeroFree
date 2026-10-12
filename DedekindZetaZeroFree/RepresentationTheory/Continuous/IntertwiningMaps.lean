module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/Intertwining.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

namespace ContRepresentation

section Intertwiners

universe u v w x y

variable {𝕜 : Type u} {G : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  {V : Type w} {W : Type x} {U : Type y}
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W]
  [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul 𝕜 U]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}
  {τ : ContRepresentation 𝕜 G U}

omit [CompleteSpace 𝕜] [T2Space V] [FiniteDimensional 𝕜 V] [ContinuousSMul 𝕜 V]
  [ContinuousSMul 𝕜 W] in

@[simp]
theorem _root_.ContIntertwiningMap.toIntertwiningMap_apply (f : ContIntertwiningMap π ρ) (v : V) :
    f.toIntertwiningMap v = f v :=
  (rfl)

end Intertwiners

end ContRepresentation
