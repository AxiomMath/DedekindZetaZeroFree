module

public import Mathlib.Algebra.Module.Torsion.Basic

/-
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RingTheory/SimpleModule/Basic.lean`. Original Apache-2.0 copyright and authors retained.
-/

@[expose] public section

namespace DedekindZetaZeroFree.TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

instance IsSemisimpleModule.prod [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by

  have hsup := _root_.IsSemisimpleModule.sup
    (_root_.IsSemisimpleModule.range (LinearMap.inl R M N))
    (_root_.IsSemisimpleModule.range (LinearMap.inr R M N))
  rw [LinearMap.sup_range_inl_inr] at hsup
  exact .congr Submodule.topEquiv.symm

end DedekindZetaZeroFree.TauCeti
