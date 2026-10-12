module

public import Mathlib.RingTheory.Length

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps

theorem length_le_of_strictMono_submodules
    {R S M N : Type*} [Ring R] [Ring S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : Submodule R M → Submodule S N) (hf : StrictMono f) :
    Module.length R M ≤ Module.length S N := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_strictMono f hf

end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps
