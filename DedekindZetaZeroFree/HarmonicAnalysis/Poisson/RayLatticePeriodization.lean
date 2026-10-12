module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Γ : Submodule ℤ E) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

variable (ν : Measure E) [ν.IsAddHaarMeasure]
    (D : Set E) (hD : MeasurableSet D)
    (hfund : IsAddFundamentalDomain Γ D ν)

include hD hfund

instance latticeVAddInvariant : VAddInvariantMeasure Γ E ν :=
  ⟨fun γ s _ => measure_preimage_add ν (γ : E) s⟩

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
