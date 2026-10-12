module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellData

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.InfinityTailNumeratorSteps

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain ValuativeRel
open KPRankOneOpenCellKernel KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]

def infinityBlock (N n : ℕ) : Set (LocalField F q)ˣ :=
  {v | (N : ℤ) + 3 * (n : ℤ) < valuationIndex F q v ∧
    valuationIndex F q v ≤ (N : ℤ) + 3 * ((n : ℤ) + 1)}

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.InfinityTailNumeratorSteps
