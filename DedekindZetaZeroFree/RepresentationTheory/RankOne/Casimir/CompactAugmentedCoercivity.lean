module

public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped BigOperators
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.FullSixCoercivity

 def nativeForm (a : Fin 6 → ℂ) : ℝ :=
  (‖a 0‖ ^ 2 - ‖a 1‖ ^ 2 +
    4 * ((star (a 2) * a 4).re - (star (a 3) * a 5).re)) / 4

 def compactTensor (q : Fin 6 → Fin 6 → ℂ) : ℂ :=
  -(q 1 1 + (q 2 2 - q 2 4 - q 4 2 + q 4 4) +
    (q 3 3 + q 3 5 + q 5 3 + q 5 5))

end DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.FullSixCoercivity

end
