module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows

@[expose] public section

noncomputable section
open scoped Classical Topology BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev MatrixLetter (ι : Type) := ι × Matrix (Fin 2) (Fin 2) ℂ

def slotWords (i : ι) : List (MatrixLetter ι) → List (Matrix (Fin 2) (Fin 2) ℂ)
  | [] => []
  | b::w => if b.1 = i then b.2 :: slotWords i w else slotWords i w

def tupleWord : List (MatrixLetter ι) → ((ι → ComplexGL2) → ℂ) → (ι → ComplexGL2) → ℂ
  | [],f => f
  | b::w,f => fun a => deriv (fun t : ℝ => tupleWord w f
      (Function.update a b.1 (a b.1 * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • b.2)))) 0

end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
