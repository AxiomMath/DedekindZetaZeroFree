module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.SphericalPairing

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
open NativeComplexHCOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def compactBoundary (ν : Measure ComplexSU2) (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) : ℂ :=
  ∫ k, f (complexSU2Embedding k) * star (g (complexSU2Embedding k)) ∂ν

theorem compactBoundary_eq_star (ν : Measure ComplexSU2) (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    compactBoundary ν s f g = star (compactPairing ν s f g) := by
  simp only [compactBoundary,compactPairing,Complex.star_def,← integral_conj,map_mul,starRingEnd_self_apply]

theorem compactBoundary_lie_adjoint (ν : Measure ComplexSU2) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    compactBoundary ν s (derivative s X f) g +
      compactBoundary ν s f (derivative (-s) X g) = 0 := by
  have h := congrArg star (compact_pairing_lie_adjoint ν s X f g)
  simpa only [compactBoundary_eq_star,star_add,star_zero] using h

def matrixWord (s : ℝ) : List (Matrix (Fin 2) (Fin 2) ℂ) → PrincipalSeries s → PrincipalSeries s
  | [],f => f
  | X::w,f => derivative s X (matrixWord s w f)

theorem matrixWord_append (s : ℝ) (w u : List (Matrix (Fin 2) (Fin 2) ℂ))
    (f : PrincipalSeries s) : matrixWord s (w++u) f = matrixWord s w (matrixWord s u f) := by
  induction w with
  | nil => rfl
  | cons X w hw => simpa only [List.cons_append,matrixWord,hw]

theorem compactBoundary_word_adjoint (ν : Measure ComplexSU2) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (s : ℝ) (w : List (Matrix (Fin 2) (Fin 2) ℂ))
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    compactBoundary ν s (matrixWord s w f) g = (-1 : ℂ)^w.length *
      compactBoundary ν s f (matrixWord (-s) w.reverse g) := by
  induction w generalizing f g with
  | nil => simp [matrixWord]
  | cons X w hw =>
    have he := compactBoundary_lie_adjoint ν s X (matrixWord s w f) g
    rw [hw] at he
    rw [matrixWord,List.reverse_cons,matrixWord_append,List.length_cons,pow_succ]
    change compactBoundary ν s (derivative s X (matrixWord s w f)) g =
      (-1 : ℂ)^w.length * (-1) * compactBoundary ν s f (matrixWord (-s) w.reverse (derivative (-s) X g))
    linear_combination he

end DedekindZetaZeroFree.CurrentComplexBoundary

end
