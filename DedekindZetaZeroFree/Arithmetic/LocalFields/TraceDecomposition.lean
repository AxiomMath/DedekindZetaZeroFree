module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.CompletionTraceComparison
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ArchimedeanTraceDecomposition
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CompletionTraceDecomposition

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain
open scoped NumberField

namespace PlaceTraceAdapter

theorem prime_eq_of_above (F : Type) [Field F] [NumberField F]
    (p : Nat.Primes)
    (v : FinitePlacesAbove ℚ F (Rat.HeightOneSpectrum.primesEquiv.symm p)) :
    prime F v.val = p := by
  change Rat.HeightOneSpectrum.primesEquiv (finitePlaceBelow (K := ℚ) v.val) = p
  rw [v.property]
  exact Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p

def traceAbove (F : Type) [Field F] [NumberField F] (p : Nat.Primes)
    (v : FinitePlacesAbove ℚ F (Rat.HeightOneSpectrum.primesEquiv.symm p))
    (x : v.val.adicCompletion F) : ℚ_[p] :=
  cast (congrArg (fun q : Nat.Primes => ℚ_[q]) (prime_eq_of_above F p v))
    (trace F v.val x)

private theorem trace_cast_eq (F : Type) [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 ℚ)) (p : Nat.Primes)
    (hp : Rat.HeightOneSpectrum.primesEquiv w = p)
    (v : FinitePlacesAbove ℚ F w) (t : F) :
    letI : Algebra (w.adicCompletion ℚ) (v.val.adicCompletion F) :=
      (finitePlaceAdicCompletionMap ℚ F w v).toAlgebra
    cast (congrArg (fun q : Nat.Primes => ℚ_[q])
      (show prime F v.val = p from by
        change Rat.HeightOneSpectrum.primesEquiv (finitePlaceBelow v.val) = p
        rw [v.property, hp]))
      (trace F v.val (algebraMap F (v.val.adicCompletion F) t)) =
      cast (congrArg (fun q : Nat.Primes => ℚ_[q]) hp)
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv w
        (Algebra.trace (w.adicCompletion ℚ) (v.val.adicCompletion F)
          (algebraMap F (v.val.adicCompletion F) t))) := by
  rcases v with ⟨v, hv⟩
  dsimp only
  rw [trace_algebraMap]
  dsimp only [rationalPlace, localTrace, rationalCompletionEquiv, completionMap]
  cases hv
  subst p
  rfl

end PlaceTraceAdapter

private theorem trace_eq_sum_transported (F : Type) [Field F] [NumberField F]
    (t : F) (w : HeightOneSpectrum (𝓞 ℚ)) (p : Nat.Primes)
    (hp : Rat.HeightOneSpectrum.primesEquiv w = p) :
    letI : Fintype (FinitePlacesAbove ℚ F w) := finitePlacesAboveFintype ℚ F w
    letI : ∀ v : FinitePlacesAbove ℚ F w,
        Algebra (w.adicCompletion ℚ) (v.val.adicCompletion F) :=
      fun v => (finitePlaceAdicCompletionMap ℚ F w v).toAlgebra
    algebraMap ℚ ℚ_[p] (Algebra.trace ℚ F t) =
      ∑ v : FinitePlacesAbove ℚ F w,
        cast (congrArg (fun q : Nat.Primes => ℚ_[q]) hp)
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv w
            (Algebra.trace (w.adicCompletion ℚ) (v.val.adicCompletion F)
              (algebraMap F (v.val.adicCompletion F) t))) := by
  classical
  subst p
  letI : Fintype (FinitePlacesAbove ℚ F w) := finitePlacesAboveFintype ℚ F w
  letI : ∀ v : FinitePlacesAbove ℚ F w,
      Algebra (w.adicCompletion ℚ) (v.val.adicCompletion F) :=
    fun v => (finitePlaceAdicCompletionMap ℚ F w v).toAlgebra
  simp only [cast_eq]
  rw [← map_sum]
  rw [← adicCompletion_trace_eq_sum ℚ F w t]
  letI : Algebra ℚ (w.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ w
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv w).commutes _ |>.symm

theorem trace_eq_sum_localTrace_padic (F : Type) [Field F] [NumberField F]
    (t : F) (p : Nat.Primes) :
    letI : Fintype (FinitePlacesAbove ℚ F (Rat.HeightOneSpectrum.primesEquiv.symm p)) :=
      finitePlacesAboveRationalPrimeFintype F p
    algebraMap ℚ ℚ_[p] (Algebra.trace ℚ F t) =
      ∑ v : FinitePlacesAbove ℚ F (Rat.HeightOneSpectrum.primesEquiv.symm p),
        PlaceTraceAdapter.traceAbove F p v
          (algebraMap F (v.val.adicCompletion F) t) := by
  classical
  letI : Fintype (FinitePlacesAbove ℚ F (Rat.HeightOneSpectrum.primesEquiv.symm p)) :=
    finitePlacesAboveRationalPrimeFintype F p
  rw [trace_eq_sum_transported F t (Rat.HeightOneSpectrum.primesEquiv.symm p) p
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact (PlaceTraceAdapter.trace_cast_eq F _ p
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p) v t).symm

theorem trace_eq_sum_localTrace_infinite (F : Type) [Field F] [NumberField F]
    (t : F) :
    (Algebra.trace ℚ F t : ℝ) =
      ∑ v : InfinitePlace F, archTrace v (algebraMap F v.Completion t) := by
  exact trace_eq_sum_archTrace t

end DedekindZetaZeroFree

end
