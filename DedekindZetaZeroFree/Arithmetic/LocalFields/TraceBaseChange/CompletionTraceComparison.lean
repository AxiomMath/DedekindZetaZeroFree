module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.IntegralCompletionTrace

@[expose] public section

noncomputable section
open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

namespace DedekindZetaZeroFree.PlaceTraceAdapter

variable (F : Type) [Field F] [NumberField F]

def rationalPlace (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 ℚ) :=
  finitePlaceBelow (K := ℚ) v

def prime (v : HeightOneSpectrum (𝓞 F)) : Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv (rationalPlace F v)

instance primeFact (v : HeightOneSpectrum (𝓞 F)) : Fact (prime F v).1.Prime :=
  ⟨(prime F v).2⟩

def completionMap (v : HeightOneSpectrum (𝓞 F)) :
    (rationalPlace F v).adicCompletion ℚ →+* v.adicCompletion F :=
  finitePlaceAdicCompletionMap ℚ F (rationalPlace F v) ⟨v, rfl⟩

def rationalCompletionEquiv (v : HeightOneSpectrum (𝓞 F)) :
    (rationalPlace F v).adicCompletion ℚ ≃+* ℚ_[prime F v] := by
  letI : Algebra ℚ ((rationalPlace F v).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ (rationalPlace F v)
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPlace F v)).toAlgEquiv.toRingEquiv

def padicMap (v : HeightOneSpectrum (𝓞 F)) :
    ℚ_[prime F v] →+* v.adicCompletion F :=
  (completionMap F v).comp
    (rationalCompletionEquiv F v).symm.toRingHom

instance padicAlgebra (v : HeightOneSpectrum (𝓞 F)) :
    Algebra ℚ_[prime F v] (v.adicCompletion F) :=
  (padicMap F v).toAlgebra

instance padicFiniteDimensional (v : HeightOneSpectrum (𝓞 F)) :
    FiniteDimensional ℚ_[prime F v] (v.adicCompletion F) := by
  let w := rationalPlace F v
  letI : Algebra (w.adicCompletion ℚ) (v.adicCompletion F) :=
    (completionMap F v).toAlgebra
  letI : Module.Finite (w.adicCompletion ℚ) (v.adicCompletion F) :=
    finitePlaceAdicCompletionMap_moduleFinite ℚ F w ⟨v, rfl⟩
  letI : Algebra (w.adicCompletion ℚ) ℚ_[prime F v] :=
    (rationalCompletionEquiv F v).toRingHom.toAlgebra
  letI : IsScalarTower (w.adicCompletion ℚ) ℚ_[prime F v] (v.adicCompletion F) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change completionMap F v x =
      completionMap F v ((rationalCompletionEquiv F v).symm
        ((rationalCompletionEquiv F v) x))
    simp
  exact Module.Finite.of_restrictScalars_finite (w.adicCompletion ℚ) ℚ_[prime F v]
    (v.adicCompletion F)

def trace (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F →ₗ[ℚ_[prime F v]] ℚ_[prime F v] :=
  Algebra.trace ℚ_[prime F v] (v.adicCompletion F)

def localTrace (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    (rationalPlace F v).adicCompletion ℚ := by
  letI : Algebra ((rationalPlace F v).adicCompletion ℚ) (v.adicCompletion F) :=
    (completionMap F v).toAlgebra
  exact Algebra.trace ((rationalPlace F v).adicCompletion ℚ) (v.adicCompletion F)
    (algebraMap F (v.adicCompletion F) t)

theorem trace_algebraMap (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    trace F v (algebraMap F (v.adicCompletion F) t) =
      rationalCompletionEquiv F v (localTrace F v t) := by
  letI : Algebra ((rationalPlace F v).adicCompletion ℚ) (v.adicCompletion F) :=
    (completionMap F v).toAlgebra
  exact (Algebra.trace_eq_of_ringEquiv (rationalCompletionEquiv F v) (by
    apply RingHom.ext
    intro x
    change completionMap F v ((rationalCompletionEquiv F v).symm
      ((rationalCompletionEquiv F v) x)) = completionMap F v x
    simp) (algebraMap F (v.adicCompletion F) t)).symm

theorem trace_mem_padicIntegers (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    trace F v x ∈ Set.range (fun z : ℤ_[prime F v] => (z : ℚ_[prime F v])) := by
  letI : Algebra ((rationalPlace F v).adicCompletion ℚ) (v.adicCompletion F) :=
    (completionMap F v).toAlgebra
  have hxtrace := adic_trace_mem_integers (rationalPlace F v) ⟨v, rfl⟩ x hx
  refine ⟨Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
    (rationalPlace F v) ⟨_, hxtrace⟩, ?_⟩
  change rationalCompletionEquiv F v
    (Algebra.trace ((rationalPlace F v).adicCompletion ℚ) (v.adicCompletion F) x) =
      trace F v x
  exact Algebra.trace_eq_of_ringEquiv (rationalCompletionEquiv F v) (by
    apply RingHom.ext
    intro z
    change completionMap F v ((rationalCompletionEquiv F v).symm
      ((rationalCompletionEquiv F v) z)) = completionMap F v z
    simp) x

end DedekindZetaZeroFree.PlaceTraceAdapter

end
