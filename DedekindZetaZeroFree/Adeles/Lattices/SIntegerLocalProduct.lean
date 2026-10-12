module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.SInteger

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain

abbrev SLocalProduct (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  InfiniteAdeleRing F × ((v : S) → v.1.adicCompletion F)

def sLocalDiagonal (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    F →+* SLocalProduct F S :=
  algebraMap F (SLocalProduct F S)

@[simp] theorem sLocalDiagonal_infinite (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (t : F) (v : InfinitePlace F) :
    (sLocalDiagonal F S t).1 v = algebraMap F v.Completion t := by
  simp only [sLocalDiagonal]
  exact InfiniteAdeleRing.algebraMap_apply F t v

@[simp] theorem sLocalDiagonal_finite (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (t : F) (v : S) :
    (sLocalDiagonal F S t).2 v = algebraMap F (v.1.adicCompletion F) t := by
  rfl

abbrev sIntegerRing (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) : Subring F :=
  ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F).toSubring

private theorem valued_algebraMap_adicCompletion (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (t : F) :
    Valued.v (algebraMap F (v.adicCompletion F) t) = v.valuation F t := by
  rw [show algebraMap F (v.adicCompletion F) t = (t : v.adicCompletion F) from rfl]
  exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe F v t

private theorem mem_sIntegerRing_iff_valuation (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (t : F) :
    t ∈ sIntegerRing F S ↔
      ∀ v : HeightOneSpectrum (RingOfIntegers F), v ∉ S → v.valuation F t ≤ 1 := by
  rw [sIntegerRing, Set.integer_eq]
  simp only [Subring.mem_iInf, ValuationSubring.mem_toSubring, Valuation.mem_valuationSubring_iff,
    Finset.mem_coe]

theorem mem_sIntegerRing_iff (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (t : F) :
    t ∈ sIntegerRing F S ↔
      ∀ v : HeightOneSpectrum (RingOfIntegers F), v ∉ S →
        algebraMap F (v.adicCompletion F) t ∈ v.adicCompletionIntegers F := by
  rw [mem_sIntegerRing_iff_valuation]
  constructor
  · intro h v hv
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      valued_algebraMap_adicCompletion]
    exact h v hv
  · intro h v hv
    have := h v hv
    rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      valued_algebraMap_adicCompletion] at this

def sIntegerDiagonal (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    sIntegerRing F S →+* SLocalProduct F S :=
  (sLocalDiagonal F S).comp (sIntegerRing F S).subtype

@[simp] theorem sIntegerDiagonal_apply (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (t : sIntegerRing F S) :
    sIntegerDiagonal F S t = sLocalDiagonal F S (t : F) := by
  rfl

end DedekindZetaZeroFree

end
