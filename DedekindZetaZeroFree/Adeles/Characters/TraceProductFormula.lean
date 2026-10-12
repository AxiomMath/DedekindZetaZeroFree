module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacters.LocalTraceCharacter
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceDecomposition
public import DedekindZetaZeroFree.Adeles.Characters.RationalPadicProductFormula

@[expose] public section

noncomputable section

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

private theorem finiteCharacter_support (a : FiniteAdeleRing (𝓞 F) F) :
    Function.HasFiniteMulSupport (fun v => localFiniteCharacter F v (a v)) := by
  change {v | ¬localFiniteCharacter F v (a v) = 1}.Finite
  rw [← Filter.eventually_cofinite]
  filter_upwards [a.cofinite_mem_adicCompletionIntegers] with v hv
  exact localFiniteCharacter_eq_one_of_mem_integers F v (a v) hv

theorem localFiniteCharacter_diagonal_hasFiniteMulSupport (t : F) :
    Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) =>
        localFiniteCharacter F v (algebraMap F (v.adicCompletion F) t)) := by
  exact finiteCharacter_support F (algebraMap F (FiniteAdeleRing (𝓞 F) F) t)

theorem localFiniteCharacter_adele_hasFiniteMulSupport
    (x : AdeleRing (𝓞 F) F) :
    Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) => localFiniteCharacter F v (x.2 v)) := by
  exact finiteCharacter_support F x.2

private theorem character_sum {A ι : Type*} [AddCommMonoid A]
    (χ : AddChar A Circle) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, χ.map_add_eq_mul, ih]

private theorem character_cast (p q : Nat.Primes) (h : p = q) (x : ℚ_[p]) :
    rationalPadicCharacter p x = rationalPadicCharacter q
      (cast (congrArg (fun r : Nat.Primes => ℚ_[r]) h) x) := by
  subst q
  rfl

private theorem fiber_character_product (t : F) (p : Nat.Primes) :
    letI := finitePlacesAboveRationalPrimeFintype F p
    (∏ v : FinitePlacesAbove ℚ F (Rat.HeightOneSpectrum.primesEquiv.symm p),
      localFiniteCharacter F v.val (algebraMap F (v.val.adicCompletion F) t)) =
        rationalPadicCharacter p (algebraMap ℚ ℚ_[p] (Algebra.trace ℚ F t)) := by
  letI := finitePlacesAboveRationalPrimeFintype F p
  rw [trace_eq_sum_localTrace_padic F t p, character_sum]
  apply Finset.prod_congr rfl
  intro v hv
  rw [localFiniteCharacter_apply]
  exact character_cast _ p (PlaceTraceAdapter.prime_eq_of_above F p v) _

private theorem finite_character_product (t : F) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      localFiniteCharacter F v (algebraMap F (v.adicCompletion F) t)) =
    (∏ᶠ p : Nat.Primes,
      rationalPadicCharacter p (algebraMap ℚ ℚ_[p] (Algebra.trace ℚ F t))) := by
  classical
  let g := fun v : HeightOneSpectrum (𝓞 F) =>
    localFiniteCharacter F v (algebraMap F (v.adicCompletion F) t)
  have hg := localFiniteCharacter_diagonal_hasFiniteMulSupport F t
  rw [finprod_eq_prod _ hg]
  rw [← finprod_prod_filter (PlaceTraceAdapter.prime F) hg.toFinset g]
  apply finprod_congr
  intro p
  letI := finitePlacesAboveRationalPrimeFintype F p
  rw [← fiber_character_product F t p]
  rw [← finprod_eq_prod_of_fintype]
  change (∏ y ∈ hg.toFinset with PlaceTraceAdapter.prime F y = p, g y) =
    ∏ᶠ i : {v : HeightOneSpectrum (𝓞 F) //
      finitePlaceBelow (K := ℚ) v = Rat.HeightOneSpectrum.primesEquiv.symm p}, g i.val
  rw [finprod_subtype_eq_finprod_cond]
  symm
  apply finprod_cond_eq_prod_of_cond_iff
  intro v hv
  rw [Finset.mem_filter]
  have hmem : v ∈ hg.toFinset := hg.mem_toFinset.mpr hv
  simp only [hmem, true_and]
  change finitePlaceBelow (K := ℚ) v = Rat.HeightOneSpectrum.primesEquiv.symm p ↔
    Rat.HeightOneSpectrum.primesEquiv (finitePlaceBelow (K := ℚ) v) = p
  exact Rat.HeightOneSpectrum.primesEquiv.apply_eq_iff_eq_symm_apply.symm

private theorem arch_character_product (t : F) :
    (∏ v : InfinitePlace F, archTraceCharacter v (algebraMap F v.Completion t)) =
      Circle.exp (2 * Real.pi * (Algebra.trace ℚ F t : ℝ)) := by
  classical
  rw [trace_eq_sum_localTrace_infinite F t, Finset.mul_sum]
  have h : ∀ (s : Finset (InfinitePlace F)),
      (∏ v ∈ s, archTraceCharacter v (algebraMap F v.Completion t)) =
        Circle.exp (∑ v ∈ s, 2 * Real.pi * archTrace v (algebraMap F v.Completion t)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hv ih =>
      rw [Finset.prod_insert hv, Finset.sum_insert hv, ih, Circle.exp_add]
      rfl
  exact h Finset.univ

theorem traceCharacter_diagonal_product_formula (t : F) :
    (∏ v : InfinitePlace F,
      archTraceCharacter v (algebraMap F v.Completion t)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        localFiniteCharacter F v (algebraMap F (v.adicCompletion F) t)) = 1 := by
  rw [arch_character_product F t, finite_character_product F t]
  exact rational_diagonal_additive_product (Algebra.trace ℚ F t)

end DedekindZetaZeroFree

end
