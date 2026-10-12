module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

private theorem denominator_prime_generator
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    ∃ d : RingOfIntegers F, d ≠ 0 ∧
      Ideal.span ({d} : Set (RingOfIntegers F)) =
        v.asIdeal ^ Fintype.card (ClassGroup (RingOfIntegers F)) := by
  let h := Fintype.card (ClassGroup (RingOfIntegers F))
  have hn : v.asIdeal ^ h ≠ 0 := pow_ne_zero _ v.prime.ne_zero
  have hp : (v.asIdeal ^ h).IsPrincipal := by
    apply (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero hn)).mp
    have hmem : v.asIdeal ∈ (Ideal (RingOfIntegers F))⁰ :=
      mem_nonZeroDivisors_of_ne_zero v.prime.ne_zero
    rw [← SubmonoidClass.mk_pow v.asIdeal hmem, map_pow]
    exact pow_card_eq_one
  obtain ⟨d, hd⟩ := (Submodule.isPrincipal_iff _).mp hp
  refine ⟨d, ?_, hd.symm⟩
  intro hz
  simp [hz] at hd
  exact hn hd

private theorem denominator_prime_order
    {F : Type*} [Field F] [NumberField F]
    (v w : HeightOneSpectrum (RingOfIntegers F)) (h : ℕ) [DecidableEq (HeightOneSpectrum (RingOfIntegers F))] :
    multiplicity w.asIdeal (v.asIdeal ^ h) = if w = v then h else 0 := by
  classical
  split_ifs with hw
  · subst w
    exact multiplicity_pow_self_of_prime v.prime h
  · apply multiplicity_eq_zero_of_not_dvd
    intro hd
    have he : w.asIdeal = v.asIdeal := associated_iff_eq.mp
      ((w.irreducible.dvd_irreducible_iff_associated v.irreducible).mp
        (w.prime.dvd_of_dvd_pow hd))
    exact hw (HeightOneSpectrum.asIdeal_injective he)

private theorem denominator_product_order
    {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : HeightOneSpectrum (RingOfIntegers F) → RingOfIntegers F)
    (ha : ∀ v, a v ≠ 0) (w : HeightOneSpectrum (RingOfIntegers F)) :
    multiplicity w.asIdeal (Ideal.span ({∏ v ∈ S, a v} : Set (RingOfIntegers F))) =
      ∑ v ∈ S, multiplicity w.asIdeal (Ideal.span ({a v} : Set (RingOfIntegers F))) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (multiplicity_one_right (a := w.asIdeal))
  | @insert v S hv ih =>
    rw [Finset.prod_insert hv, ← Ideal.span_singleton_mul_span_singleton,
      multiplicity_mul w.prime, Finset.sum_insert hv, ih]
    apply FiniteMultiplicity.of_prime_left w.prime
    rw [Ideal.span_singleton_mul_span_singleton]
    exact fun hz => (mul_ne_zero (ha v) (Finset.prod_ne_zero_iff.mpr fun x _ => ha x))
      (Ideal.span_singleton_eq_bot.mp hz)

private theorem denominator_clears
    {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (d : RingOfIntegers F) (hd : d ≠ 0)
    (hp : ∀ v ∈ S, 0 < multiplicity v.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))))
    (b : (v : S) → v.val.adicCompletion F) (k : S → ℤ) :
    ∃ t : ℕ, ∀ v : S,
      (algebraMap F (v.val.adicCompletion F) (d : F)) ^ t * b v ∈
        v.val.adicCompletionIntegers F ∧
      0 ≤ k v + (t : ℤ) *
        (multiplicity v.val.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))) : ℤ) := by
  classical
  let bound : S → ℕ := fun v => (Valued.v (b v)).log.natAbs + (k v).natAbs
  let t := ∑ v : S, bound v
  refine ⟨t, fun v => ?_⟩
  have hbt : bound v ≤ t := Finset.single_le_sum (fun i _ => Nat.zero_le (bound i))
    (Finset.mem_univ v)
  have hlog : (Valued.v (b v)).log ≤ (t : ℤ) :=
    Int.le_natAbs.trans (by exact_mod_cast (Nat.le_add_right _ _).trans hbt)
  have hk : -(k v) ≤ (t : ℤ) := by
    have habs : (k v).natAbs ≤ t := (Nat.le_add_left _ _).trans hbt
    have hneg : -(k v) ≤ ((k v).natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -(k v)))
    exact hneg.trans (by exact_mod_cast habs)
  have hm : (1 : ℤ) ≤ multiplicity v.val.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))) :=
    by exact_mod_cast hp v.val v.property
  have ht : (0 : ℤ) ≤ t := Nat.cast_nonneg _
  have htm : (t : ℤ) ≤ (t : ℤ) *
      (multiplicity v.val.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))) : ℤ) := by
    nlinarith
  refine ⟨?_, by omega⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  by_cases hb : b v = 0
  · simp [hb]
  have hvd : Valued.v (algebraMap F (v.val.adicCompletion F) (d : F)) =
      WithZero.exp (-(multiplicity v.val.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))) : ℤ)) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    change Valued.v (d : v.val.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.val.valuation_of_algebraMap d).trans
      (v.val.intValuation_eq_exp_neg_multiplicity hd)
  have hbval : Valued.v (b v) ≠ 0 := (Valued.v.ne_zero_iff).mpr hb
  rw [map_mul, map_pow, hvd, ← WithZero.exp_log hbval,
    ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  simp only [nsmul_eq_mul]
  nlinarith

theorem sSupported_denominator
    (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    ∃ d : RingOfIntegers F, d ≠ 0 ∧
      (S = ∅ → d = 1) ∧
      (∀ w : HeightOneSpectrum (RingOfIntegers F), w ∉ S →
        multiplicity w.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))) = 0) ∧
      (∀ v ∈ S, 0 < multiplicity v.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F)))) ∧
      (∀ (b : (v : S) → v.val.adicCompletion F) (k : S → ℤ), ∃ t : ℕ, ∀ v : S,
        (algebraMap F (v.val.adicCompletion F) (d : F)) ^ t * b v ∈
          v.val.adicCompletionIntegers F ∧
        0 ≤ k v + (t : ℤ) *
          (multiplicity v.val.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))) : ℤ)) := by
  classical
  choose a ha hspan using denominator_prime_generator F
  let h := Fintype.card (ClassGroup (RingOfIntegers F))
  let d := ∏ v ∈ S, a v
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => ha v
  have horder (w : HeightOneSpectrum (RingOfIntegers F)) :
      multiplicity w.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))) =
        if w ∈ S then h else 0 := by
    rw [denominator_product_order S a ha]
    simp_rw [hspan, denominator_prime_order]
    simpa only [eq_comm] using (Finset.sum_ite_eq' S w (fun _ => h))
  have hp : ∀ v ∈ S, 0 < multiplicity v.asIdeal (Ideal.span ({d} : Set (RingOfIntegers F))) := by
    intro v hv
    rw [horder, if_pos hv]
    exact Fintype.card_pos
  refine ⟨d, hd, ?_, ?_, hp, denominator_clears S d hd hp⟩
  · intro hs
    simp [d, hs]
  · intro w hw
    rw [horder, if_neg hw]

end DedekindZetaZeroFree

end
