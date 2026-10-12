module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClasses

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.AbelianQuotient

theorem narrowModulus_support_iff
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ (narrowIdealModulus K m hm).finitePart.support ↔ m ≤ v.asIdeal := by
  rw [Finsupp.mem_support_iff, narrowIdealModulus_finitePart, Multiset.count_ne_zero,
    Ideal.mem_normalizedFactors_iff hm]
  exact ⟨fun h => h.2, fun h => ⟨v.isPrime, h⟩⟩

theorem mem_ideal_iff_narrow_primePowers
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (r : 𝓞 K) :
    r ∈ m ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ (narrowIdealModulus K m hm).finitePart.support →
        r ∈ v.asIdeal ^ ((narrowIdealModulus K m hm).finitePart v) := by
  have hprime : ∀ P ∈ (normalizedFactors m).toFinset, Prime P := by
    intro P hP
    have hmem := Multiset.mem_toFinset.mp hP
    have hPne : P ≠ ⊥ := by
      intro h
      have hmle : m ≤ ⊥ := by
        rw [h] at hmem
        exact ((Ideal.mem_normalizedFactors_iff hm).mp hmem).2
      exact hm (le_bot_iff.mp hmle)
    exact Ideal.prime_of_isPrime hPne ((Ideal.mem_normalizedFactors_iff hm).mp hmem).1
  have hcop : ∀ᵉ (i ∈ (normalizedFactors m).toFinset) (j ∈ (normalizedFactors m).toFinset),
      i ≠ j → (fun P => P) i ≠ (fun P => P) j := fun _ _ _ _ hij => hij
  have hcount : (normalizedFactors m).prod =
      ∏ P ∈ (normalizedFactors m).toFinset,
        P ^ Multiset.count P (normalizedFactors m) :=
    Finset.prod_multiset_count (normalizedFactors m)
  have hinf :
      ∏ P ∈ (normalizedFactors m).toFinset,
        P ^ Multiset.count P (normalizedFactors m) =
      ((normalizedFactors m).toFinset.inf
        fun P => P ^ Multiset.count P (normalizedFactors m)) := by
    simpa using (IsDedekindDomain.inf_pow_eq_prod_of_prime
      (s := (normalizedFactors m).toFinset) (f := fun P => P)
      (e := fun P => Multiset.count P (normalizedFactors m)) hprime hcop).symm
  have hprod : m = (normalizedFactors m).toFinset.inf
      (fun P => P ^ Multiset.count P (normalizedFactors m)) :=
    (Ideal.prod_normalizedFactors_eq_self hm).symm.trans (hcount.trans hinf)
  have key : ∀ r : 𝓞 K, r ∈ m ↔ ∀ P ∈ (normalizedFactors m).toFinset,
      r ∈ P ^ Multiset.count P (normalizedFactors m) := by
    intro r
    conv_lhs => rw [hprod]
    rw [← Ideal.span_singleton_le_iff_mem (x := r), Finset.le_inf_iff]
    simp only [Ideal.span_singleton_le_iff_mem]
  constructor
  · intro hr v hv
    have hvmem : v.asIdeal ∈ (normalizedFactors m).toFinset :=
      Multiset.mem_toFinset.mpr (Multiset.count_ne_zero.mp (by
        simpa using Finsupp.mem_support_iff.mp hv))
    simpa [narrowIdealModulus_finitePart] using (key r).mp hr v.asIdeal hvmem
  · intro hr
    refine (key r).mpr fun P hP => ?_
    have hPmem : P ∈ normalizedFactors m := Multiset.mem_toFinset.mp hP
    have hv : (HeightOneSpectrum.ofPrime (hprime P hP)) ∈
        (narrowIdealModulus K m hm).finitePart.support := by
      rw [Finsupp.mem_support_iff, narrowIdealModulus_finitePart, Multiset.count_ne_zero]
      exact hPmem
    simpa [narrowIdealModulus_finitePart] using hr (HeightOneSpectrum.ofPrime (hprime P hP)) hv

end DedekindZetaZeroFree.AbelianQuotient

end
