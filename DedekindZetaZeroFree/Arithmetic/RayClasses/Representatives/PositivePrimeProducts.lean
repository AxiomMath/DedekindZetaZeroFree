module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClassOperations

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.AbelianQuotient

private lemma ideal_pow_ne_bot {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    {P : Ideal R} (hP : P ≠ ⊥) (n : ℕ) : P ^ n ≠ ⊥ := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact fun h => bot_ne_top h.symm
  | succ n ih => rw [pow_succ]; exact fun h => (Ideal.mul_eq_bot.mp h).elim ih hP

private lemma prime_coprime_modulus
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (narrowIdealModulus K m hm).finitePart.support) :
    v.asIdeal ⊔ m = ⊤ := by
  have hnot : ¬ m ≤ v.asIdeal := by
    intro hle
    apply hv
    apply Finsupp.mem_support_iff.mpr
    rw [narrowIdealModulus_finitePart]
    exact Multiset.count_ne_zero.mpr
      ((Ideal.mem_normalizedFactors_iff hm).mpr ⟨v.isPrime, hle⟩)
  by_contra hne
  have heq := v.isMaximal.eq_of_le hne le_sup_left
  exact hnot (heq ▸ le_sup_right)

private lemma rayIdealClass_pow
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (P : Ideal (𝓞 K)) (c : RayIdealClass K m hm)
    (hc : rayIdealClass K m hm P = some c) (n : ℕ) :
    rayIdealClass K m hm (P ^ n) = some (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top]; exact rayIdealClass_top K m hm
  | succ n ih =>
      rw [pow_succ, pow_succ, rayIdealClass_mul K m hm (P ^ n) P, ih, hc]
      simp

private lemma rayIdealClass_prod
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    {ι : Type*} (s : Finset ι) (P : ι → Ideal (𝓞 K))
    (c : ι → RayIdealClass K m hm)
    (hne : ∀ i ∈ s, P i ≠ ⊥)
    (hcop : ∀ i ∈ s, P i ⊔ m = ⊤)
    (hcl : ∀ i ∈ s, rayIdealClass K m hm (P i) = some (c i)) :
    (∏ i ∈ s, P i) ≠ ⊥ ∧ (∏ i ∈ s, P i) ⊔ m = ⊤ ∧
      rayIdealClass K m hm (∏ i ∈ s, P i) = some (∏ i ∈ s, c i) := by
  have key : ∀ s : Finset ι,
      (∀ i ∈ s, P i ≠ ⊥) → (∀ i ∈ s, P i ⊔ m = ⊤) →
      (∀ i ∈ s, rayIdealClass K m hm (P i) = some (c i)) →
      (∏ i ∈ s, P i) ≠ ⊥ ∧ (∏ i ∈ s, P i) ⊔ m = ⊤ ∧
        rayIdealClass K m hm (∏ i ∈ s, P i) = some (∏ i ∈ s, c i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ _ _
        simp [Finset.prod_empty, Ideal.one_eq_top, rayIdealClass_top K m hm]
    | insert v s hv ih =>
        intro hne hcop hcl
        rw [Finset.prod_insert hv, Finset.prod_insert hv]
        obtain ⟨ihne, ihcop, ihcl⟩ :=
          ih (fun i hi => hne i (Finset.mem_insert_of_mem hi))
            (fun i hi => hcop i (Finset.mem_insert_of_mem hi))
            (fun i hi => hcl i (Finset.mem_insert_of_mem hi))
        have hvne : P v ≠ ⊥ := hne v (Finset.mem_insert_self v s)
        have hvcop : P v ⊔ m = ⊤ := hcop v (Finset.mem_insert_self v s)
        have hvcl : rayIdealClass K m hm (P v) = some (c v) := hcl v (Finset.mem_insert_self v s)
        refine ⟨?_, ?_, ?_⟩
        · intro h
          rcases Ideal.mul_eq_bot.mp h with h' | h'
          · exact hvne h'
          · exact ihne h'
        · rw [← Ideal.isCoprime_iff_sup_eq] at hvcop ihcop ⊢
          exact hvcop.mul_left ihcop
        · rw [rayIdealClass_mul K m hm (P v) (∏ i ∈ s, P i), hvcl, ihcl]
          simp
  exact key s hne hcop hcl

theorem rayPositivePrimeProduct
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    let μ := narrowIdealModulus K m hm
    let V := {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) //
      v ∉ μ.finitePart.support}
    ∀ (s : Finset V) (e : V → ℕ),
      let a : Ideal (𝓞 K) := ∏ v ∈ s, v.val.asIdeal ^ e v
      a ≠ ⊥ ∧ a ⊔ m = ⊤ ∧
        rayIdealClass K m hm a =
          some (∏ v ∈ s,
            (ClassFieldTheory.rayClassOfFinitePrime μ v.val v.property) ^ e v) := by
  dsimp only
  intro s e
  exact rayIdealClass_prod K m hm s (fun v : {v : HeightOneSpectrum (𝓞 K) //
      v ∉ (narrowIdealModulus K m hm).finitePart.support} => v.val.asIdeal ^ e v)
    (fun v => (ClassFieldTheory.rayClassOfFinitePrime (narrowIdealModulus K m hm)
      v.val v.property) ^ e v)
    (fun v _ => ideal_pow_ne_bot v.val.ne_bot (e v))
    (fun v _ => Ideal.isCoprime_iff_sup_eq.mp
      (Ideal.isCoprime_iff_sup_eq.mpr (prime_coprime_modulus K m hm v.val v.property)).pow_left)
    (fun v _ => rayIdealClass_pow K m hm v.val
      (ClassFieldTheory.rayClassOfFinitePrime (narrowIdealModulus K m hm) v.val v.property)
      (rayIdealClass_of_finitePrime K m hm v.val v.property) (e v))

end DedekindZetaZeroFree.AbelianQuotient

end
