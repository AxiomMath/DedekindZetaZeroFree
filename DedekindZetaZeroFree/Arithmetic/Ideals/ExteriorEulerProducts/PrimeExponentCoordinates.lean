module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdeals.EulerWeights

@[expose] public section

namespace DedekindZetaZeroFree.ExteriorEulerPrimeIndex
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]

def exteriorPrimeRawIndex (cS : Ideal (𝓞 F)) :=
  {p : ExteriorIdeal cS // Prime p.val}

def rawOne (cS : Ideal (𝓞 F)) : ExteriorIdeal cS := ⟨⊤, by simp⟩

def rawMul {cS : Ideal (𝓞 F)} (I J : ExteriorIdeal cS) : ExteriorIdeal cS :=
  ⟨I.val * J.val, mul_ne_zero I.property.1 J.property.1,
    by rw [Ideal.mul_sup_eq_of_coprime_left I.property.2]; exact J.property.2⟩

def rawPow {cS : Ideal (𝓞 F)} (I : ExteriorIdeal cS) (k : ℕ) : ExteriorIdeal cS :=
  ⟨I.val ^ k, pow_ne_zero k I.property.1, Ideal.pow_sup_eq_top I.property.2⟩

def primeEmbedding {cS : Ideal (𝓞 F)} :
    exteriorPrimeRawIndex cS ↪ Ideal (𝓞 F) where
  toFun p := p.val.val
  inj' := by
    intro p q h
    exact Subtype.ext (Subtype.ext h)

def rawExponent {cS : Ideal (𝓞 F)} (I : ExteriorIdeal cS) :
    exteriorPrimeRawIndex cS →₀ ℕ :=
  Finsupp.comapDomain primeEmbedding (factorization I.val) primeEmbedding.injective.injOn

private theorem factor_support {cS : Ideal (𝓞 F)} (I : ExteriorIdeal cS) :
    ↑(factorization I.val).support ⊆ Set.range (primeEmbedding (cS := cS)) := by
  intro p hp
  have hm : p ∈ UniqueFactorizationMonoid.normalizedFactors I.val := by
    have hp' : p ∈ (factorization I.val).support := hp
    simpa only [support_factorization, Multiset.mem_toFinset] using hp'
  have hd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hm
  have hc : p ⊔ cS = ⊤ := top_unique (I.property.2 ▸
    sup_le_sup_right (Ideal.dvd_iff_le.mp hd) cS)
  exact ⟨⟨⟨p, (UniqueFactorizationMonoid.prime_of_normalized_factor p hm).ne_zero, hc⟩,
    UniqueFactorizationMonoid.prime_of_normalized_factor p hm⟩, rfl⟩

def fromExponent {cS : Ideal (𝓞 F)}
    (v : exteriorPrimeRawIndex cS →₀ ℕ) : ExteriorIdeal cS :=
  ⟨(v.toMultiset.map primeEmbedding).prod, by
    apply Multiset.prod_ne_zero
    intro h
    obtain ⟨p, _, hp⟩ := Multiset.mem_map.mp h
    exact p.property.ne_zero hp,
    by
      rw [sup_comm]
      apply Ideal.sup_multiset_prod_eq_top
      intro p hp
      obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
      exact sup_comm q.val.val cS ▸ q.val.property.2⟩

private theorem factorization_fromExponent {cS : Ideal (𝓞 F)}
    (v : exteriorPrimeRawIndex cS →₀ ℕ) :
    factorization (fromExponent v).val = v.embDomain primeEmbedding := by
  unfold factorization fromExponent
  rw [UniqueFactorizationMonoid.normalizedFactors_prod_of_prime]
  · rw [Finsupp.toMultiset_map, Finsupp.toMultiset_toFinsupp]
    exact (Finsupp.embDomain_eq_mapDomain _ _).symm
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
    exact q.property

theorem rawExponent_bijective (cS : Ideal (𝓞 F)) :
    Function.Bijective (rawExponent (cS := cS)) := by
  constructor
  · intro I J h
    apply Subtype.ext
    apply associated_iff_eq.mp
    apply associated_of_factorization_eq _ _ I.property.1 J.property.1
    have hi := Finsupp.embDomain_comapDomain (factor_support I)
    have hj := Finsupp.embDomain_comapDomain (factor_support J)
    exact hi.symm.trans ((congrArg (Finsupp.embDomain primeEmbedding) h).trans hj)
  · intro v
    refine ⟨fromExponent v, ?_⟩
    ext p
    simp only [rawExponent, Finsupp.comapDomain_apply, factorization_fromExponent,
      Finsupp.embDomain_apply_self]

def exponentEquiv (cS : Ideal (𝓞 F)) :
    ExteriorIdeal cS ≃ (exteriorPrimeRawIndex cS →₀ ℕ) :=
  Equiv.ofBijective rawExponent (rawExponent_bijective cS)

private theorem fromExponent_zero {cS : Ideal (𝓞 F)} :
    fromExponent (0 : exteriorPrimeRawIndex cS →₀ ℕ) = rawOne cS := by
  apply Subtype.ext
  simp [fromExponent, rawOne]

private theorem fromExponent_single {cS : Ideal (𝓞 F)}
    (p : exteriorPrimeRawIndex cS) (k : ℕ) :
    fromExponent (Finsupp.single p k) = rawPow p.val k := by
  apply Subtype.ext
  simp only [fromExponent, rawPow, Finsupp.toMultiset_single, Multiset.map_nsmul,
    Multiset.map_singleton, Multiset.prod_nsmul, Multiset.prod_singleton]
  rfl

private theorem fromExponent_add {cS : Ideal (𝓞 F)}
    (v w : exteriorPrimeRawIndex cS →₀ ℕ) :
    fromExponent (v + w) = rawMul (fromExponent v) (fromExponent w) := by
  apply Subtype.ext
  simp [fromExponent, rawMul, Finsupp.toMultiset_add]

private theorem fromExponent_coprime {cS : Ideal (𝓞 F)}
    (p : exteriorPrimeRawIndex cS) (v : exteriorPrimeRawIndex cS →₀ ℕ)
    (hp : p ∉ v.support) (k : ℕ) :
    (rawPow p.val k).val ⊔ (fromExponent v).val = ⊤ := by
  apply Ideal.pow_sup_eq_top
  apply Ideal.sup_multiset_prod_eq_top
  intro q hq
  obtain ⟨q', hq', rfl⟩ := Multiset.mem_map.mp hq
  have hne : p.val.val ≠ q'.val.val := by
    intro h
    have he : p = q' := primeEmbedding.injective h
    exact hp (he ▸ (Finsupp.mem_toMultiset v q').mp hq')
  exact (Ideal.isPrime_of_prime p.property).isMaximal p.property.ne_zero |>.coprime_of_ne
    ((Ideal.isPrime_of_prime q'.property).isMaximal q'.property.ne_zero) hne

theorem coefficient_factorization {cS : Ideal (𝓞 F)}
    (f : ExteriorIdeal cS → ℂ)
    (h1 : f (rawOne cS) = 1)
    (hmul : ∀ I J : ExteriorIdeal cS, I.val ⊔ J.val = ⊤ →
      f (rawMul I J) = f I * f J)
    (hpow : ∀ (p : exteriorPrimeRawIndex cS) (k : ℕ),
      f (rawPow p.val k) = f p.val ^ k)
    (I : ExteriorIdeal cS) :
    f I = (rawExponent I).prod (fun p k => f p.val ^ k) := by
  have hv (v : exteriorPrimeRawIndex cS →₀ ℕ) :
      f (fromExponent v) = v.prod (fun p k => f p.val ^ k) := by
    induction v using Finsupp.induction with
    | zero => simpa only [fromExponent_zero, Finsupp.prod_zero_index] using h1
    | @single_add p k v hp hk ih =>
      rw [fromExponent_add, fromExponent_single,
        hmul _ _ (fromExponent_coprime p v hp k), hpow, ih]
      rw [Finsupp.prod_add_index' (fun (p : exteriorPrimeRawIndex cS) => pow_zero (f p.val))
        (fun (p : exteriorPrimeRawIndex cS) m n => pow_add (f p.val) m n),
        Finsupp.prod_single_index]
      exact pow_zero _
  have he : fromExponent (rawExponent I) = I := by
    apply Subtype.ext
    apply associated_iff_eq.mp
    apply associated_of_factorization_eq _ _ (fromExponent _).property.1 I.property.1
    rw [factorization_fromExponent]
    exact Finsupp.embDomain_comapDomain (factor_support I)
  simpa only [he] using hv (rawExponent I)

end
end DedekindZetaZeroFree.ExteriorEulerPrimeIndex
