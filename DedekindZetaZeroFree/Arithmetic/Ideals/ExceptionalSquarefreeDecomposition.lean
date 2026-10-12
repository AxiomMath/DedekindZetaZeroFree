module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets
public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeGcdDecomposition

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

noncomputable def exceptionalDivisors (F : Type) [Field F] [NumberField F]
    (c q : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  (DedekindZetaZeroFree.LargeSieve.idealDivisors (UniqueFactorizationMonoid.radical q)).filter
    (fun t => t ⊔ c = ⊤)

variable {F : Type} [Field F] [NumberField F]
variable {c q b t u : Ideal (𝓞 F)}

private theorem isRelPrime_iff_sup_eq_top {I J : Ideal (𝓞 F)} :
    IsRelPrime I J ↔ I ⊔ J = ⊤ := by
  rw [← gcd_isUnit_iff_isRelPrime, Ideal.gcd_eq_sup, Ideal.isUnit_iff]

private theorem prime_dvd_radical_iff (hq : q ≠ ⊥) {d : Ideal (𝓞 F)} (hd : Prime d) :
    d ∣ UniqueFactorizationMonoid.radical q ↔ d ∣ q :=
  UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible hd.irreducible hq

theorem exceptional_radical_ne_bot (hq : q ≠ ⊥) :
    UniqueFactorizationMonoid.radical q ≠ ⊥ :=
  UniqueFactorizationMonoid.radical_ne_zero

theorem exceptional_radical_squarefree (hq : q ≠ ⊥) :
    Squarefree (UniqueFactorizationMonoid.radical q) :=
  UniqueFactorizationMonoid.squarefree_radical

theorem exceptional_radical_dvd (hq : q ≠ ⊥) :
    UniqueFactorizationMonoid.radical q ∣ q :=
  UniqueFactorizationMonoid.radical_dvd_self

theorem sup_exceptional_radical_eq_top_iff (hq : q ≠ ⊥) (u : Ideal (𝓞 F)) :
    u ⊔ UniqueFactorizationMonoid.radical q = ⊤ ↔ u ⊔ q = ⊤ := by
  rw [← isRelPrime_iff_sup_eq_top, ← isRelPrime_iff_sup_eq_top]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow hq
    rcases eq_or_ne n 0 with rfl | hn0
    · exact (isUnit_of_dvd_one hn).isRelPrime_right
    · exact IsRelPrime.of_dvd_right
        ((IsRelPrime.pow_right_iff (Nat.pos_of_ne_zero hn0)).mpr h) hn
  · intro h
    exact IsRelPrime.of_dvd_right h UniqueFactorizationMonoid.radical_dvd_self

theorem mem_exceptionalDivisors (hq : q ≠ ⊥) :
    t ∈ exceptionalDivisors F c q ↔
      t ∣ UniqueFactorizationMonoid.radical q ∧ t ⊔ c = ⊤ := by
  simp only [exceptionalDivisors, Finset.mem_filter,
    DedekindZetaZeroFree.LargeSieve.mem_idealDivisors (exceptional_radical_ne_bot hq)]

theorem exceptionalDivisors_properties (hq : q ≠ ⊥)
    (ht : t ∈ exceptionalDivisors F c q) :
    t ≠ ⊥ ∧ Squarefree t ∧ t ∣ q ∧ t ⊔ c = ⊤ ∧
      1 ≤ (Ideal.absNorm t : ℝ) := by
  obtain ⟨hdiv, hc⟩ := (mem_exceptionalDivisors hq).mp ht
  have htmem : t ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors (UniqueFactorizationMonoid.radical q) :=
    (Finset.mem_filter.mp ht).1
  have htne : t ≠ ⊥ := DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors htmem
  refine ⟨htne, (exceptional_radical_squarefree hq).squarefree_of_dvd hdiv,
    hdiv.trans (exceptional_radical_dvd hq), hc, ?_⟩
  have h0 : Ideal.absNorm t ≠ 0 := fun h => htne (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : (1 : ℕ) ≤ Ideal.absNorm t := Nat.one_le_iff_ne_zero.mpr h0
  exact_mod_cast h1

theorem exceptional_decomposition_fixedPart (hq : q ≠ ⊥) (hcq : c ∣ q)
    (ht : t ∈ exceptionalDivisors F c q) (hu : Squarefree u)
    (huq : u ⊔ q = ⊤) (hbt : b = t * u) :
    t = b ⊔ UniqueFactorizationMonoid.radical q := by
  obtain ⟨htR, htc⟩ := (mem_exceptionalDivisors hq).mp ht
  have hrel : IsRelPrime u (UniqueFactorizationMonoid.radical q) :=
    isRelPrime_iff_sup_eq_top.mpr ((sup_exceptional_radical_eq_top_iff hq u).mpr huq)
  obtain ⟨R', hR'⟩ := htR
  have hR'dvd : R' ∣ UniqueFactorizationMonoid.radical q := ⟨t, by rw [hR', mul_comm]⟩
  have hsup : u ⊔ R' = ⊤ := isRelPrime_iff_sup_eq_top.mp (hrel.of_dvd_right hR'dvd)
  calc t = t * ⊤ := (Ideal.mul_top t).symm
    _ = t * (u ⊔ R') := by rw [hsup]
    _ = t * u ⊔ t * R' := Ideal.mul_sup t u R'
    _ = b ⊔ UniqueFactorizationMonoid.radical q := by rw [← hbt, hR']

theorem existsUnique_exceptional_decomposition (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hb : Squarefree b) (hbc : b ⊔ c = ⊤) :
    ∃! tu : Ideal (𝓞 F) × Ideal (𝓞 F),
      tu.1 ∈ exceptionalDivisors F c q ∧ Squarefree tu.2 ∧
        tu.2 ⊔ q = ⊤ ∧ b = tu.1 * tu.2 := by
  set t₀ : Ideal (𝓞 F) := b ⊔ UniqueFactorizationMonoid.radical q with ht₀
  have ht0_dvd_b : t₀ ∣ b := Ideal.dvd_iff_le.mpr le_sup_left
  have ht0_dvd_R : t₀ ∣ UniqueFactorizationMonoid.radical q :=
    Ideal.dvd_iff_le.mpr le_sup_right
  have hrel_bc : IsRelPrime b c := isRelPrime_iff_sup_eq_top.mpr hbc
  have ht0_mem : t₀ ∈ exceptionalDivisors F c q := by
    rw [mem_exceptionalDivisors hq]
    refine ⟨ht0_dvd_R, ?_⟩
    refine isRelPrime_iff_sup_eq_top.mp ?_
    intro d hdt0 hdc
    exact hrel_bc (hdt0.trans ht0_dvd_b) hdc
  obtain ⟨u₀, hu₀⟩ := ht0_dvd_b
  have hsq_u₀ : Squarefree u₀ := (hu₀ ▸ hb).of_mul_right
  have hu₀ne : u₀ ≠ ⊥ := DedekindZetaZeroFree.LargeSieve.SquarefreeGcd.ne_bot_of_squarefree hsq_u₀
  have hrel_t0u₀ : IsRelPrime t₀ u₀ := IsRelPrime.of_squarefree_mul (hu₀ ▸ hb)
  have hu₀q : u₀ ⊔ q = ⊤ := by
    rw [← isRelPrime_iff_sup_eq_top]
    refine (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hu₀ne).mpr ?_
    intro d hdu₀ hdq hd
    have hdR : d ∣ UniqueFactorizationMonoid.radical q :=
      (prime_dvd_radical_iff hq hd).mpr hdq
    have hdb : d ∣ b := by rw [hu₀]; exact dvd_mul_of_dvd_right hdu₀ _
    have hdt0 : d ∣ t₀ :=
      Ideal.dvd_iff_le.mpr (sup_le (Ideal.dvd_iff_le.mp hdb) (Ideal.dvd_iff_le.mp hdR))
    exact hd.not_isUnit (hrel_t0u₀ hdt0 hdu₀)
  refine ⟨(t₀, u₀), ⟨ht0_mem, hsq_u₀, hu₀q, hu₀⟩, ?_⟩
  rintro ⟨t', u'⟩ ⟨ht', hu', huq', hbt'⟩
  have hteq : t' = t₀ :=
    exceptional_decomposition_fixedPart hq hcq ht' hu' huq' hbt'
  have ht0ne : t₀ ≠ ⊥ := DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors (Finset.mem_filter.mp ht0_mem).1
  have hbt'' : b = t' * u' := hbt'
  have hu_eq : u' = u₀ := by
    have h1 : t₀ * u' = b := by
      conv_rhs => rw [hbt'']
      rw [hteq]
    have h2 : t₀ * u₀ = b := hu₀.symm
    exact mul_left_cancel₀ ht0ne (h1.trans h2.symm)
  exact Prod.ext hteq hu_eq

theorem exceptional_decomposition_converse (hq : q ≠ ⊥) (hcq : c ∣ q)
    (ht : t ∈ exceptionalDivisors F c q) (hu : Squarefree u)
    (huq : u ⊔ q = ⊤) :
    Squarefree (t * u) ∧ (t * u) ⊔ c = ⊤ := by
  obtain ⟨htR, htc⟩ := (mem_exceptionalDivisors hq).mp ht
  have htne : t ≠ ⊥ := DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors (Finset.mem_filter.mp ht).1
  have hrel_uq : IsRelPrime u q := isRelPrime_iff_sup_eq_top.mpr huq
  have hrel_uc : IsRelPrime u c := fun d hdu hdc => hrel_uq hdu (hdc.trans hcq)
  have hrel_tu : IsRelPrime t u := by
    refine (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors (a := t) htne).mpr ?_
    intro d hdt hdu hd
    have hdq : d ∣ q :=
      (prime_dvd_radical_iff hq hd).mp (hdt.trans htR)
    exact hd.not_isUnit (hrel_uq hdu hdq)
  have hrel_tuc : IsRelPrime (t * u) c :=
    (isRelPrime_iff_sup_eq_top.mpr htc).mul_left hrel_uc
  refine ⟨?_, isRelPrime_iff_sup_eq_top.mp hrel_tuc⟩
  rw [squarefree_mul_iff]
  exact ⟨hrel_tu, (exceptional_radical_squarefree hq).squarefree_of_dvd htR, hu⟩

end DedekindZetaZeroFree.LargeSieve.Sieve
