module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

noncomputable def rationalPrincipalIdeal (F : Type) [Field F] [NumberField F]
    (p : ℕ) : Ideal (𝓞 F) :=
  Ideal.span ({(p : 𝓞 F)} : Set (𝓞 F))

theorem rationalPrincipalIdeal_ne_bot (F : Type) [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) : rationalPrincipalIdeal F p ≠ ⊥ := by
  intro h
  exact Nat.cast_ne_zero.mpr hp.ne_zero ((Ideal.span_singleton_eq_bot).mp h)

theorem rationalPrincipalIdeal_absNorm (F : Type) [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) :
    Ideal.absNorm (rationalPrincipalIdeal F p) = p ^ Module.finrank ℚ F := by
  rw [rationalPrincipalIdeal, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]

theorem rationalPrincipalIdeal_squarefree (F : Type) [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) (hunramified : ¬ (p : ℤ) ∣ NumberField.discr F) :
    Squarefree (rationalPrincipalIdeal F p) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hne : rationalPrincipalIdeal F p ≠ ⊥ := rationalPrincipalIdeal_ne_bot F hp
  rw [squarefree_iff_no_irreducibles hne]
  intro Q hirr hdvd
  have hprime : Prime Q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hQprime : Q.IsPrime := Ideal.isPrime_of_prime hprime
  have hle : rationalPrincipalIdeal F p ≤ Q * Q := Ideal.dvd_iff_le.mp hdvd
  have hpQnat : (p : 𝓞 F) ∈ Q :=
    (SetLike.le_def.mp (le_trans hle Ideal.mul_le_right)) (Ideal.mem_span_singleton_self _)
  have hpQ : ((p : ℤ) : 𝓞 F) ∈ Q := by simpa using hpQnat
  have hlies : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    (Ideal.liesOver_span_iff hQprime.ne_top hpZ).mpr hpQ
  haveI := hlies
  haveI := hQprime
  have hunram : Algebra.IsUnramifiedAt ℤ Q :=
    (NumberField.not_dvd_discr_iff_forall_mem F (𝓞 F) hpZ).mp hunramified Q hQprime hpQ
  haveI := hunram
  have h1 : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) Q = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) Q
      (Ideal.span_singleton_eq_bot.not.mpr hpZ.ne_zero)]
    exact Ideal.ramificationIdx_eq_one Q ℤ
  have hmap_eq : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) =
      rationalPrincipalIdeal F p := by
    rw [Ideal.map_span, Set.image_singleton, rationalPrincipalIdeal]
    simp
  have hmap_le : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≤ Q := by
    rw [hlies.over]
    exact Ideal.map_comap_le
  exact (Ideal.ramificationIdx'_ne_one_iff hmap_le).mpr
    (by rw [hmap_eq, pow_two]; exact hle) h1

theorem rationalPrincipalIdeal_sup_eq_top (F : Type) [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (havoid : ¬ p ∣ Ideal.absNorm I) :
    rationalPrincipalIdeal F p ⊔ I = ⊤ := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hPprime : P.IsPrime := hPmax.isPrime
  have hpP : (p : 𝓞 F) ∈ P :=
    (SetLike.le_def.mp hle) (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hlies : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    (Ideal.liesOver_span_iff hPprime.ne_top hpZ).mpr (by simpa using hpP)
  haveI := hlies
  haveI := hPprime
  have habs : Ideal.absNorm P = p ^ P.inertiaDeg ℤ := (Ideal.pow_inertiaDeg p P).symm
  have hk : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos (q := P) (R := ℤ)
  have hdvd : Ideal.absNorm P ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le (le_trans le_sup_right hle)
  have hpP' : p ∣ Ideal.absNorm P := by
    rw [habs]
    simpa using pow_dvd_pow p hk
  exact havoid (dvd_trans hpP' hdvd)

theorem rationalPrincipalIdeal_squarefree_coprime (F : Type) [Field F]
    [NumberField F] {p : ℕ} (hp : p.Prime) (q : Ideal (𝓞 F)) (hq : q ≠ ⊥)
    (hlarge : max (NumberField.discr F).natAbs (Ideal.absNorm q) < p) :
    Squarefree (rationalPrincipalIdeal F p) ∧
      rationalPrincipalIdeal F p ⊔ q = ⊤ := by
  have hdiscr : ¬ (p : ℤ) ∣ NumberField.discr F := by
    intro h
    have h1 : p ∣ (NumberField.discr F).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    have hpos : 0 < (NumberField.discr F).natAbs :=
      Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
    have h2 : p ≤ (NumberField.discr F).natAbs := Nat.le_of_dvd hpos h1
    have h3 := le_max_left (NumberField.discr F).natAbs (Ideal.absNorm q)
    omega
  have havoid : ¬ p ∣ Ideal.absNorm q := by
    intro h
    have hpos : 0 < Ideal.absNorm q := by
      rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
      exact hq
    have h2 : p ≤ Ideal.absNorm q := Nat.le_of_dvd hpos h
    have h3 := le_max_right (NumberField.discr F).natAbs (Ideal.absNorm q)
    omega
  exact ⟨rationalPrincipalIdeal_squarefree F hp hdiscr,
    rationalPrincipalIdeal_sup_eq_top F hp q hq havoid⟩

end DedekindZetaZeroFree.LargeSieve.Sieve
