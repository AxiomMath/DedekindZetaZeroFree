module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdeals.EulerWeights

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

theorem unique_coprime_powerful_squarefree_decomposition
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    ∃! hd : NonzeroIdeal F × NonzeroIdeal F,
      m = hd.1.val * hd.2.val ∧ Powerful hd.1.val ∧
        Squarefree hd.2.val ∧ hd.1.val ⊔ hd.2.val = ⊤ := by
  classical
  let t := UniqueFactorizationMonoid.normalizedFactors m
  let H := t.filter (fun p => t.count p ≠ 1)
  let D := t.filter (fun p => t.count p = 1)
  let h := H.prod
  let d := D.prod
  have hH : H ⊆ UniqueFactorizationMonoid.normalizedFactors m := Multiset.filter_subset _ _
  have hD : D ⊆ UniqueFactorizationMonoid.normalizedFactors m := Multiset.filter_subset _ _
  have hh0 : h ≠ 0 := Multiset.prod_ne_zero (fun hz =>
    (UniqueFactorizationMonoid.prime_of_normalized_factor 0 (hH hz)).ne_zero rfl)
  have hd0 : d ≠ 0 := Multiset.prod_ne_zero (fun hz =>
    (UniqueFactorizationMonoid.prime_of_normalized_factor 0 (hD hz)).ne_zero rfl)
  have hhf : UniqueFactorizationMonoid.normalizedFactors h = H :=
    UniqueFactorizationMonoid.normalizedFactors_prod_eq_self_of_subset hH
  have hdf : UniqueFactorizationMonoid.normalizedFactors d = D :=
    UniqueFactorizationMonoid.normalizedFactors_prod_eq_self_of_subset hD
  have hhc : ∀ p, idealPrimeExponent p h = if t.count p ≠ 1 then t.count p else 0 := by
    intro p
    simp only [idealPrimeExponent, hhf, H, Multiset.count_filter]
  have hdc : ∀ p, idealPrimeExponent p d = if t.count p = 1 then t.count p else 0 := by
    intro p
    simp only [idealPrimeExponent, hdf, D, Multiset.count_filter]
  have hfac : m = h * d := by
    have ht : H + D = t := by
      simpa only [H, D, not_not] using Multiset.filter_add_not (fun p => t.count p ≠ 1) t
    have heq := UniqueFactorizationMonoid.prod_normalizedFactors_eq hm
    rw [normalize_eq] at heq
    calc
      m = t.prod := heq.symm
      _ = (H + D).prod := congrArg Multiset.prod ht.symm
      _ = h * d := Multiset.prod_add _ _
  have hpower : Powerful h := by
    intro p hp
    rw [hhc]
    split_ifs with hc
    · omega
    · exact Or.inl rfl
  have dsq : Squarefree d := by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hd0).mpr
    apply Multiset.nodup_iff_count_le_one.mpr
    intro p
    change idealPrimeExponent p d ≤ 1
    rw [hdc]
    split_ifs <;> omega
  have hrel : IsRelPrime h d := by
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hh0).mpr
    intro p hph hpd hp
    have hpmh := (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hh0).mpr
      ⟨hp.irreducible, normalize_eq p, hph⟩
    have hpmd := (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hd0).mpr
      ⟨hp.irreducible, normalize_eq p, hpd⟩
    rw [hhf] at hpmh
    rw [hdf] at hpmd
    exact (Multiset.mem_filter.mp hpmh).2 (Multiset.mem_filter.mp hpmd).2
  have hcop : h ⊔ d = ⊤ := by
    simpa only [Ideal.gcd_eq_sup, Ideal.one_eq_top] using
      (gcd_isUnit_iff_isRelPrime.mpr hrel).eq_one
  refine ⟨(⟨h, hh0⟩, ⟨d, hd0⟩), ⟨hfac, hpower, dsq, hcop⟩, ?_⟩
  rintro ⟨⟨h', hh'⟩, ⟨d', hd'⟩⟩ ⟨hfac', hpower', dsq', hcop'⟩
  have dc' := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hd').mp dsq')
  have hdis := UniqueFactorizationMonoid.disjoint_normalizedFactors
    ((Ideal.isCoprime_iff_sup_eq.mpr hcop').isRelPrime)
  have hc' : ∀ p, idealPrimeExponent p h' = idealPrimeExponent p h ∧
      idealPrimeExponent p d' = idealPrimeExponent p d := by
    intro p
    have he : t.count p = idealPrimeExponent p h' + idealPrimeExponent p d' := by
      change idealPrimeExponent p m = _
      rw [hfac']
      simp only [idealPrimeExponent,
        UniqueFactorizationMonoid.normalizedFactors_mul hh' hd', Multiset.count_add]
    have hdle : idealPrimeExponent p d' ≤ 1 := dc' p
    have hdz : idealPrimeExponent p h' = 0 ∨ idealPrimeExponent p d' = 0 := by
      by_cases hz : idealPrimeExponent p h' = 0
      · exact Or.inl hz
      · right
        apply Multiset.count_eq_zero_of_notMem
        exact Multiset.disjoint_left.mp hdis
          (Multiset.count_pos.mp (Nat.pos_of_ne_zero hz))
    rw [hhc, hdc]
    by_cases ht0 : t.count p = 0
    · simp only [ht0, ne_eq, Nat.zero_ne_one, not_false_eq_true, if_true, if_false]
      omega
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor p
      (Multiset.count_pos.mp (Nat.pos_of_ne_zero ht0))
    have hpp : idealPrimeExponent p h' = 0 ∨ 2 ≤ idealPrimeExponent p h' := hpower' p hp
    by_cases ht1 : t.count p = 1
    · simp only [ht1, ne_eq, not_true_eq_false, if_false, if_true]
      omega
    · simp only [ht1, ne_eq, not_false_eq_true, if_true, if_false]
      omega
  have heq : h' = h := associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors hh' hh0).mpr
      (Multiset.ext.mpr fun p => (hc' p).1))
  have deq : d' = d := associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors hd' hd0).mpr
      (Multiset.ext.mpr fun p => (hc' p).2))
  exact Prod.ext (Subtype.ext heq) (Subtype.ext deq)

theorem exterior_of_powerful_squarefree_factorization
    {cS m h d : Ideal (𝓞 F)}
    (hm : m ⊔ cS = ⊤) (hmd : m = h * d) :
    h ⊔ cS = ⊤ ∧ d ⊔ cS = ⊤ := by
  constructor
  · apply top_unique
    rw [← hm, hmd]
    exact sup_le (Ideal.mul_le_left.trans le_sup_left) le_sup_right
  · apply top_unique
    rw [← hm, hmd]
    exact sup_le (Ideal.mul_le_right.trans le_sup_left) le_sup_right

theorem squarefree_radical_divisor_pow_two_le_powerful
    (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) (hpower : Powerful h)
    (f : Ideal (𝓞 F)) (hf : Squarefree f)
    (hdiv : f ∣ idealRadical h) :
    f ^ 2 ∣ h ∧ idealNorm f ^ 2 ≤ idealNorm h := by
  have hr := idealRadical_squarefree_nonzero h hh
  have hf0 : f ≠ 0 := ne_zero_of_dvd_ne_zero hr.2 hdiv
  have hcounts := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
    hf0 hr.2).mp hdiv
  have hsq := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf0).mp hf
  have hpow : f ^ 2 ∣ h := by
    apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      (pow_ne_zero _ hf0) hh).mpr
    apply Multiset.le_iff_count.mpr
    intro p
    rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
    by_cases hp0 : (UniqueFactorizationMonoid.normalizedFactors f).count p = 0
    · simp [hp0]
    have hpmem := Multiset.count_pos.mp (Nat.pos_of_ne_zero hp0)
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor p hpmem
    have hrad : 0 < idealPrimeExponent p (idealRadical h) :=
      lt_of_lt_of_le (Nat.pos_of_ne_zero hp0) ((Multiset.le_iff_count.mp hcounts) p)
    rw [idealPrimeExponent_radical h hh p hp] at hrad
    have hph : p ∈ idealPrimeSupport h := by
      by_contra hn
      simp [hn] at hrad
    have hhpos : 0 < idealPrimeExponent p h := by
      exact Multiset.count_pos.mpr (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hph)
    have he := (hpower p hp).resolve_left (Nat.ne_of_gt hhpos)
    have hc := (Multiset.nodup_iff_count_le_one.mp hsq) p
    change 2 * (UniqueFactorizationMonoid.normalizedFactors f).count p ≤ idealPrimeExponent p h
    omega
  refine ⟨hpow, ?_⟩
  have hn : Ideal.absNorm (f ^ 2) ≤ Ideal.absNorm h :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hh))
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hpow))
  have hn' : (Ideal.absNorm (f ^ 2) : ℝ) ≤ (Ideal.absNorm h : ℝ) := by exact_mod_cast hn
  simpa [idealNorm, map_pow] using hn'

theorem unique_powerful_square_cube_decomposition
    (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) (hpower : Powerful h) :
    ∃! rs : NonzeroIdeal F × NonzeroIdeal F,
      h = rs.1.val ^ 2 * rs.2.val ^ 3 ∧ Squarefree rs.2.val := by
  classical
  obtain ⟨e, s, hes, hs⟩ := exists_sq_mul_squarefree h
  have he0 : e ≠ 0 := by intro he; simp [he] at hes; exact hh hes.symm
  have hs0 : s ≠ 0 := by intro he; simp [he] at hes; exact hh hes.symm
  have hscount := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hs0).mp hs)
  have hse : s ∣ e := by
    apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hs0 he0).mpr
    apply Multiset.le_iff_count.mpr
    intro p
    by_cases hp0 : (UniqueFactorizationMonoid.normalizedFactors s).count p = 0
    · simp [hp0]
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor p
      (Multiset.count_pos.mp (Nat.pos_of_ne_zero hp0))
    have hc := hscount p
    have hpc := hpower p hp
    have hexp : idealPrimeExponent p h =
        2 * (UniqueFactorizationMonoid.normalizedFactors e).count p +
        (UniqueFactorizationMonoid.normalizedFactors s).count p := by
      rw [← hes]
      simp [idealPrimeExponent, UniqueFactorizationMonoid.normalizedFactors_mul
        (pow_ne_zero _ he0) hs0, Multiset.count_nsmul]
    rw [hexp] at hpc
    omega
  obtain ⟨r, her⟩ := hse
  have hr0 : r ≠ 0 := by intro hr; simp [hr] at her; exact he0 her
  have hfactor : h = r ^ 2 * s ^ 3 := by
    rw [← hes, her]
    ring
  refine ⟨(⟨r, hr0⟩, ⟨s, hs0⟩), ⟨hfactor, hs⟩, ?_⟩
  rintro ⟨⟨r', hr'⟩, ⟨s', hs'⟩⟩ ⟨hfactor', hsq'⟩
  have hscount' := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hs').mp hsq')
  have hcount : ∀ p : Ideal (𝓞 F),
      (UniqueFactorizationMonoid.normalizedFactors r').count p =
        (UniqueFactorizationMonoid.normalizedFactors r).count p ∧
      (UniqueFactorizationMonoid.normalizedFactors s').count p =
        (UniqueFactorizationMonoid.normalizedFactors s).count p := by
    intro p
    have hexp := congrArg (fun I => idealPrimeExponent p I) (hfactor'.symm.trans hfactor)
    simp only [idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ hr') (pow_ne_zero _ hs'),
      UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ hr0) (pow_ne_zero _ hs0),
      UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_add,
      Multiset.count_nsmul] at hexp
    have hc := hscount p
    have hc' := hscount' p
    omega
  have hre : r' = r := associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors hr' hr0).mpr
      (Multiset.ext.mpr fun p => (hcount p).1))
  have hse' : s' = s := associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors hs' hs0).mpr
      (Multiset.ext.mpr fun p => (hcount p).2))
  exact Prod.ext (Subtype.ext hre) (Subtype.ext hse')

end
end DedekindZetaZeroFree
