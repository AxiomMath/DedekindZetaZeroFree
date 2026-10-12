module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Bilinear

variable {F : Type} [Field F] [NumberField F]

def badPrimes (q : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  (UniqueFactorizationMonoid.normalizedFactors q).toFinset

def badPart (q I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ((UniqueFactorizationMonoid.normalizedFactors I).filter
    (fun p => p ∈ badPrimes q)).prod

def goodPart (q I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ((UniqueFactorizationMonoid.normalizedFactors I).filter
    (fun p => p ∉ badPrimes q)).prod

def squarefreeBadPool (q : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  (badPrimes q).powerset.image (fun s => ∏ p ∈ s, p)

theorem mem_badPrimes {q p : Ideal (𝓞 F)} (hq : q ≠ ⊥) :
    p ∈ badPrimes q ↔ Prime p ∧ p ∣ q := by
  simpa only [badPrimes, Multiset.mem_toFinset] using
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hq :
      p ∈ UniqueFactorizationMonoid.normalizedFactors q ↔ Prime p ∧ p ∣ q)

private theorem factors_bad (q I : Ideal (𝓞 F)) :
    UniqueFactorizationMonoid.normalizedFactors (badPart q I) =
      (UniqueFactorizationMonoid.normalizedFactors I).filter (fun p => p ∈ badPrimes q) := by
  apply UniqueFactorizationMonoid.normalizedFactors_prod_eq_self_of_subset
  intro p hp
  exact (Multiset.mem_filter.mp hp).1

private theorem factors_good (q I : Ideal (𝓞 F)) :
    UniqueFactorizationMonoid.normalizedFactors (goodPart q I) =
      (UniqueFactorizationMonoid.normalizedFactors I).filter (fun p => p ∉ badPrimes q) := by
  apply UniqueFactorizationMonoid.normalizedFactors_prod_eq_self_of_subset
  intro p hp
  exact (Multiset.mem_filter.mp hp).1

theorem bad_good_factorization {q I : Ideal (𝓞 F)}
    (hq : q ≠ ⊥) (hI : I ≠ ⊥) :
    badPart q I ≠ ⊥ ∧ goodPart q I ≠ ⊥ ∧
      I = badPart q I * goodPart q I ∧ goodPart q I ⊔ q = ⊤ ∧
      (∀ p : Ideal (𝓞 F), Prime p → p ∣ badPart q I → p ∣ q) := by
  let s := UniqueFactorizationMonoid.normalizedFactors I
  have he : badPart q I ≠ ⊥ := by
    apply UniqueFactorizationMonoid.prod_ne_zero_of_subset_normalizedFactors
    intro p hp
    exact (Multiset.mem_filter.mp hp).1
  have hz : goodPart q I ≠ ⊥ := by
    apply UniqueFactorizationMonoid.prod_ne_zero_of_subset_normalizedFactors
    intro p hp
    exact (Multiset.mem_filter.mp hp).1
  have hprod : I = badPart q I * goodPart q I := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
    simp only [badPart, goodPart, ← Multiset.prod_add,
      Multiset.filter_add_not (fun p : Ideal (𝓞 F) => p ∈ badPrimes q)
        (UniqueFactorizationMonoid.normalizedFactors I)]
  have hsup : goodPart q I ⊔ q = ⊤ := by
    rw [Ideal.sup_eq_prod_inf_factors hz hq, factors_good]
    have hh : (s.filter (fun p => p ∉ badPrimes q)) ∩
        UniqueFactorizationMonoid.normalizedFactors q = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro p hp
      have hp' := (Multiset.mem_inter.mp hp)
      exact (Multiset.mem_filter.mp hp'.1).2 (Multiset.mem_toFinset.mpr hp'.2)
    change (s.filter (fun p => p ∉ badPrimes q) ∩
      UniqueFactorizationMonoid.normalizedFactors q).prod = ⊤
    rw [hh, Multiset.prod_zero]
    exact Ideal.one_eq_top
  refine ⟨he, hz, hprod, hsup, ?_⟩
  intro p hp hpe
  have hmem := (UniqueFactorizationMonoid.mem_normalizedFactors_iff he).mpr ⟨hp, hpe⟩
  rw [factors_bad] at hmem
  exact (mem_badPrimes hq).mp (Multiset.mem_filter.mp hmem).2 |>.2

theorem bad_good_unique {q I e z : Ideal (𝓞 F)}
    (hq : q ≠ ⊥) (hI : I ≠ ⊥) (he : e ≠ ⊥) (hz : z ≠ ⊥)
    (hIz : I = e * z) (hzq : z ⊔ q = ⊤)
    (heq : ∀ p : Ideal (𝓞 F), Prime p → p ∣ e → p ∣ q) :
    e = badPart q I ∧ z = goodPart q I := by
  have hcop : IsRelPrime z q := (Ideal.isCoprime_iff_sup_eq.mpr hzq).isRelPrime
  have hfe : (UniqueFactorizationMonoid.normalizedFactors e).filter
      (fun p => p ∈ badPrimes q) = UniqueFactorizationMonoid.normalizedFactors e := by
    apply Multiset.filter_eq_self.mpr
    intro p hp
    exact (mem_badPrimes hq).mpr
      ⟨UniqueFactorizationMonoid.prime_of_normalized_factor p hp,
        heq p (UniqueFactorizationMonoid.prime_of_normalized_factor p hp)
          (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)⟩
  have hfz : (UniqueFactorizationMonoid.normalizedFactors z).filter
      (fun p => p ∈ badPrimes q) = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro p hp
    obtain ⟨hpz, hpq⟩ := Multiset.mem_filter.mp hp
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p hpz
    exact hprime.not_isUnit (hcop
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpz) ((mem_badPrimes hq).mp hpq).2)
  have heb : e = badPart q I := by
    rw [badPart, hIz, UniqueFactorizationMonoid.normalizedFactors_mul he hz,
      Multiset.filter_add, hfe, hfz, add_zero, Ideal.prod_normalizedFactors_eq_self he]
  refine ⟨heb, ?_⟩
  apply mul_left_cancel₀ he
  rw [← hIz, heb]
  exact (bad_good_factorization hq hI).2.2.1

theorem squarefree_bad_good {q I : Ideal (𝓞 F)}
    (hq : q ≠ ⊥) (hI : I ≠ ⊥) (hsf : Squarefree I) :
    Squarefree (badPart q I) ∧ Squarefree (goodPart q I) := by
  rw [(bad_good_factorization hq hI).2.2.1] at hsf
  exact ⟨hsf.of_mul_left, hsf.of_mul_right⟩

private theorem factors_prod_subset {q : Ideal (𝓞 F)} (hq : q ≠ ⊥)
    {s : Finset (Ideal (𝓞 F))} (hs : s ⊆ badPrimes q) :
    UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val := by
  rw [Finset.prod_eq_multiset_prod]
  simp only [Multiset.map_id']
  apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
  intro p hp
  exact ((mem_badPrimes hq).mp (hs (Finset.mem_def.mpr hp))).1

private theorem supported_subset {q e : Ideal (𝓞 F)} (hq : q ≠ ⊥) (he : e ≠ ⊥)
    (hsf : Squarefree e) (hsup : ∀ p : Ideal (𝓞 F), Prime p → p ∣ e → p ∣ q) :
    ∃! s : Finset (Ideal (𝓞 F)), s ⊆ badPrimes q ∧ e = ∏ p ∈ s, p := by
  let s := (UniqueFactorizationMonoid.normalizedFactors e).toFinset
  have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors he).mp hsf
  have hv : s.val = UniqueFactorizationMonoid.normalizedFactors e := by
    exact (Multiset.toFinset_val _).trans (Multiset.dedup_eq_self.mpr hn)
  have hs : s ⊆ badPrimes q := by
    intro p hp
    have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors e := Multiset.mem_toFinset.mp hp
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p hp'
    exact (mem_badPrimes hq).mpr ⟨hprime, hsup p hprime
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp')⟩
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [Finset.prod_eq_multiset_prod]
    simp only [Multiset.map_id', hv, Ideal.prod_normalizedFactors_eq_self he]
  · intro t ht
    apply Finset.val_injective
    rw [hv, ht.2, factors_prod_subset hq ht.1]

theorem mem_squarefreeBadPool {q e : Ideal (𝓞 F)} (hq : q ≠ ⊥) :
    e ∈ squarefreeBadPool q ↔ e ≠ ⊥ ∧ Squarefree e ∧
      (∀ p : Ideal (𝓞 F), Prime p → p ∣ e → p ∣ q) := by
  constructor
  · intro he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
    have hs' : s ⊆ badPrimes q := Finset.mem_powerset.mp hs
    have hne : (∏ p ∈ s, p) ≠ ⊥ := by
      change (∏ p ∈ s, p) ≠ 0
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      exact ((mem_badPrimes hq).mp (hs' hp)).1.ne_zero
    refine ⟨hne, ?_, ?_⟩
    · exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne).mpr
        (by rw [factors_prod_subset hq hs']; exact s.nodup)
    · intro p hprime hp
      have hmem := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hne).mpr
        ⟨hprime, hp⟩
      rw [factors_prod_subset hq hs'] at hmem
      exact ((mem_badPrimes hq).mp (hs' (Finset.mem_def.mpr hmem))).2
  · rintro ⟨he, hsf, hsup⟩
    obtain ⟨s, ⟨hs, rfl⟩, _⟩ := supported_subset hq he hsf hsup
    exact Finset.mem_image.mpr ⟨s, Finset.mem_powerset.mpr hs, rfl⟩

theorem badPart_mem_squarefreeBadPool {q I : Ideal (𝓞 F)}
    (hq : q ≠ ⊥) (hI : I ≠ ⊥) (hsf : Squarefree I) :
    badPart q I ∈ squarefreeBadPool q := by
  exact (mem_squarefreeBadPool hq).mpr ⟨(bad_good_factorization hq hI).1,
    (squarefree_bad_good hq hI hsf).1, (bad_good_factorization hq hI).2.2.2.2⟩

end DedekindZetaZeroFree.LargeSieve.Bilinear

end
