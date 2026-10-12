module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Cutoffs.NormalizedCharactersAndMoebiusSums

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference
open SplitData
noncomputable section
variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
  [Subsingleton Rˣ]

private theorem nodup_prod_eq_finset_prod (l : Multiset R) (hl : l.Nodup) :
    l.prod = ∏ x ∈ l.toFinset, x := by
  rw [Finset.prod_multiset_count]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Multiset.count_eq_one_of_mem hl (Multiset.mem_toFinset.mp hx), pow_one]

private theorem moebius_finset_prod_prime (S : Finset R) (hS : ∀ p ∈ S, Prime p) :
    UniqueFactorizationMonoid.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hSa : Prime a := hS a (Finset.mem_insert_self a S)
    have hS' : ∀ p ∈ S, Prime p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hrel : IsRelPrime a (∏ p ∈ S, p) := by
      refine hSa.irreducible.isRelPrime_iff_not_dvd.mpr ?_
      rw [Prime.dvd_finsetProd_iff hSa]
      rintro ⟨b, hb, hdvd⟩
      exact ha (by rw [(prime_dvd_prime_iff_eq hSa (hS' b hb)).mp hdvd]; exact hb)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ, hrel.moebius_mul,
      ih hS', hSa.irreducible.moebius_eq]
    ring

theorem squarefree_divisor_dictionary (g : R) (hg0 : g ≠ 0) (hg : Squarefree g) :
    let P := (UniqueFactorizationMonoid.factors g).toFinset
    (∀ p ∈ P, Prime p) ∧
    (∏ p ∈ P, p) = g ∧
    divisors g = P.powerset.image (fun S => ∏ p ∈ S, p) ∧
    Set.InjOn (fun S : Finset R => ∏ p ∈ S, p) (↑P.powerset : Set (Finset R)) ∧
    (∀ S ∈ P.powerset,
      UniqueFactorizationMonoid.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card) ∧
    (∀ d : R, d ∈ divisors g ↔ d ∣ g) := by
  classical
  have hnd : (UniqueFactorizationMonoid.factors g).Nodup := by
    rw [UniqueFactorizationMonoid.factors_eq_normalizedFactors g]
    exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hg0).mp hg
  have hprod : (UniqueFactorizationMonoid.factors g).prod = g :=
    associated_iff_eq.mp (UniqueFactorizationMonoid.factors_prod hg0)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro p hp
    exact UniqueFactorizationMonoid.prime_of_factor p (Multiset.mem_toFinset.mp hp)
  ·
    rw [← nodup_prod_eq_finset_prod (UniqueFactorizationMonoid.factors g) hnd, hprod]
  ·
    rw [divisors, if_neg hg0]
    ext d
    simp only [Finset.mem_image, Multiset.mem_toFinset, Multiset.mem_powerset,
      Finset.mem_powerset]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.toFinset,
        Multiset.toFinset_subset.mpr ((Multiset.le_iff_subset (Multiset.nodup_of_le hm hnd)).mp hm),
        (nodup_prod_eq_finset_prod m (Multiset.nodup_of_le hm hnd)).symm⟩
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S.val, ?_, ?_⟩
      · rw [Multiset.le_iff_subset S.nodup, ← Multiset.toFinset_subset, Finset.val_toFinset]
        exact hS
      · rw [nodup_prod_eq_finset_prod S.val S.nodup, Finset.val_toFinset]
  ·
    intro S hS T hT heq
    simp only [SetLike.mem_coe, Finset.mem_powerset] at hS hT
    have hkey : ∀ p ∈ (UniqueFactorizationMonoid.factors g).toFinset, ∀ U ⊆
        (UniqueFactorizationMonoid.factors g).toFinset,
        (p ∣ ∏ q ∈ U, q ↔ p ∈ U) := by
      intro p hp U hU
      refine ⟨fun hdvd => ?_, fun hmem => Finset.dvd_prod_of_mem _ hmem⟩
      rw [Prime.dvd_finsetProd_iff (UniqueFactorizationMonoid.prime_of_factor p
        (Multiset.mem_toFinset.mp hp))] at hdvd
      obtain ⟨q, hqU, hpq⟩ := hdvd
      rw [(prime_dvd_prime_iff_eq (UniqueFactorizationMonoid.prime_of_factor p
        (Multiset.mem_toFinset.mp hp)) (UniqueFactorizationMonoid.prime_of_factor q
        (Multiset.mem_toFinset.mp (hU hqU)))).mp hpq]
      exact hqU
    have heq' : (∏ q ∈ S, q) = (∏ q ∈ T, q) := heq
    ext p
    by_cases hp : p ∈ (UniqueFactorizationMonoid.factors g).toFinset
    · rw [← hkey p hp S hS, ← hkey p hp T hT, heq']
    · exact iff_of_false (fun h => hp (hS h)) (fun h => hp (hT h))
  ·
    intro S hS
    rw [Finset.mem_powerset] at hS
    exact moebius_finset_prod_prime S fun p hp =>
      UniqueFactorizationMonoid.prime_of_factor p (Multiset.mem_toFinset.mp (hS hp))
  ·
    intro d
    rw [divisors, if_neg hg0, Finset.mem_image]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [Multiset.mem_toFinset, Multiset.mem_powerset] at hm
      rw [← hprod]
      obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp hm
      rw [ht, Multiset.prod_add]
      exact dvd_mul_right _ _
    · intro hd
      have hd0 : d ≠ 0 := fun h => hg0 (by rw [h] at hd; exact zero_dvd_iff.mp hd)
      refine ⟨UniqueFactorizationMonoid.factors d, ?_, ?_⟩
      · rw [Multiset.mem_toFinset, Multiset.mem_powerset]
        rw [UniqueFactorizationMonoid.factors_eq_normalizedFactors,
          UniqueFactorizationMonoid.factors_eq_normalizedFactors]
        exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
          hd0 hg0).mp hd
      · exact associated_iff_eq.mp (UniqueFactorizationMonoid.factors_prod hd0)

end
end DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference
