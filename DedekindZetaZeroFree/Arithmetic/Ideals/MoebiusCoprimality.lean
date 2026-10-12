module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets
public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeDivisorsAndPrimeSubsets

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact

open UniqueFactorizationMonoid

private lemma sum_mu {F : Type*} [Field F] [NumberField F]
    (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) :
    (∑ d ∈ idealDivisors a, (moebius d : ℂ)) = if a = ⊤ then 1 else 0 := by
  let r := UniqueFactorizationMonoid.radical a
  have hr : r ≠ ⊥ := radical_ne_zero
  obtain ⟨hp, hprod, hd, hi, hmu, hmem⟩ :=
    DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference.squarefree_divisor_dictionary r hr squarefree_radical
  have heq : idealDivisors r = DedekindZetaZeroFree.LargeSieve.Vendor.CutoffDifference.SplitData.divisors r := by
    ext d
    rw [mem_idealDivisors hr, hmem]
  have hsub : idealDivisors r ⊆ idealDivisors a := by
    intro d hd
    exact (mem_idealDivisors ha).mpr (((mem_idealDivisors hr).mp hd).trans radical_dvd_self)
  have hz : ∀ d ∈ idealDivisors a, d ∉ idealDivisors r → (moebius d : ℂ) = 0 := by
    intro d hd hdr
    have hns : ¬ Squarefree d := by
      intro hs
      apply hdr
      exact (mem_idealDivisors hr).mpr ((dvd_radical_iff hs.isRadical ha).mpr
        ((mem_idealDivisors ha).mp hd))
    simp [moebius_of_not_squarefree hns]
  rw [← Finset.sum_subset hsub hz, heq, hd]
  trans ∑ S ∈ (factors r).toFinset.powerset, (moebius (∏ p ∈ S, p) : ℂ)
  · exact Finset.sum_image hi
  have he : (∑ S ∈ (factors r).toFinset.powerset, (moebius (∏ p ∈ S, p) : ℂ)) =
      ∑ S ∈ (factors r).toFinset.powerset, (-1 : ℂ) ^ S.card := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [hmu S hS]
    push_cast
    rfl
  rw [he]
  have heprod : (∑ S ∈ (factors r).toFinset.powerset, (-1 : ℂ) ^ S.card) =
      ∏ p ∈ (factors r).toFinset, (1 + (-1 : ℂ)) := by
    rw [Finset.prod_one_add]
    simp
  rw [heprod]
  have hP : (factors r).toFinset = ∅ ↔ a = ⊤ := by
    constructor
    · intro h
      have hr1 : r = 1 := hprod.symm.trans
        ((congrArg (fun S : Finset (Ideal (𝓞 F)) => ∏ p ∈ S, p) h).trans (by simp))
      exact Ideal.isUnit_iff.mp ((radical_eq_one_iff.mp hr1).resolve_left ha)
    · intro h
      subst a
      have hr1 : r = 1 := radical_of_isUnit (Ideal.isUnit_iff.mpr rfl)
      rw [hr1]
      simp only [factors_one, Multiset.toFinset_zero]
  by_cases h : a = ⊤
  · rw [hP.mpr h, Finset.prod_empty, if_pos h]
  · have hne : (factors r).toFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (fun he => h (hP.mp he))
    rw [if_neg h]
    simp only [add_neg_cancel]
    obtain ⟨p, hp⟩ := hne
    exact Finset.prod_eq_zero hp rfl
private lemma indicator {F : Type*} [Field F] [NumberField F]
    (m I : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hI : I ≠ ⊥) :
    (∑ d ∈ idealDivisors m, if d ∣ I then (moebius d : ℂ) else 0) =
      if I ⊔ m = ⊤ then 1 else 0 := by
  have hsup : I ⊔ m ≠ ⊥ := fun h => hm (le_bot_iff.mp (h ▸ le_sup_right))
  have heq : (idealDivisors m).filter (fun d => d ∣ I) = idealDivisors (I ⊔ m) := by
    ext d
    simp only [Finset.mem_filter, mem_idealDivisors hm, mem_idealDivisors hsup,
      Ideal.dvd_iff_le, sup_le_iff]
    exact and_comm
  rw [← Finset.sum_filter, heq, sum_mu _ hsup]

theorem coprimeFinsum_eq_moebiusMultiples
    {F : Type*} [Field F] [NumberField F]
    (g : Ideal (𝓞 F) → ℂ)
    (hg : Function.HasFiniteSupport (fun I => if I = ⊥ then 0 else g I))
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ I ⊔ m = ⊤ then g I else 0) =
      ∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ) *
        (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ d ∣ I then g I else 0) := by
  have hg' : (Function.support (fun I => if I = ⊥ then 0 else g I)).Finite := hg
  let S := hg'.toFinset
  have hs (p : Ideal (𝓞 F) → Prop) [DecidablePred p] :
      Function.support (fun I => if I ≠ ⊥ ∧ p I then g I else 0) ⊆ (S : Set (Ideal (𝓞 F))) := by
    intro I h
    have hn : I ≠ ⊥ ∧ p I := by
      by_contra hn
      simp [Function.mem_support, hn] at h
    have hgI : g I ≠ 0 := by simpa only [Function.mem_support, if_pos hn] using h
    change I ∈ hg'.toFinset
    rw [Set.Finite.mem_toFinset]
    simp [Function.mem_support, hn.1, hgI]
  rw [finsum_eq_finsetSum_of_support_subset _ (hs (fun I => I ⊔ m = ⊤))]
  simp_rw [finsum_eq_finsetSum_of_support_subset _ (hs (fun I => _ ∣ I))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hIS
  by_cases hI : I = ⊥
  · simp [hI]
  · have hid := indicator m I hm hI
    have he : (∑ d ∈ idealDivisors m, (moebius d : ℂ) *
        (if I ≠ ⊥ ∧ d ∣ I then g I else 0)) =
        (∑ d ∈ idealDivisors m, if d ∣ I then (moebius d : ℂ) else 0) * g I := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdI : d ∣ I <;> simp [hI, hdI]
    rw [he, hid]
    by_cases hc : I ⊔ m = ⊤ <;> simp [hI, hc]

end DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact

end
