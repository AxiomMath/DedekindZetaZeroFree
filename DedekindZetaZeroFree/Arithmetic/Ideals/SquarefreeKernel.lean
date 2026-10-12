module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve.UniversalB2

theorem canonical_kernel_extraction
    {F : Type} [Field F] [NumberField F]
    (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) :
    squarefreeKernel a ≠ ⊥ ∧ Squarefree (squarefreeKernel a) ∧
      squarefreeKernel a ∣ a ∧
      ∃ t : Ideal (𝓞 F), t ≠ ⊥ ∧ a = squarefreeKernel a * t ^ 2 := by
  classical
  let v := UniqueFactorizationMonoid.normalizedFactors a
  let S := v.toFinset.filter (fun p => v.count p % 2 = 1)
  let t := ∏ p ∈ v.toFinset, p ^ (v.count p / 2)
  have hp (p : Ideal (𝓞 F)) (h : p ∈ v) : Prime p :=
    UniqueFactorizationMonoid.prime_of_normalized_factor p h
  have hkernel : squarefreeKernel a = ∏ p ∈ S, p := by
    simp only [squarefreeKernel, if_neg ha]
    rfl
  have hk0 : squarefreeKernel a ≠ ⊥ := by
    rw [hkernel]
    exact Finset.prod_ne_zero_iff.mpr fun p h =>
      (hp p (Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1)).ne_zero
  have ht0 : t ≠ ⊥ := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p h
    exact pow_ne_zero _ (hp p (Multiset.mem_toFinset.mp h)).ne_zero
  have hnf : UniqueFactorizationMonoid.normalizedFactors (squarefreeKernel a) = S.val := by
    rw [hkernel, Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq]
    · simp only [normalize_eq, Multiset.map_id']
    · intro p h
      exact (hp p (Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1)).irreducible
  have hsf : Squarefree (squarefreeKernel a) := by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hk0).mpr
    rw [hnf]
    exact S.nodup
  have heq : a = squarefreeKernel a * t ^ 2 := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self ha, Finset.prod_multiset_count]
    change (∏ p ∈ v.toFinset, p ^ v.count p) = squarefreeKernel a * t ^ 2
    rw [hkernel, Finset.prod_filter]
    change (∏ p ∈ v.toFinset, p ^ v.count p) =
      (∏ p ∈ v.toFinset, if v.count p % 2 = 1 then p else 1) *
        (∏ p ∈ v.toFinset, p ^ (v.count p / 2)) ^ 2
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [← pow_mul]
    have hn : v.count p = v.count p % 2 + v.count p / 2 * 2 := by omega
    nth_rw 1 [hn]
    rw [pow_add]
    congr 1
    by_cases h : v.count p % 2 = 1
    · simp [h]
    · have hzero : v.count p % 2 = 0 := by omega
      simp [h, hzero]
  exact ⟨hk0, hsf, ⟨t ^ 2, heq⟩, t, ht0, heq⟩

end DedekindZetaZeroFree.LargeSieve.Sieve.UniversalB2

end
