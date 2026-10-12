module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

variable {F : Type} [Field F] [NumberField F] {a : Ideal (𝓞 F)}

theorem squarefreeKernel_eq_self (ha : Squarefree a) : squarefreeKernel a = a := by
  have ha0 : a ≠ ⊥ := ha.ne_zero
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors a).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors ha0).1 ha
  have hfilter :
      (UniqueFactorizationMonoid.normalizedFactors a).toFinset.filter
          (fun p => (UniqueFactorizationMonoid.normalizedFactors a).count p % 2 = 1)
        = (UniqueFactorizationMonoid.normalizedFactors a).toFinset := by
    apply Finset.filter_true_of_mem
    intro p hp
    have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors a :=
      Multiset.mem_toFinset.1 hp
    have h1 : (UniqueFactorizationMonoid.normalizedFactors a).count p = 1 :=
      Multiset.count_eq_one_of_mem hnodup hp'
    rw [h1]
  rw [squarefreeKernel, if_neg ha0, hfilter, Finset.prod_eq_multiset_prod]
  rw [Multiset.map_id', Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnodup]
  exact Ideal.prod_normalizedFactors_eq_self ha0

theorem s_eq_absNorm_of_squarefree (ha : Squarefree a) :
    s a = (Ideal.absNorm a : ℝ) := by
  rw [s, squarefreeKernel_eq_self ha]

end DedekindZetaZeroFree.LargeSieve.Sieve

end
