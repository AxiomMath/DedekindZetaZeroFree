module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedSquareLocalResidues
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.CoprimeAndFiniteScaledSummation

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical ContDiff BigOperators Topology
open Filter

namespace DedekindZetaZeroFree.LargeSieve

def idealEulerDeletion {F : Type} [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (_hm : m ≠ ⊥) (s : ℂ) : ℂ :=
  ∑ d ∈ idealDivisors m,
    (UniqueFactorizationMonoid.moebius d : ℂ) * (Ideal.absNorm d : ℂ) ^ (-s)

variable {F : Type} [Field F] [NumberField F]

open UniqueFactorizationMonoid

private lemma subset_prod_factors (m : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 F)))
    (ht : t ⊆ (UniqueFactorizationMonoid.normalizedFactors m).toFinset) :
    UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ t, p) = t.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact UniqueFactorizationMonoid.normalizedFactors_prod_eq_self_of_subset (fun p hp =>
    Multiset.mem_toFinset.mp (ht (Finset.mem_val.mp hp)))
private lemma subset_prod_ne_zero (m : Ideal (𝓞 F)) (t : Finset (Ideal (𝓞 F)))
    (ht : t ⊆ (UniqueFactorizationMonoid.normalizedFactors m).toFinset) : (∏ p ∈ t, p) ≠ ⊥ := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact prod_ne_zero_of_subset_normalizedFactors (fun p hp =>
    Multiset.mem_toFinset.mp (ht (Finset.mem_val.mp hp)))
private lemma norm_prod_cpow (t : Finset (Ideal (𝓞 F))) (z : ℂ) :
    (Ideal.absNorm (∏ p ∈ t, p) : ℂ) ^ z =
      ∏ p ∈ t, (Ideal.absNorm p : ℂ) ^ z := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert p t hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, map_mul, Nat.cast_mul]
    rw [← ih]
    simpa only [Complex.ofReal_natCast] using
      (Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm p))
        (Nat.cast_nonneg (Ideal.absNorm (∏ q ∈ t, q))) z)

theorem idealEulerDeletion_eq_prod (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (s : ℂ) :
    idealEulerDeletion m hm s =
      ∏ p ∈ (UniqueFactorizationMonoid.normalizedFactors m).toFinset,
        (1 - (Ideal.absNorm p : ℂ) ^ (-s)) := by
  let P := (normalizedFactors m).toFinset
  have hprod := Finset.prod_sub (fun _ : Ideal (𝓞 F) => (1 : ℂ))
    (fun p => (Ideal.absNorm p : ℂ) ^ (-s)) P
  simp only [Finset.prod_const_one, mul_one] at hprod
  rw [hprod]
  unfold idealEulerDeletion
  have hrestrict : (∑ d ∈ (idealDivisors m).filter Squarefree,
      (moebius d : ℂ) * (Ideal.absNorm d : ℂ) ^ (-s)) =
      ∑ d ∈ idealDivisors m, (moebius d : ℂ) * (Ideal.absNorm d : ℂ) ^ (-s) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hn
    have hns : ¬ Squarefree d := by simpa [hd] using hn
    simp [moebius_of_not_squarefree hns]
  rw [← hrestrict]
  symm
  apply Finset.sum_bij (fun t _ => ∏ p ∈ t, p)
  · intro t ht
    have hsub : t ⊆ P := Finset.mem_powerset.mp ht
    have hfac := subset_prod_factors m t hsub
    have hne := subset_prod_ne_zero m t hsub
    refine Finset.mem_filter.mpr ⟨(mem_idealDivisors hm).mpr ?_, ?_⟩
    · rw [dvd_iff_normalizedFactors_le_normalizedFactors hne hm, hfac]
      exact (Multiset.le_iff_subset t.nodup).mpr (fun p hp =>
        Multiset.mem_toFinset.mp (hsub (Finset.mem_val.mp hp)))
    · rw [squarefree_iff_nodup_normalizedFactors hne, hfac]
      exact t.nodup
  · intro t ht u hu heq
    have ht' := subset_prod_factors m t (Finset.mem_powerset.mp ht)
    have hu' := subset_prod_factors m u (Finset.mem_powerset.mp hu)
    apply Finset.val_injective
    rw [← ht', ← hu', heq]
  · intro d hd
    obtain ⟨hd, hsf⟩ := Finset.mem_filter.mp hd
    have hd0 := ne_bot_of_mem_idealDivisors hd
    have hn := (squarefree_iff_nodup_normalizedFactors hd0).mp hsf
    refine ⟨(normalizedFactors d).toFinset, ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro p hp
      apply Multiset.mem_toFinset.mpr
      exact Multiset.mem_of_le
        ((dvd_iff_normalizedFactors_le_normalizedFactors hd0 hm).mp
          ((mem_idealDivisors hm).mp hd)) (Multiset.mem_toFinset.mp hp)
    · rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val,
        Multiset.dedup_eq_self.mpr hn]
      exact Ideal.prod_normalizedFactors_eq_self hd0
  · intro t ht
    have hsub : t ⊆ P := Finset.mem_powerset.mp ht
    have hfac := subset_prod_factors m t hsub
    have hne := subset_prod_ne_zero m t hsub
    have hsf : Squarefree (∏ p ∈ t, p) := by
      rw [squarefree_iff_nodup_normalizedFactors hne, hfac]
      exact t.nodup
    rw [hsf.moebius_eq, factors_eq_normalizedFactors, hfac, Int.cast_pow,
      Int.cast_neg, Int.cast_one, norm_prod_cpow]
    rfl

end DedekindZetaZeroFree.LargeSieve

end
