module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoprimeForms.WeightedEnergyAndPrimeSupportCost
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

open scoped NumberField Classical

private lemma primeSupportCost_le_divisorCount {F : Type} [Field F] [NumberField F]
    (u : Ideal (𝓞 F)) (hu : u ≠ ⊥) :
    primeSupportCost u ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisorCount u : ℝ) := by
  classical
  set m := UniqueFactorizationMonoid.normalizedFactors u with hm
  set S := m.toFinset with hS
  have hmem : ∀ p : Ideal (𝓞 F), p ∈ S ↔ p ∈ m := fun p => Multiset.mem_toFinset
  have hprime : ∀ p ∈ S, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p ((hmem p).mp hp)
  have hnorm : ∀ p ∈ S, normalize p = p := fun p hp =>
    UniqueFactorizationMonoid.normalize_normalized_factor p ((hmem p).mp hp)
  have key : ∀ s : Finset (Ideal (𝓞 F)), s ⊆ S →
      UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val := by
    intro s hs
    have hirr : ∀ p ∈ s.val, Irreducible p := by
      intro p hp
      exact hprime p (hs (by simpa using hp))
    have h1 := UniqueFactorizationMonoid.normalizedFactors_prod_eq s.val hirr
    have hprod : (∏ p ∈ s, p) = s.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod, h1]
    rw [Multiset.map_congr rfl (fun p hp => hnorm p (hs (by simpa using hp))),
      Multiset.map_id']
  have hinj : Set.InjOn (fun s : Finset (Ideal (𝓞 F)) => ∏ p ∈ s, p)
      (↑S.powerset : Set (Finset (Ideal (𝓞 F)))) := by
    intro s hs t ht hst
    have hssub : s ⊆ S := Finset.mem_powerset.mp hs
    have htsub : t ⊆ S := Finset.mem_powerset.mp ht
    have hsval : UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val :=
      key s hssub
    have htval : UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ t, p) = t.val :=
      key t htsub
    have hst' : (∏ p ∈ s, p) = (∏ p ∈ t, p) := hst
    rw [hst'] at hsval
    exact Finset.val_inj.mp (hsval.symm.trans htval)
  have hmaps : Set.MapsTo (fun s : Finset (Ideal (𝓞 F)) => ∏ p ∈ s, p)
      (↑S.powerset : Set (Finset (Ideal (𝓞 F))))
      (↑(DedekindZetaZeroFree.LargeSieve.idealDivisors u) : Set (Ideal (𝓞 F))) := by
    intro s hs
    change (∏ p ∈ s, p) ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors u
    rw [DedekindZetaZeroFree.LargeSieve.mem_idealDivisors hu]
    have hssub : s ⊆ S := Finset.mem_powerset.mp hs
    have hle : s.val ≤ m := by
      rw [Multiset.le_iff_subset s.nodup]
      intro p hp
      exact (hmem p).mp (hssub (by simpa using hp))
    have hprod : (∏ p ∈ s, p) = s.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod, ← Ideal.prod_normalizedFactors_eq_self hu]
    exact Multiset.prod_dvd_prod_of_le hle
  have hcard : S.powerset.card ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisors u).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hcost : primeSupportCost u = (2 : ℝ) ^ S.card := by
    rw [primeSupportCost, hS, ← hm]
  rw [hcost]
  have hpc : ((S.powerset.card : ℕ) : ℝ) = (2 : ℝ) ^ S.card := by
    rw [Finset.card_powerset]
    push_cast
    ring
  rw [← hpc]
  exact_mod_cast hcard

theorem support_cost_energy_bound
    (F : Type) [Field F] [NumberField F] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (N X : ℝ), 1 ≤ N → 0 < X → X ≤ N →
      ∀ alpha : Ideal (𝓞 F) → ℂ,
        (∑ u ∈ paperShell F c X, primeSupportCost u * ‖alpha u‖ ^ 2) ≤
          C * Real.rpow N ε * energy F c X alpha := by
  obtain ⟨C₀, hC₀1, hC₀⟩ := DedekindZetaZeroFree.LargeSieve.ideal_divisor_count_le_rpow F ε hε
  refine ⟨C₀ * Real.rpow 2 ε, mul_nonneg (le_trans zero_le_one hC₀1)
    (Real.rpow_nonneg (by norm_num) ε), ?_⟩
  intro c N X hN hX hXN alpha
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hC₀0 : (0 : ℝ) ≤ C₀ := le_trans zero_le_one hC₀1
  have hterm : ∀ u ∈ paperShell F c X,
      primeSupportCost u * ‖alpha u‖ ^ 2 ≤
        (C₀ * Real.rpow 2 ε * Real.rpow N ε) * ‖alpha u‖ ^ 2 := by
    intro u hu
    have hmem := (mem_paperShell F c X u).mp hu
    have hune : u ≠ ⊥ := by
      have := hmem.1.ne_zero
      simpa [Ideal.zero_eq_bot] using this
    have hnormle : (Ideal.absNorm u : ℝ) ≤ 2 * N := by
      have h2 : (Ideal.absNorm u : ℝ) ≤ 2 * X := hmem.2.2.2
      nlinarith [hXN]
    have hrpow : (Ideal.absNorm u : ℝ) ^ ε ≤ (2 * N) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hnormle hε.le
    have hcost : primeSupportCost u ≤ C₀ * Real.rpow 2 ε * Real.rpow N ε := by
      calc primeSupportCost u ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisorCount u : ℝ) :=
            primeSupportCost_le_divisorCount u hune
        _ ≤ C₀ * (Ideal.absNorm u : ℝ) ^ ε := hC₀ u
        _ ≤ C₀ * (2 * N) ^ ε := mul_le_mul_of_nonneg_left hrpow hC₀0
        _ = C₀ * Real.rpow 2 ε * Real.rpow N ε := by
              rw [Real.mul_rpow (by norm_num) hNpos.le, mul_assoc]
              rfl
    exact mul_le_mul_of_nonneg_right hcost (sq_nonneg _)
  calc (∑ u ∈ paperShell F c X, primeSupportCost u * ‖alpha u‖ ^ 2)
      ≤ ∑ u ∈ paperShell F c X,
          (C₀ * Real.rpow 2 ε * Real.rpow N ε) * ‖alpha u‖ ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (C₀ * Real.rpow 2 ε * Real.rpow N ε) * energy F c X alpha := by
        simp only [energy, Finset.mul_sum]

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

end
