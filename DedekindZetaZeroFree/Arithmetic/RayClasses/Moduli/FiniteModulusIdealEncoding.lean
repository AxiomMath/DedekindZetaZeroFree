module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClasses

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.AbelianQuotient

def finiteRayModulusIdeal
    (K : Type) [Field K] [NumberField K]
    (f : HeightOneSpectrum (𝓞 K) →₀ ℕ) : Ideal (𝓞 K) :=
  ∏ p ∈ f.support, p.asIdeal ^ f p

theorem finiteRayModulusIdeal_ne_bot
    (K : Type) [Field K] [NumberField K]
    (f : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    finiteRayModulusIdeal K f ≠ ⊥ := by
  change (∏ p ∈ f.support, p.asIdeal ^ f p) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ p.ne_bot)

@[simp] theorem finiteRayModulusIdeal_count
    (K : Type) [Field K] [NumberField K]
    (f : HeightOneSpectrum (𝓞 K) →₀ ℕ) (p : HeightOneSpectrum (𝓞 K)) :
    Multiset.count p.asIdeal (normalizedFactors (finiteRayModulusIdeal K f)) = f p := by
  have hcount (s : Finset (HeightOneSpectrum (𝓞 K))) :
      Multiset.count p.asIdeal (normalizedFactors (∏ q ∈ s, q.asIdeal ^ f q)) =
        ∑ q ∈ s, if p = q then f q else 0 := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, normalizedFactors_one, Multiset.count_zero,
        Finset.sum_empty]
    | @insert q s hq ih =>
      rw [Finset.prod_insert hq, normalizedFactors_mul
        (pow_ne_zero _ q.ne_bot)
        (Finset.prod_ne_zero_iff.mpr (fun r _ => pow_ne_zero _ r.ne_bot)),
        Multiset.count_add, ih, Finset.sum_insert hq,
        q.irreducible.normalizedFactors_pow]
      congr 1
      by_cases hpq : p = q
      · subst q
        simp
      · have hne : p.asIdeal ≠ q.asIdeal := fun h => hpq (HeightOneSpectrum.asIdeal_injective h)
        simp [hpq, hne, Multiset.mem_replicate]
  rw [finiteRayModulusIdeal, hcount]
  by_cases hp : p ∈ f.support
  · simp [Finset.sum_eq_single p, hp]
  · have hz : f p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [Finset.sum_eq_single p, hp, hz]

theorem finiteRayModulusIdeal_coprime
    (K : Type) [Field K] [NumberField K]
    (f : HeightOneSpectrum (𝓞 K) →₀ ℕ) (p : HeightOneSpectrum (𝓞 K)) :
    p.asIdeal ⊔ finiteRayModulusIdeal K f = ⊤ ↔ f p = 0 := by
  have hle : finiteRayModulusIdeal K f ≤ p.asIdeal ↔ f p ≠ 0 := by
    rw [← finiteRayModulusIdeal_count K f p, Multiset.count_ne_zero,
      Ideal.mem_normalizedFactors_iff (finiteRayModulusIdeal_ne_bot K f)]
    simp only [p.isPrime, true_and]
  constructor
  · intro htop
    by_contra hne
    have h := sup_le le_rfl (hle.mpr hne)
    rw [htop] at h
    exact p.isPrime.ne_top (top_unique h)
  · intro hz
    by_contra hne
    have heq := p.isMaximal.eq_of_le hne le_sup_left
    have h := hle.mp (heq ▸ le_sup_right)
    exact h hz

theorem narrowIdealModulus_finiteRayModulusIdeal
    (K : Type) [Field K] [NumberField K]
    (c : ClassFieldTheory.RayClassModulus K) (hc : c.infinitePart = Finset.univ) :
    narrowIdealModulus K (finiteRayModulusIdeal K c.finitePart)
      (finiteRayModulusIdeal_ne_bot K c.finitePart) = c := by
  apply ClassFieldTheory.RayClassModulus.ext
  · ext p
    simp
  · simpa using hc.symm

end DedekindZetaZeroFree.AbelianQuotient

end
