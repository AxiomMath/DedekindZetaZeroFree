module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.SigmaFourKernelsAndReindexing
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.PositiveQuadraticMass
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.UniformEulerDecay
public import DedekindZetaZeroFree.Arithmetic.Ideals.ScaledNormSeriesBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedEulerDeletion

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff BigOperators
open UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.LargeSieve.Bilinear

variable {F : Type} [Field F] [NumberField F]

def sigma4DyadicRows (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (K B : ℝ) : Finset (Ideal (𝓞 F)) :=
  (DedekindZetaZeroFree.LargeSieve.Sieve.paperShell F m B).filter (fun a => (Ideal.absNorm a : ℝ) ≤ K)

def sigma4Rho (j : Ideal (𝓞 F)) : ℝ :=
  ∏ p ∈ badPrimes j, (1 - 1 / (Ideal.absNorm p : ℝ))

theorem primeToSquarefreeKernel_eq_of_coprime (c I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hcop : I ⊔ c = ⊤) :
    primeToSquarefreeKernel c I = DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I := by
  classical
  haveI : Subsingleton (Ideal (𝓞 F))ˣ := ⟨fun u v => by
    refine Units.ext ?_
    rw [Ideal.isUnit_iff.mp u.isUnit, Ideal.isUnit_iff.mp v.isUnit]⟩
  set S : Finset (Ideal (𝓞 F)) :=
    (normalizedFactors I).toFinset.filter
      (fun p => (normalizedFactors I).count p % 2 = 1) with hSdef
  have hker : DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I = ∏ p ∈ S, p := by
    rw [DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel, if_neg hI]
  have hmem : ∀ p ∈ S, p ∈ normalizedFactors I ∧ (normalizedFactors I).count p % 2 = 1 := by
    intro p hp
    rw [hSdef, Finset.mem_filter, Multiset.mem_toFinset] at hp
    exact hp
  have hprime : ∀ p ∈ S, Prime p := fun p hp =>
    prime_of_normalized_factor p (hmem p hp).1
  have hkerne : DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I ≠ ⊥ := by
    rw [hker]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => (hprime p hp).ne_zero
  have hnf : normalizedFactors (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I) = S.val := by
    rw [hker]
    simpa using (normalizedFactors_prod_of_prime (m := S.val)
      fun p hp => hprime p (by simpa using hp))
  have hsq : Squarefree (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I) := by
    rw [squarefree_iff_nodup_normalizedFactors hkerne, hnf]
    exact S.nodup
  have hdvd : DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I ∣ I := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors hkerne hI, hnf]
    refine Multiset.le_iff_count.mpr fun p => ?_
    by_cases hp : p ∈ S
    · have h1 : Multiset.count p S.val = 1 := Multiset.count_eq_one_of_mem S.nodup hp
      have h2 : 1 ≤ Multiset.count p (normalizedFactors I) := by
        have := (hmem p hp).2
        omega
      omega
    · have h0 : Multiset.count p S.val = 0 :=
        Multiset.count_eq_zero.mpr fun hc => hp (by simpa using hc)
      omega
  have hrad : radical (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I) =
      DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I := by
    have hass := radical_associated (hsq.isRadical) hkerne
    exact le_antisymm (Ideal.dvd_iff_le.mp hass.symm.dvd) (Ideal.dvd_iff_le.mp hass.dvd)
  have hfilter : ∀ p ∈ (normalizedFactors (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I)).toFinset,
      ¬ p ∣ c := by
    intro p hp
    have hpmem : p ∈ normalizedFactors (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I) :=
      Multiset.mem_toFinset.mp hp
    have hpprime : Prime p := prime_of_normalized_factor p hpmem
    have hpdvd : p ∣ DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I := dvd_of_mem_normalizedFactors hpmem
    intro hpc
    have h1 : I ≤ p := Ideal.dvd_iff_le.mp (hpdvd.trans hdvd)
    have h2 : c ≤ p := Ideal.dvd_iff_le.mp hpc
    have h3 : (⊤ : Ideal (𝓞 F)) ≤ p := by rw [← hcop]; exact sup_le h1 h2
    have h4 : p = ⊤ := top_le_iff.mp h3
    exact hpprime.not_isUnit (Ideal.isUnit_iff.mpr h4)
  rw [primeToSquarefreeKernel, Finset.filter_true_of_mem hfilter]
  have : (∏ p ∈ (normalizedFactors (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I)).toFinset, p)
      = radical (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I) := by
    rw [radical, primeFactors]
    rfl
  rw [this, hrad]

end DedekindZetaZeroFree.LargeSieve.Bilinear

end
