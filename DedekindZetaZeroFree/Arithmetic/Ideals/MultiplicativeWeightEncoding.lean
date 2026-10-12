module

public import DedekindZetaZeroFree.LFunctions.Dedekind.PrimeIdealEulerProduct

@[expose] public section

/-
Adapts the encoding argument of LeanPool/lean-pool
(commit 68aa6ee63d20ad76bcc15f595adfc72949991f06, Apache-2.0,
`LeanPool/Odlyzko/DedekindZeta/PrimeIdealEulerProduct.lean`,
original copyright The FLT Project / Imperial College London).
-/

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField

open Ideal IsDedekindDomain

open DedekindZetaZeroFree.Odlyzko

theorem multiplicativeIdealEncoding
    (K : Type*) [Field K] [NumberField K]
    (g : Ideal (𝓞 K) →*₀ ℂ) :
    ∃ f : ℕ →*₀ ℂ,
      (∀ n : ℕ, f n =
        Odlyzko.extendByZero (Odlyzko.idealPrimeCode K)
          (fun I : Odlyzko.NonzeroIdeal K => g (I : Ideal (𝓞 K))) n) ∧
      (∀ p : Nat.Primes, f p =
        (Odlyzko.primeIdealAtCode K (p : ℕ)).elim 0 (fun P => g P.asIdeal)) := by
  classical
  let a : ℕ → ℂ := fun n =>
    (Odlyzko.primeIdealAtCode K n).elim 0 (fun P => g P.asIdeal)
  have ha_code : ∀ P : HeightOneSpectrum (𝓞 K),
      a (Odlyzko.primeIdealCode K P) = g P.asIdeal := by
    intro P
    simp [a, Odlyzko.primeIdealAtCode_primeIdealCode]
  have ha_ne : ∀ p, a p ≠ 0 → Odlyzko.primeIdealAtCode K p ≠ none := by
    intro p hp h
    exact hp (by simp [a, h])

  have h_exists_code : ∀ {b : ℕ → ℂ},
      (∀ p, b p ≠ 0 → Odlyzko.primeIdealAtCode K p ≠ none) →
      ∀ {n : ℕ}, Odlyzko.primeValueHom b n ≠ 0 →
      ∃ I : Odlyzko.NonzeroIdeal K, Odlyzko.idealPrimeCode K I = n := by
    intro b hb n hn
    have hn0 : n ≠ 0 := by
      intro h; exact hn (by rw [h, map_zero])
    refine Odlyzko.exists_idealPrimeCode_eq_of_primeFactors K hn0 ?_
    intro p hp
    have hpsupp : p ∈ n.factorization.support := by
      simp_all [Multiset.mem_coe, Nat.mem_primeFactorsList', Nat.mem_primeFactors]
    have hprod : n.factorization.prod (fun q e => b q ^ e) ≠ 0 := by
      simpa [Odlyzko.primeValueHom, hn0] using hn
    have hne := (Finsupp.prod_ne_zero_iff.mp hprod) p hpsupp
    have hbp : b p ≠ 0 :=
      (pow_ne_zero_iff (Finsupp.mem_support_iff.mp hpsupp)).mp hne
    cases h : Odlyzko.primeIdealAtCode K p with
    | none => exact absurd (hb p hbp) (by simp [h])
    | some P => exact ⟨P, (Odlyzko.primeIdealAtCode_eq_some_iff K).1 h⟩

  have h_in_range : ∀ I : Odlyzko.NonzeroIdeal K,
      Odlyzko.primeValueHom a (Odlyzko.idealPrimeCode K I) = g (I : Ideal (𝓞 K)) := by
    intro I
    have hcoe : ((Odlyzko.idealPrimeFactors K I).map
        (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal)).prod = (I : Ideal (𝓞 K)) := by
      rw [← Odlyzko.idealOfPrimeFactors_coe]
      exact congrArg (fun J : Odlyzko.NonzeroIdeal K => (J : Ideal (𝓞 K)))
        (Odlyzko.idealOfPrimeFactors_idealPrimeFactors K I)
    have hmap : ((Odlyzko.idealPrimeFactors K I).map (Odlyzko.primeIdealCode K)).map a
        = (Odlyzko.idealPrimeFactors K I).map (fun P => g P.asIdeal) := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro P _
      exact ha_code P
    rw [Odlyzko.idealPrimeCode,
      Odlyzko.primeValueHom_multiset_prod_of_prime a
        (Odlyzko.prime_mem_idealPrimeCode_factors K I),
      hmap, ← hcoe, map_multiset_prod g, Multiset.map_map]
    rfl
  refine ⟨Odlyzko.primeValueHom a, ?_, ?_⟩
  · intro n
    by_cases hmem : n ∈ Set.range (Odlyzko.idealPrimeCode K)
    · obtain ⟨I, hI⟩ := hmem
      rw [← hI, Odlyzko.extendByZero_apply (Odlyzko.idealPrimeCode K)
        (Odlyzko.idealPrimeCode_injective K)
        (fun I : Odlyzko.NonzeroIdeal K => g (I : Ideal (𝓞 K))) I]
      exact h_in_range I
    · rw [Odlyzko.extendByZero_eq_zero_of_not_mem_range _ _ hmem]
      by_contra hne
      obtain ⟨I, hI⟩ := h_exists_code ha_ne hne
      exact hmem ⟨I, hI⟩
  · intro p
    exact Odlyzko.primeValueHom_apply_prime_subtype a p

end DedekindZetaZeroFree.AbelianQuotient
