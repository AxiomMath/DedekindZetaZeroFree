module

public import DedekindZetaZeroFree.Arithmetic.Ideals.MultiplicativeWeightEncoding

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField BigOperators

private lemma norm_extendByZero {α β E : Type*} [SeminormedAddCommGroup E] (e : α → β)
    (he : Function.Injective e) (f : α → E) (b : β) :
    ‖Odlyzko.extendByZero e f b‖ = Odlyzko.extendByZero e (fun a => ‖f a‖) b := by
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    rw [Odlyzko.extendByZero_apply e he f a,
      Odlyzko.extendByZero_apply e he (fun a => ‖f a‖) a]
  · rw [Odlyzko.extendByZero_eq_zero_of_not_mem_range e f hb,
      Odlyzko.extendByZero_eq_zero_of_not_mem_range e (fun a => ‖f a‖) hb, norm_zero]

theorem genericIdealEulerProduct
    (K : Type*) [Field K] [NumberField K]
    (g : Ideal (𝓞 K) →*₀ ℂ)
    (hg : Summable (fun I : Ideal (𝓞 K) => ‖g I‖)) :
    HasProd
      (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (1 - g P.asIdeal)⁻¹)
      (∑' I : Ideal (𝓞 K), g I) := by
  obtain ⟨F, hF1, hF2⟩ := multiplicativeIdealEncoding K g
  have hsumm_nz : Summable (fun I : Odlyzko.NonzeroIdeal K => ‖g (I : Ideal (𝓞 K))‖) :=
    hg.comp_injective Subtype.val_injective
  have hnorm : ∀ n, ‖F n‖ = Odlyzko.extendByZero (Odlyzko.idealPrimeCode K)
      (fun I : Odlyzko.NonzeroIdeal K => ‖g (I : Ideal (𝓞 K))‖) n := by
    intro n
    rw [hF1 n]
    exact norm_extendByZero _ (Odlyzko.idealPrimeCode_injective K) _ n
  have hsumm_F : Summable (fun n => ‖F n‖) := by
    rw [show (fun n => ‖F n‖) = Odlyzko.extendByZero (Odlyzko.idealPrimeCode K)
        (fun I : Odlyzko.NonzeroIdeal K => ‖g (I : Ideal (𝓞 K))‖) from funext hnorm]
    exact Odlyzko.summable_extendByZero _ (Odlyzko.idealPrimeCode_injective K) hsumm_nz
  have hsub : Function.support g ⊆ {I : Ideal (𝓞 K) | I ≠ 0} := by
    intro I hI h0
    exact hI (by rw [h0, map_zero])
  have hsumm_nz_g : Summable (fun I : Odlyzko.NonzeroIdeal K => g (I : Ideal (𝓞 K))) :=
    (hg.of_norm).comp_injective Subtype.val_injective
  have hts : (∑' I : Odlyzko.NonzeroIdeal K, g (I : Ideal (𝓞 K))) =
      ∑' I : Ideal (𝓞 K), g I := tsum_subtype_eq_of_support_subset hsub
  have hhasSum_nz : HasSum (fun I : Odlyzko.NonzeroIdeal K => g (I : Ideal (𝓞 K)))
      (∑' I : Ideal (𝓞 K), g I) := by
    have h := hsumm_nz_g.hasSum
    rw [hts] at h
    exact h
  have hhasSum_F : HasSum (fun n => F n) (∑' I : Ideal (𝓞 K), g I) := by
    rw [show (fun n => F n) = Odlyzko.extendByZero (Odlyzko.idealPrimeCode K)
        (fun I : Odlyzko.NonzeroIdeal K => g (I : Ideal (𝓞 K))) from funext hF1]
    exact Odlyzko.hasSum_extendByZero _ (Odlyzko.idealPrimeCode_injective K) hhasSum_nz
  have htsum : (∑' n, F n) = ∑' I : Ideal (𝓞 K), g I := hhasSum_F.tsum_eq
  have hEuler : HasProd (fun p : Nat.Primes => (1 - F p)⁻¹) (∑' n, F n) :=
    EulerProduct.eulerProduct_completely_multiplicative_hasProd hsumm_F
  have hout : ∀ p : Nat.Primes, p ∉ Set.range (Odlyzko.primeIdealCodeEmbedding K) →
      (1 - F p)⁻¹ = 1 := by
    intro p hp
    have hnone : Odlyzko.primeIdealAtCode K (p : ℕ) = none := by
      cases h : Odlyzko.primeIdealAtCode K (p : ℕ) with
      | none => rfl
      | some P =>
          exact absurd ⟨P, Subtype.ext ((Odlyzko.primeIdealAtCode_eq_some_iff K).1 h)⟩ hp
    rw [hF2 p, hnone]
    simp
  have hcodes : HasProd ((fun p : Nat.Primes => (1 - F p)⁻¹) ∘ Odlyzko.primeIdealCodeEmbedding K)
      (∑' n, F n) :=
    ((Odlyzko.primeIdealCodeEmbedding K).injective.hasProd_iff hout).2 hEuler
  refine (htsum ▸ hcodes).congr_fun (fun P => ?_)
  simp only [Function.comp_apply]
  have hval : (Odlyzko.primeIdealCodeEmbedding K P : ℕ) = Odlyzko.primeIdealCode K P := rfl
  rw [hF2 (Odlyzko.primeIdealCodeEmbedding K P), hval,
    Odlyzko.primeIdealAtCode_primeIdealCode]
  simp

end DedekindZetaZeroFree.AbelianQuotient
