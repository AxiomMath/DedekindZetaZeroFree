module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PrimeClassFactorization
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PositivePrimeProducts
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupFinite

@[expose] public section

noncomputable section

open scoped NumberField Classical

open IsDedekindDomain

namespace DedekindZetaZeroFree.AbelianQuotient

theorem exists_integral_inverse_rayIdealClass
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (c : RayIdealClass K m hm) :
    ∃ a : Ideal (𝓞 K), a ≠ ⊥ ∧ a ⊔ m = ⊤ ∧
      rayIdealClass K m hm a = some (c⁻¹) := by
  let μ := narrowIdealModulus K m hm
  let V := {v : HeightOneSpectrum (𝓞 K) // v ∉ μ.finitePart.support}
  let : Finite (RayIdealClass K m hm) := ClassFieldTheory.rayClassGroup_finite K μ
  obtain ⟨s, e, he⟩ := rayClassFinitePrimeFactorization K μ c⁻¹
  have key : ∀ v : V, ∃ n : ℕ,
      (ClassFieldTheory.rayClassOfFinitePrime μ v.val v.property) ^ n =
        (ClassFieldTheory.rayClassOfFinitePrime μ v.val v.property) ^ e v := by
    intro v
    have hmem : (ClassFieldTheory.rayClassOfFinitePrime μ v.val v.property) ^ e v ∈
        Submonoid.powers (ClassFieldTheory.rayClassOfFinitePrime μ v.val v.property) := by
      rw [mem_powers_iff_mem_zpowers]
      exact ⟨e v, rfl⟩
    obtain ⟨n, hn⟩ := hmem
    exact ⟨n, hn⟩
  choose n hn using key
  obtain ⟨hne, hcop, hcls⟩ := rayPositivePrimeProduct K m hm s n
  refine ⟨∏ v ∈ s, v.val.asIdeal ^ n v, hne, hcop, ?_⟩
  rw [hcls, he]
  congr 1
  exact Finset.prod_congr rfl fun v _ => hn v

theorem exists_ray_congruence_basepoint
    (K : Type) [Field K] [NumberField K]
    (m a : Ideal (𝓞 K)) (hcoprime : a ⊔ m = ⊤) :
    ∃ b : 𝓞 K, b ∈ a ∧ b - 1 ∈ m := by
  obtain ⟨b, hb, d, hd, hbd⟩ := (Ideal.isCoprime_iff_sup_eq.mpr hcoprime).exists
  refine ⟨b, hb, ?_⟩
  have h : b - 1 = -d := by rw [← hbd]; ring
  rw [h]
  exact m.neg_mem hd

end DedekindZetaZeroFree.AbelianQuotient

end
