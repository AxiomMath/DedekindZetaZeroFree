module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralNarrowCongruence

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.AbelianQuotient

theorem rayDenominatorIdealCoprime
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (x : Kˣ)
    (hx : ClassFieldTheory.IsRayCongruent (narrowIdealModulus K m hm) x)
    (D : Ideal (𝓞 K))
    (hD : ∀ d : 𝓞 K, d ∈ D ↔ ∃ a : 𝓞 K, (a : K) = (d : K) * (x : K)) :
    D ⊔ m = ⊤ := by
  rw [← Ideal.isCoprime_iff_sup_eq]
  refine Ideal.coprime_of_no_prime_ge fun P hDP hmP hPprime => ?_
  have hPne : P ≠ ⊥ := fun h => hm (le_bot_iff.mp (h ▸ hmP))
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, hPprime, hPne⟩
  have hv : v ∈ (narrowIdealModulus K m hm).finitePart.support := by
    rw [narrowModulus_support_iff K m hm v]
    exact hmP
  obtain ⟨n, d, hnd⟩ :=
    v.exists_primeCompl_mul_eq_of_integer (x : K)
      (narrowRayCongruent_valuation_le_one K m hm x hx v hv)
  exact d.property (hDP ((hD (d : 𝓞 K)).mpr ⟨n, by simpa [mul_comm] using hnd.symm⟩))

end DedekindZetaZeroFree.AbelianQuotient

end
