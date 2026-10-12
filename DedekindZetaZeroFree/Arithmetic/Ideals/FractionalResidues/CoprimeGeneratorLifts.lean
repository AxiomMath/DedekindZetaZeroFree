module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.QuotientModule

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

def fractionalResidueLiftIdeal (I : FractionalIdeal R⁰ K) (β : K) :
    FractionalIdeal R⁰ K :=
  FractionalIdeal.spanSingleton R⁰ β * I⁻¹

theorem fractionalResidueGenerator_lift_properties (m : Ideal R)
    (I : FractionalIdeal R⁰ K) (hm : m ≠ ⊥) (hm1 : m ≠ ⊤) (hI : I ≠ 0)
    (z : fractionalResidueModule m I)
    (hz : Function.Surjective (fun k : R ⧸ m => k • z))
    (β : K) (hβ : β ∈ I)
    (hlift : Submodule.Quotient.mk (p := fractionalResidueDenominator m I)
      ⟨β, hβ⟩ = z) :
    β ≠ 0 ∧
      (m : FractionalIdeal R⁰ K) * I + FractionalIdeal.spanSingleton R⁰ β = I ∧
      fractionalResidueLiftIdeal I β ≠ 0 ∧
      fractionalResidueLiftIdeal I β ≤ 1 ∧
      (m : FractionalIdeal R⁰ K) + fractionalResidueLiftIdeal I β = 1 := by
  have hspan : FractionalIdeal.spanSingleton R⁰ β ≤ I :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hβ
  have heq : (m : FractionalIdeal R⁰ K) * I +
      FractionalIdeal.spanSingleton R⁰ β = I := by
    apply le_antisymm
    · exact add_le (fractionalResidue_mul_le m I) hspan
    · intro x hx
      obtain ⟨k, hk⟩ := hz (Submodule.Quotient.mk
        (p := fractionalResidueDenominator m I) ⟨x, hx⟩)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective k
      dsimp only at hk
      rw [← hlift, fractionalResidueModule_mk_smul_mk] at hk
      have hd := (Submodule.Quotient.eq (fractionalResidueDenominator m I)).mp hk.symm
      have hd' : x - r • β ∈ (m : FractionalIdeal R⁰ K) * I := hd
      apply (FractionalIdeal.mem_add _ _ _).mpr
      exact ⟨x - r • β, hd', r • β,
        (FractionalIdeal.mem_spanSingleton R⁰).mpr ⟨r, rfl⟩, sub_add_cancel _ _⟩
  have hsum : (m : FractionalIdeal R⁰ K) + fractionalResidueLiftIdeal I β = 1 := by
    have h := congrArg (fun J : FractionalIdeal R⁰ K => J * I⁻¹) heq
    simpa [add_mul, mul_assoc, mul_inv_cancel₀ hI, fractionalResidueLiftIdeal] using h
  have hne : β ≠ 0 := by
    intro hzero
    have hm' : (m : FractionalIdeal R⁰ K) = 1 := by
      simpa [fractionalResidueLiftIdeal, hzero] using hsum
    apply hm1
    apply FractionalIdeal.coeIdeal_injective (K := K)
    simpa using hm'
  refine ⟨hne, heq, ?_, ?_, hsum⟩
  · exact mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hne) (inv_ne_zero hI)
  · change FractionalIdeal.spanSingleton R⁰ β * I⁻¹ ≤ 1
    calc
      FractionalIdeal.spanSingleton R⁰ β * I⁻¹ ≤ I * I⁻¹ := mul_le_mul_of_nonneg_right hspan (FractionalIdeal.zero_le _)
      _ = 1 := mul_inv_cancel₀ hI

theorem fractionalResidueGenerator_lift_coprime_ideal (m : Ideal R)
    (I : FractionalIdeal R⁰ K) (hm : m ≠ ⊥) (hm1 : m ≠ ⊤) (hI : I ≠ 0)
    (z : fractionalResidueModule m I)
    (hz : Function.Surjective (fun k : R ⧸ m => k • z))
    (β : K) (hβ : β ∈ I)
    (hlift : Submodule.Quotient.mk (p := fractionalResidueDenominator m I)
      ⟨β, hβ⟩ = z) :
    ∃ b : Ideal R,
      (b : FractionalIdeal R⁰ K) = fractionalResidueLiftIdeal I β ∧
      b ≠ ⊥ ∧ m ⊔ b = ⊤ ∧
      FractionalIdeal.spanSingleton R⁰ β = (b : FractionalIdeal R⁰ K) * I := by
  obtain ⟨_, _, hbne, hble, hsum⟩ :=
    fractionalResidueGenerator_lift_properties m I hm hm1 hI z hz β hβ hlift
  obtain ⟨b, hb⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hble
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · intro hzero
    apply hbne
    rw [← hb, hzero, FractionalIdeal.coeIdeal_bot]
  · apply FractionalIdeal.coeIdeal_injective (K := K)
    simpa only [FractionalIdeal.coeIdeal_sup, FractionalIdeal.coeIdeal_top, hb] using hsum
  · rw [hb, fractionalResidueLiftIdeal, mul_assoc, inv_mul_cancel₀ hI, mul_one]

end

end DedekindZetaZeroFree.Hecke
