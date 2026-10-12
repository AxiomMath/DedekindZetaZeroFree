module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.IntegralRayCongruence
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.NarrowModulusPrimePowers
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.NarrowRealPositivity

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.AbelianQuotient

theorem integralNarrowRayCongruence
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    ClassFieldTheory.IsRayCongruent (narrowIdealModulus K m hm)
        (Units.mk0 (a : K) ha) ↔
      (a - 1 ∈ m ∧ ∀ φ : K →+* ℝ, 0 < φ (a : K)) := by
  rw [ClassFieldTheory.IsRayCongruent]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [mem_ideal_iff_narrow_primePowers K m hm (a - 1)]
      intro v hv
      have hn : 1 ≤ (narrowIdealModulus K m hm).finitePart v :=
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
      exact (localIntegralRayCongruence K v _ hn a ha).mp (h.1 v hv)
    · exact (narrowRayRealPositivity K m hm (a : K)).mp (fun v hv => h.2 v hv)
  · rintro ⟨hmem, hpos⟩
    constructor
    · intro v hv
      have hn : 1 ≤ (narrowIdealModulus K m hm).finitePart v :=
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
      exact (localIntegralRayCongruence K v _ hn a ha).mpr
        ((mem_ideal_iff_narrow_primePowers K m hm (a - 1)).mp hmem v hv)
    · exact (narrowRayRealPositivity K m hm (a : K)).mpr hpos

theorem narrowRayCongruent_valuation_le_one
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (x : Kˣ)
    (hx : ClassFieldTheory.IsRayCongruent (narrowIdealModulus K m hm) x) :
    ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ (narrowIdealModulus K m hm).finitePart.support →
        v.valuation K (x : K) ≤ 1 := by
  intro v hv
  exact valuation_le_one_of_localRayCongruence K v
    ((narrowIdealModulus K m hm).finitePart v) x (hx.1 v hv)

end DedekindZetaZeroFree.AbelianQuotient

end
