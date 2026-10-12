module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PrimeToIntegralIdealClasses
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralPrincipalCongruence
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

theorem integral_span_coprime (m : Ideal (𝓞 F)) (a : 𝓞 F)
    (hcong : a - 1 ∈ m) :
    Ideal.span {a} ⊔ m = ⊤ := by
  refine Ideal.eq_top_iff_one _ |>.mpr ?_
  have h1 : a - (a - 1) ∈ Ideal.span {a} ⊔ m :=
    sub_mem (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton a)))
      (Ideal.mem_sup_right hcong)
  simpa using h1

theorem idealClass_integral_principal (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (a : 𝓞 F) (ha : a ≠ 0) (hcong : a - 1 ∈ m)
    (hpos : ∀ φ : F →+* ℝ, 0 < φ (a : F)) :
    idealClass m hm (Ideal.span {a})
      (mt Ideal.span_singleton_eq_bot.mp ha)
      (integral_span_coprime m a hcong) = 1 := by
  have hmem : idealToPrimeTo m hm (Ideal.span {a})
      (mt Ideal.span_singleton_eq_bot.mp ha) (integral_span_coprime m a hcong) ∈
      ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (fullModulus m hm) := by
    rw [ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo, Subgroup.mem_comap]
    change integralIdealUnit (Ideal.span {a}) (mt Ideal.span_singleton_eq_bot.mp ha) ∈
      ClassFieldTheory.rayPrincipalIdealSubgroup (fullModulus m hm)
    rw [← principal_integral_span a ha]
    exact Subgroup.subset_closure
      ⟨_, integral_isRayCongruent m hm a ha hcong hpos, rfl⟩
  unfold idealClass
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hmem

theorem prime_not_mem_fullModulus_support (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hcop : p.asIdeal ⊔ m = ⊤) :
    p ∉ (fullModulus m hm).finitePart.support := by
  intro hp
  rw [Finsupp.mem_support_iff, fullModulus_finitePart] at hp
  rw [Associates.count_ne_zero_iff_dvd hm p.irreducible] at hp
  have hle : m ≤ p.asIdeal := Ideal.dvd_iff_le.mp hp
  have hsup : p.asIdeal ⊔ m = p.asIdeal := sup_eq_left.mpr hle
  exact p.isPrime.ne_top (hsup ▸ hcop)

theorem idealClass_prime (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hcop : p.asIdeal ⊔ m = ⊤) :
    idealClass m hm p.asIdeal p.ne_bot hcop =
      ClassFieldTheory.rayClassOfFinitePrime (fullModulus m hm) p
        (prime_not_mem_fullModulus_support m hm p hcop) := by
  unfold idealClass ClassFieldTheory.rayClassOfFinitePrime
  congr 1

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
