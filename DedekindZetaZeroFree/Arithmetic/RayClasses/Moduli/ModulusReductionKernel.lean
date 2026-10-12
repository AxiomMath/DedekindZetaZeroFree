module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.ModulusReduction
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CoprimePositiveGenerators
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralPrincipalCongruence
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

private lemma rayPrimeToIdeals_antitone' {m n : ClassFieldTheory.RayClassModulus F}
    (hmn : m ≤ n) :
    ClassFieldTheory.rayClassPrimeToIdeals n ≤ ClassFieldTheory.rayClassPrimeToIdeals m := by
  intro I hI v hv
  exact hI v (Finsupp.support_mono hmn.1 hv)

private lemma modulusReduction_mk'_apply (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) (hmf : m ≤ f)
    (J : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm)) :
    modulusReduction m hm f hf hmf
      (QuotientGroup.mk' (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
        (fullModulus m hm)) J) =
      QuotientGroup.mk' (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
        (fullModulus f hf))
      (⟨(J : ClassFieldTheory.NumberFieldFractionalIdealGroup F),
        rayPrimeToIdeals_antitone' (fullModulus_le_of_le m hm f hf hmf) J.2⟩) := by
  simp only [modulusReduction, ClassFieldTheory.rayClassIdealModulusProjection,
    QuotientGroup.map_mk']
  refine congrArg _ (Subtype.ext ?_)
  exact Subgroup.coe_inclusion _ J

theorem modulusReduction_kernel (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) (hmf : m ≤ f)
    (c : ClassFieldTheory.RayClassGroup (fullModulus m hm))
    (hc : modulusReduction m hm f hf hmf c = 1) :
    ∃ (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
      (hca : Ideal.span {a} ⊔ m = ⊤) (hcb : Ideal.span {b} ⊔ m = ⊤),
      a - 1 ∈ f ∧ b - 1 ∈ f ∧
      (∀ φ : F →+* ℝ, 0 < φ (a : F)) ∧
      (∀ φ : F →+* ℝ, 0 < φ (b : F)) ∧
      c = idealClass m hm (Ideal.span {a})
          (mt Ideal.span_singleton_eq_bot.mp ha) hca *
        (idealClass m hm (Ideal.span {b})
          (mt Ideal.span_singleton_eq_bot.mp hb) hcb)⁻¹ := by
  classical

  obtain ⟨J, hJ⟩ := QuotientGroup.mk'_surjective
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (fullModulus m hm)) c
  have hc' : modulusReduction m hm f hf hmf
      (QuotientGroup.mk' (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
        (fullModulus m hm)) J) = 1 := by rw [hJ]; exact hc
  rw [modulusReduction_mk'_apply m hm f hf hmf J] at hc'

  have hkey2 : (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) ∈
      ClassFieldTheory.rayPrincipalIdealSubgroup (fullModulus f hf) := by
    have hmem : (⟨(J : ClassFieldTheory.NumberFieldFractionalIdealGroup F),
        rayPrimeToIdeals_antitone' (fullModulus_le_of_le m hm f hf hmf) J.2⟩ :
        ClassFieldTheory.rayClassPrimeToIdeals (fullModulus f hf)) ∈
        ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (fullModulus f hf) := by
      rw [← QuotientGroup.eq_one_iff]
      exact hc'
    exact hmem
  rw [ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff] at hkey2
  obtain ⟨x, hx, hxJ⟩ := hkey2

  have hprime : toPrincipalIdeal (𝓞 F) F x ∈
      ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm) := by
    rw [hxJ]; exact J.2
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hposa, hposb, hcam, hcbm⟩ :=
    exists_mixed_integral_generator m f hm hf hmf x hx hprime
  refine ⟨a, b, ha, hb, hcam, hcbm, ha1, hb1, hposa, hposb, ?_⟩
  have hxa : Units.mk0 (a : F) (by exact_mod_cast ha) =
      x * Units.mk0 (b : F) (by exact_mod_cast hb) := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul]
    exact hab
  have hunit : integralIdealUnit (Ideal.span {a})
        (mt Ideal.span_singleton_eq_bot.mp ha) =
      (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) *
        integralIdealUnit (Ideal.span {b}) (mt Ideal.span_singleton_eq_bot.mp hb) := by
    rw [← principal_integral_span a ha, hxa, map_mul, principal_integral_span b hb, hxJ]
  have hrep : idealClass m hm (Ideal.span {a})
        (mt Ideal.span_singleton_eq_bot.mp ha) hcam =
      c * idealClass m hm (Ideal.span {b})
        (mt Ideal.span_singleton_eq_bot.mp hb) hcbm := by
    have helem : idealToPrimeTo m hm (Ideal.span {a})
          (mt Ideal.span_singleton_eq_bot.mp ha) hcam =
        J * idealToPrimeTo m hm (Ideal.span {b})
          (mt Ideal.span_singleton_eq_bot.mp hb) hcbm := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, idealToPrimeTo_coe] using hunit
    rw [idealClass, idealClass, helem, map_mul, hJ]
  rw [hrep]
  group

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
