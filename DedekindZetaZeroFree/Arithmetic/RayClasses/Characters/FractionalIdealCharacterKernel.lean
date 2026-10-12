module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PositiveDenominator
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem rayFractionalCharacterKernel
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m) :
    let μ := narrowIdealModulus K m hm
    let P := ClassFieldTheory.rayClassPrimeToIdeals μ
    let F := FractionalIdeal (nonZeroDivisors (𝓞 K)) K
    ∀ (f : P →* ℂˣ),
      (∀ I : Ideal (𝓞 K), I ≠ ⊥ → I ⊔ m = ⊤ →
        ∀ J : P,
          ((J : ClassFieldTheory.NumberFieldFractionalIdealGroup K) : F) =
            (I : F) →
          (f J : ℂ) = χ I) →
      ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo μ ≤ f.ker := by
  intro μ P F f hf
  intro J hJ
  rw [MonoidHom.mem_ker]
  have hJmem : (J : ClassFieldTheory.NumberFieldFractionalIdealGroup K) ∈
      ClassFieldTheory.rayPrincipalIdealSubgroup μ := by
    have hJ' := hJ
    rw [ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo, Subgroup.mem_comap] at hJ'
    exact hJ'
  obtain ⟨x, hx, hJx⟩ :=
    (ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff μ
      (J : ClassFieldTheory.NumberFieldFractionalIdealGroup K)).1 hJmem
  obtain ⟨a, d, ha, hd, had, ha1, hd1, hapos, hdpos⟩ :=
    positiveRayDenominator K m hm x hx

  have hIa : Ideal.span ({a} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact ha
  have hId : Ideal.span ({d} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hd
  have hca : Ideal.span ({a} : Set (𝓞 K)) ⊔ m = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 K) = a - (a - 1) := by ring
    rw [h1]
    exact sub_mem (Submodule.mem_sup_left (Ideal.mem_span_singleton_self a))
      (Submodule.mem_sup_right ha1)
  have hcd : Ideal.span ({d} : Set (𝓞 K)) ⊔ m = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 K) = d - (d - 1) := by ring
    rw [h1]
    exact sub_mem (Submodule.mem_sup_left (Ideal.mem_span_singleton_self d))
      (Submodule.mem_sup_right hd1)

  let Ja : P := rayIdealClassRepresentative K m hm (Ideal.span {a}) hIa hca
  let Jd : P := rayIdealClassRepresentative K m hm (Ideal.span {d}) hId hcd
  have hJa_coe : (Ja : ClassFieldTheory.NumberFieldFractionalIdealGroup K) =
      rayIdealFractionalIdeal K (Ideal.span {a}) hIa := rfl
  have hJd_coe : (Jd : ClassFieldTheory.NumberFieldFractionalIdealGroup K) =
      rayIdealFractionalIdeal K (Ideal.span {d}) hId := rfl
  have hJa_val : (((Ja : ClassFieldTheory.NumberFieldFractionalIdealGroup K) : F)) =
      ((Ideal.span {a} : Ideal (𝓞 K)) : F) := by
    rw [hJa_coe, rayIdealFractionalIdeal_coe]
  have hJd_val : (((Jd : ClassFieldTheory.NumberFieldFractionalIdealGroup K) : F)) =
      ((Ideal.span {d} : Ideal (𝓞 K)) : F) := by
    rw [hJd_coe, rayIdealFractionalIdeal_coe]

  have hfa : f Ja = 1 := by
    have h := hf (Ideal.span {a}) hIa hca Ja hJa_val
    rw [χ.map_span' a ha ha1 hapos] at h
    exact Units.val_eq_one.mp h
  have hfd : f Jd = 1 := by
    have h := hf (Ideal.span {d}) hId hcd Jd hJd_val
    rw [χ.map_span' d hd hd1 hdpos] at h
    exact Units.val_eq_one.mp h

  have hdK : (d : K) ≠ 0 := fun hzero =>
    hd (IsFractionRing.injective (𝓞 K) K (by simpa using hzero))
  have hdiv : (a : K) / (d : K) = (x : K) := by
    rw [had, mul_div_cancel_left₀ _ hdK]
  have hunit : toPrincipalIdeal (𝓞 K) K x =
      rayIdealFractionalIdeal K (Ideal.span {a}) hIa *
        (rayIdealFractionalIdeal K (Ideal.span {d}) hId)⁻¹ := by
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_mul, Units.val_inv_eq_inv_val,
      rayIdealFractionalIdeal_coe, rayIdealFractionalIdeal_coe,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      ← div_eq_mul_inv, FractionalIdeal.spanSingleton_div_spanSingleton, hdiv]
  have hJeq : J = Ja * Jd⁻¹ := by
    apply Subtype.ext
    rw [← hJx, Subgroup.coe_mul, Subgroup.coe_inv, hJa_coe, hJd_coe]
    exact hunit
  rw [hJeq, map_mul, map_inv, hfa, hfd]
  simp

end DedekindZetaZeroFree.AbelianQuotient
