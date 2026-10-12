module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralCongruence
public import DedekindZetaZeroFree.Arithmetic.Ideals.IntegralPrincipalGenerator

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.RayUnitary

theorem integral_ideal_pow_card_rayClassGroup_generator
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) :
    let M := RayClassBridge.narrowIdealModulus F 𝔪 h𝔪
    let N := Nat.card (ClassFieldTheory.RayClassGroup M)
    0 < N ∧ ∃ α : 𝓞 F,
      α ≠ 0 ∧ α - 1 ∈ 𝔪 ∧
      (∀ φ : F →+* ℝ, 0 < φ (α : F)) ∧ I ^ N = Ideal.span {α} := by
  classical
  let M := RayClassBridge.narrowIdealModulus F 𝔪 h𝔪
  let N := Nat.card (ClassFieldTheory.RayClassGroup M)
  letI : Finite (ClassFieldTheory.RayClassGroup M) :=
    ClassFieldTheory.rayClassGroup_finite F M
  have hN : 0 < N := Nat.card_pos
  let J := RayClassBridge.integralPrimeTo F 𝔪 h𝔪 I hI hcop
  have hpow : J ^ N ∈ ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo M := by
    apply (QuotientGroup.eq_one_iff (J ^ N)).mp
    rw [QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  rw [ClassFieldTheory.GlobalClassFieldComparison.rayPrincipalIdealSubgroup_eq] at hpow
  let M' := ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F M
  obtain ⟨x, hx, hEq⟩ :=
    (RayClass.mem_principalRayIdealSubgroup_iff M' (J ^ N)).mp hpow
  have hxray : ClassFieldTheory.IsRayCongruent M x :=
    (ClassFieldTheory.GlobalClassFieldComparison.principalIdele_mem_primeTo_iff_isRayCongruent
      F M x).mp hx
  have hfrac : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) =
      ((I ^ N : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [← coe_toPrincipalIdeal x]
    have hVal := congrArg (fun y : ClassFieldTheory.NumberFieldFractionalIdealGroup F =>
      (y : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) hEq
    simpa only [J, RayClassBridge.integralPrimeTo, Subgroup.coe_pow,
      Units.val_pow_eq_pow_val, RayClassBridge.integralUnit_val,
      FractionalIdeal.coeIdeal_pow] using hVal
  obtain ⟨α, hα0, hαx, hαI⟩ :=
    integral_generator_of_spanSingleton_eq_coeIdeal F (I ^ N) x hfrac
  have hcong :=
    (RayClassBridge.isRayCongruent_iff_integral F 𝔪 h𝔪 α hα0 x hαx.symm).mp hxray
  exact ⟨hN, α, hα0, hcong.1, hcong.2, hαI.symm⟩

end DedekindZetaZeroFree.RayUnitary
