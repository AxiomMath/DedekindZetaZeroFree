module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PositiveChineseRemainder
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.LocalCongruenceAndPositivity
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PrimeToFractionalIdealRatios
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealPrimeTo

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

theorem exists_positive_integral_generator
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (x : Fˣ)
    (hx : ClassFieldTheory.IsRayCongruent (fullModulus m hm) x) :
    ∃ a b : 𝓞 F, a ≠ 0 ∧ b ≠ 0 ∧
      (a : F) = (x : F) * (b : F) ∧ a - 1 ∈ m ∧ b - 1 ∈ m ∧
      (∀ φ : F →+* ℝ, 0 < φ (a : F)) ∧
      (∀ φ : F →+* ℝ, 0 < φ (b : F)) := by
  classical

  have hmem : toPrincipalIdeal (𝓞 F) F x ∈
      ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm) :=
    ClassFieldTheory.rayPrincipalIdealSubgroup_le_primeToIdeals F (fullModulus m hm)
      (Subgroup.subset_closure ⟨x, hx, rfl⟩)

  obtain ⟨A, B, hA, hB, hAm, hBm, hratio⟩ :=
    exists_integralIdealUnit_ratio m hm ⟨toPrincipalIdeal (𝓞 F) F x, hmem⟩

  obtain ⟨b, hbne, hbB, hb1, hbpos⟩ :=
    exists_positive_mem_congruent_one m hm B hB hBm
  have hratio' : toPrincipalIdeal (𝓞 F) F x =
      integralIdealUnit A hA * (integralIdealUnit B hB)⁻¹ := hratio
  have hmul : toPrincipalIdeal (𝓞 F) F x * integralIdealUnit B hB = integralIdealUnit A hA := by
    rw [hratio', mul_assoc, inv_mul_cancel, mul_one]
  have hAB : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) *
      (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    have h := congrArg
      (fun u : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ =>
        (u : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) hmul
    simpa [integralIdealUnit, coe_toPrincipalIdeal] using h
  have hspanb : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F) ≤
      (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr
      (FractionalIdeal.mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 F)) hbB)

  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((x : F) * (b : F)) ≤
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton (x : F) (b : F)]
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)
        ≤ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) *
            (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          mul_le_mul_right hspanb _
      _ = (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hAB
      _ ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hy1 : (x : F) * (b : F) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mp hle
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 F))).mp hy1
  have hbF : (algebraMap (𝓞 F) F) b ≠ 0 :=
    fun h => hbne (IsFractionRing.injective (𝓞 F) F (by simpa using h))
  have haF : (algebraMap (𝓞 F) F) a ≠ 0 := by
    rw [ha]; exact mul_ne_zero (Units.ne_zero x) hbF
  have hane : a ≠ 0 := fun h => haF (by rw [h]; exact map_zero _)
  refine ⟨a, b, hane, hbne, ha, ?_, hb1, ?_, hbpos⟩
  ·
    have h1 : a - b ∈ m := ray_congruent_sub_mem m hm x hx a b ha
    have : a - 1 = (a - b) + (b - 1) := by ring
    rw [this]; exact m.add_mem h1 hb1
  ·
    intro φ
    change 0 < φ ((algebraMap (𝓞 F) F) a)
    have hxpos : 0 < φ (x : F) := ray_congruent_pos m hm x hx φ
    rw [ha, map_mul]
    exact mul_pos hxpos (hbpos φ)

end DedekindZetaZeroFree.LargeSieve.RayBridge
