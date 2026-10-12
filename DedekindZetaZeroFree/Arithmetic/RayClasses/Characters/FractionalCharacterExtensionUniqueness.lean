module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PrimeToFractionalIdealRatios
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOperations

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

 def characterUnit {m : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (A : Ideal (𝓞 F)) (hA : A ≠ ⊥) (hAcop : A ⊔ m = ⊤) : ℂˣ :=
  Units.mk0 (η A) ((RayOperations.ne_zero_iff η A).mpr ⟨hA, hAcop⟩)

private theorem characterUnit_mul {m : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (A B : Ideal (𝓞 F)) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hAcop : A ⊔ m = ⊤) (hBcop : B ⊔ m = ⊤)
    (hAB : A * B ≠ ⊥) (hABcop : (A * B) ⊔ m = ⊤) :
    characterUnit η (A * B) hAB hABcop =
      characterUnit η A hA hAcop * characterUnit η B hB hBcop := by
  apply Units.ext
  exact η.map_mul' A B

private theorem character_ratio_well_defined {m : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (A B C D : Ideal (𝓞 F))
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hC : C ≠ ⊥) (hD : D ≠ ⊥)
    (hAcop : A ⊔ m = ⊤) (hBcop : B ⊔ m = ⊤)
    (hCcop : C ⊔ m = ⊤) (hDcop : D ⊔ m = ⊤)
    (h : integralIdealUnit A hA * (integralIdealUnit B hB)⁻¹ =
      integralIdealUnit C hC * (integralIdealUnit D hD)⁻¹) :
    characterUnit η A hA hAcop * (characterUnit η B hB hBcop)⁻¹ =
      characterUnit η C hC hCcop * (characterUnit η D hD hDcop)⁻¹ := by
  have hcross := mul_inv_eq_mul_inv_iff_mul_eq_mul.mp h
  have hideals : A * D = C * B := by
    apply FractionalIdeal.coeIdeal_injective (K := F)
    have hval := congrArg (fun u : ClassFieldTheory.NumberFieldFractionalIdealGroup F =>
      (u : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) hcross
    simpa only [Units.val_mul, integralIdealUnit, Units.val_mk0,
      FractionalIdeal.coeIdeal_mul] using hval
  apply mul_inv_eq_mul_inv_iff_mul_eq_mul.mpr
  apply Units.ext
  change η A * η D = η C * η B
  rw [← η.map_mul' A D, ← η.map_mul' C B, hideals]

 structure CharacterRatio (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (J : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm)) where
  A : Ideal (𝓞 F)
  B : Ideal (𝓞 F)
  hA : A ≠ ⊥
  hB : B ≠ ⊥
  hAcop : A ⊔ m = ⊤
  hBcop : B ⊔ m = ⊤
  eq_ratio : (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) =
    integralIdealUnit A hA * (integralIdealUnit B hB)⁻¹

 def chooseCharacterRatio (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (J : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm)) :
    CharacterRatio m hm J := by
  have hex : Nonempty (CharacterRatio m hm J) := by
    obtain ⟨A, B, hA, hB, hAcop, hBcop, h⟩ := exists_integralIdealUnit_ratio m hm J
    exact ⟨⟨A, B, hA, hB, hAcop, hBcop, h⟩⟩
  exact Classical.choice hex

 def fractionalValue (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (J : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm)) : ℂˣ :=
  let r := chooseCharacterRatio m hm J
  characterUnit η r.A r.hA r.hAcop * (characterUnit η r.B r.hB r.hBcop)⁻¹

private theorem fractionalValue_ratio (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (A B : Ideal (𝓞 F)) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hAcop : A ⊔ m = ⊤) (hBcop : B ⊔ m = ⊤)
    (J : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm))
    (hJ : (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) =
      integralIdealUnit A hA * (integralIdealUnit B hB)⁻¹) :
    fractionalValue m hm η J =
      characterUnit η A hA hAcop * (characterUnit η B hB hBcop)⁻¹ := by
  let r := chooseCharacterRatio m hm J
  exact character_ratio_well_defined η r.A r.B A B r.hA r.hB hA hB
    r.hAcop r.hBcop hAcop hBcop (r.eq_ratio.symm.trans hJ)

 theorem fractionalValue_one (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    fractionalValue m hm η 1 = 1 := by
  apply (fractionalValue_ratio m hm η ⊤ ⊤ top_ne_bot top_ne_bot
    (by simp) (by simp) 1 (by simp)).trans
  exact mul_inv_cancel _

 theorem fractionalValue_mul (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (J K : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm)) :
    fractionalValue m hm η (J * K) = fractionalValue m hm η J * fractionalValue m hm η K := by
  let r := chooseCharacterRatio m hm J
  let s := chooseCharacterRatio m hm K
  have h : ((J * K) : ClassFieldTheory.NumberFieldFractionalIdealGroup F) =
      integralIdealUnit (r.A * s.A) (ideal_mul_ne_bot _ _ r.hA s.hA) *
        (integralIdealUnit (r.B * s.B) (ideal_mul_ne_bot _ _ r.hB s.hB))⁻¹ := by
    rw [r.eq_ratio, s.eq_ratio,
      integralIdealUnit_mul _ _ r.hA s.hA,
      integralIdealUnit_mul _ _ r.hB s.hB, mul_inv_rev]
    ac_rfl
  rw [fractionalValue_ratio m hm η (r.A * s.A) (r.B * s.B)
    (ideal_mul_ne_bot _ _ r.hA s.hA) (ideal_mul_ne_bot _ _ r.hB s.hB)
    (ideal_mul_coprime m _ _ r.hAcop s.hAcop)
    (ideal_mul_coprime m _ _ r.hBcop s.hBcop) (J * K) h]
  rw [characterUnit_mul η _ _ r.hA s.hA r.hAcop s.hAcop,
    characterUnit_mul η _ _ r.hB s.hB r.hBcop s.hBcop]
  unfold fractionalValue
  dsimp only
  rw [mul_inv_rev]
  ac_rfl

def fractionalCharacter (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm) →* ℂˣ where
  toFun := fractionalValue m hm η
  map_one' := fractionalValue_one m hm η
  map_mul' := fractionalValue_mul m hm η

@[simp] theorem fractionalCharacter_apply (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    (fractionalCharacter m hm η (idealToPrimeTo m hm I hI hcop) : ℂ) = η I := by
  have h := fractionalValue_ratio m hm η I ⊤ hI top_ne_bot hcop (by simp)
    (idealToPrimeTo m hm I hI hcop) (by
      rw [idealToPrimeTo_coe]
      have ht : integralIdealUnit (⊤ : Ideal (𝓞 F)) top_ne_bot = 1 := by
        simpa only [Ideal.one_eq_top] using integralIdealUnit_one (F := F) (by simp)
      rw [ht, inv_one, mul_one])
  change (fractionalValue m hm η (idealToPrimeTo m hm I hI hcop) : ℂ) = η I
  rw [h]
  simp [characterUnit, η.map_top']

theorem fractionalCharacter_apply_ratio (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (A B : Ideal (𝓞 F)) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hAcop : A ⊔ m = ⊤) (hBcop : B ⊔ m = ⊤)
    (J : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm))
    (hJ : (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) =
      integralIdealUnit A hA * (integralIdealUnit B hB)⁻¹) :
    (fractionalCharacter m hm η J : ℂ) = η A / η B := by
  change (fractionalValue m hm η J : ℂ) = η A / η B
  rw [fractionalValue_ratio m hm η A B hA hB hAcop hBcop J hJ]
  simp [characterUnit, div_eq_mul_inv]

theorem fractionalCharacter_unique (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (χ : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm) →* ℂˣ)
    (hχ : ∀ (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤),
      (χ (idealToPrimeTo m hm I hI hcop) : ℂ) = η I) :
    χ = fractionalCharacter m hm η := by
  ext J
  obtain ⟨A, B, hA, hB, hAcop, hBcop, hJ⟩ := exists_integralIdealUnit_ratio m hm J
  have heq : J = idealToPrimeTo m hm A hA hAcop *
      (idealToPrimeTo m hm B hB hBcop)⁻¹ := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, idealToPrimeTo_coe] using hJ
  rw [fractionalCharacter_apply_ratio m hm η A B hA hB hAcop hBcop J hJ]
  rw [heq, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    hχ A hA hAcop, hχ B hB hBcop]
  rfl

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
