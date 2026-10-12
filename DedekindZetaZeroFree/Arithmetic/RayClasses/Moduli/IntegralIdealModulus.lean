module

public import ClassFieldTheory.Definitions.All
public import ClassFieldTheory.Theorems.All
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.RayClassBridge

 theorem modulus_support_finite
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) :
    (Function.support (fun v : HeightOneSpectrum (𝓞 F) =>
      Int.toNat (FractionalIdeal.count F v
        (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)))).Finite := by
  have hf := FractionalIdeal.finite_factors
    (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  rw [Filter.eventually_cofinite] at hf
  exact hf.subset (by intro v hv hz; exact hv (by simp [hz]))

private theorem toNat_count_coe_ne_zero_iff
    (F : Type) [Field F] [NumberField F]
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    Int.toNat (FractionalIdeal.count F v
      (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) ≠ 0 ↔ J ≤ v.asIdeal := by
  rw [ne_eq, Int.toNat_eq_zero, not_le,
    FractionalIdeal.count_coe F v hJ, Int.natCast_pos,
    Nat.pos_iff_ne_zero, Associates.count_ne_zero_iff_dvd hJ v.irreducible, Ideal.dvd_iff_le]

def narrowIdealModulus
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (_h𝔪 : 𝔪 ≠ ⊥) : ClassFieldTheory.RayClassModulus F where
  finitePart := Finsupp.ofSupportFinite
    (fun v => Int.toNat (FractionalIdeal.count F v
      (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)))
    (modulus_support_finite F 𝔪)
  infinitePart := Finset.univ

def integralUnit
    (F : Type) [Field F] [NumberField F]
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

@[simp] theorem integralUnit_val
    (F : Type) [Field F] [NumberField F]
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (integralUnit F I hI : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = I := rfl

@[simp] theorem narrowIdealModulus_finitePart
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    (narrowIdealModulus F 𝔪 h𝔪).finitePart v =
      Int.toNat (FractionalIdeal.count F v
        (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := rfl

@[simp] theorem narrowIdealModulus_infinitePart
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    (narrowIdealModulus F 𝔪 h𝔪).infinitePart = Finset.univ := rfl

theorem narrowIdealModulus_support
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    (↑(narrowIdealModulus F 𝔪 h𝔪).finitePart.support : Set (HeightOneSpectrum (𝓞 F))) =
      {v | 𝔪 ≤ v.asIdeal} := by
  ext v
  rw [Finset.mem_coe, Finsupp.mem_support_iff, narrowIdealModulus_finitePart,
    Set.mem_setOf_eq]
  exact toNat_count_coe_ne_zero_iff F 𝔪 h𝔪 v

private theorem mem_finitePart_support_iff
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support ↔ 𝔪 ≤ v.asIdeal := by
  rw [← Finset.mem_coe, narrowIdealModulus_support, Set.mem_setOf_eq]

@[simp] theorem narrowIdealModulus_top_finitePart
    (F : Type) [Field F] [NumberField F] (h : (⊤ : Ideal (𝓞 F)) ≠ ⊥) :
    (narrowIdealModulus F ⊤ h).finitePart = 0 := by
  ext v
  rw [narrowIdealModulus_finitePart, FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]
  rfl

theorem integralUnit_mem_primeTo_iff
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    integralUnit F I hI ∈ ClassFieldTheory.rayClassPrimeToIdeals
      (narrowIdealModulus F 𝔪 h𝔪) ↔ I ⊔ 𝔪 = ⊤ := by
  simp only [ClassFieldTheory.rayClassPrimeToIdeals, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hne
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (I ⊔ 𝔪) hne
    have hne_bot : I ⊔ 𝔪 ≠ ⊥ := fun hb =>
      hI (le_bot_iff.mp (hb ▸ le_sup_left))
    have hpne : p ≠ ⊥ := fun hb => hne_bot (le_bot_iff.mp (hb ▸ hle))
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp.isPrime, hpne⟩
    have h𝔪le : 𝔪 ≤ v.asIdeal := le_trans le_sup_right hle
    have hmem : v ∈ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support :=
      (mem_finitePart_support_iff F 𝔪 h𝔪 v).mpr h𝔪le
    have hcount := h v hmem
    rw [integralUnit_val, FractionalIdeal.count_coe F v hI, Int.natCast_eq_zero] at hcount
    have hnd : ¬ (v.asIdeal ∣ I) := fun hd =>
      ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mpr hd) hcount
    rw [Ideal.dvd_iff_le] at hnd
    exact hnd (le_trans le_sup_left hle)
  · intro hcop v hv
    rw [integralUnit_val]
    by_contra hc
    rw [FractionalIdeal.count_coe F v hI, Int.natCast_eq_zero] at hc
    have hdvd : v.asIdeal ∣ I := (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc
    rw [Ideal.dvd_iff_le] at hdvd
    have hv' : 𝔪 ≤ v.asIdeal := (mem_finitePart_support_iff F 𝔪 h𝔪 v).mp hv
    exact Ideal.IsMaximal.ne_top inferInstance (top_le_iff.mp (hcop ▸ sup_le hdvd hv'))

def integralPrimeTo
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) :
    ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪) :=
  ⟨integralUnit F I hI, (integralUnit_mem_primeTo_iff F 𝔪 h𝔪 I hI).mpr hcop⟩

def integralRayClass
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) :
    ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪) :=
  QuotientGroup.mk (integralPrimeTo F 𝔪 h𝔪 I hI hcop)

@[simp] theorem integralUnit_top
    (F : Type) [Field F] [NumberField F] (h : (⊤ : Ideal (𝓞 F)) ≠ ⊥) :
    integralUnit F ⊤ h = 1 := by
  ext
  simp [integralUnit]

theorem integralUnit_mul
    (F : Type) [Field F] [NumberField F]
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I * J ≠ ⊥) :
    integralUnit F (I * J) hIJ = integralUnit F I hI * integralUnit F J hJ := by
  ext
  simp [integralUnit, FractionalIdeal.coeIdeal_mul]

@[simp] theorem integralPrimeTo_top
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (h : (⊤ : Ideal (𝓞 F)) ≠ ⊥) (hcop : ⊤ ⊔ 𝔪 = ⊤) :
    integralPrimeTo F 𝔪 h𝔪 ⊤ h hcop = 1 := by
  ext
  simp [integralPrimeTo, integralUnit_top]

@[simp] theorem integralRayClass_top
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (h : (⊤ : Ideal (𝓞 F)) ≠ ⊥) (hcop : ⊤ ⊔ 𝔪 = ⊤) :
    integralRayClass F 𝔪 h𝔪 ⊤ h hcop = 1 := by
  simp [integralRayClass, integralPrimeTo_top]

end DedekindZetaZeroFree.RayClassBridge

end
