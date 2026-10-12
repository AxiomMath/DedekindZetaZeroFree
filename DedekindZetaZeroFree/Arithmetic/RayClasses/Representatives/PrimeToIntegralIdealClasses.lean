module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.FullModulusAndIntegralIdealUnits
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

def idealToPrimeTo (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm) :=
  ⟨integralIdealUnit I hI, by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv
    rw [fullModulus_finitePart] at hv
    have hm0 : m ≠ 0 := by simpa using hm
    have hI0 : I ≠ 0 := by simpa using hI
    have hle_m : m ≤ v.asIdeal :=
      Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hm0 v.irreducible).mp hv)
    have hcoe : ((integralIdealUnit I hI :
        ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := rfl
    rw [hcoe, FractionalIdeal.count_coe F v hI0, Nat.cast_eq_zero]
    by_contra hne
    have hle_I : I ≤ v.asIdeal :=
      Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hne)
    have htop : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
      rw [← hcop]
      exact sup_le hle_I hle_m
    exact v.isPrime.ne_top (top_le_iff.mp htop)⟩

def idealClass (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    ClassFieldTheory.RayClassGroup (fullModulus m hm) :=
  QuotientGroup.mk'
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (fullModulus m hm))
    (idealToPrimeTo m hm I hI hcop)

@[simp] theorem idealToPrimeTo_coe (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    (idealToPrimeTo m hm I hI hcop :
      ClassFieldTheory.NumberFieldFractionalIdealGroup F) = integralIdealUnit I hI :=
  rfl

theorem ideal_mul_ne_bot (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I * J ≠ ⊥ := by
  intro h
  exact (Ideal.mul_eq_bot.mp h).elim hI hJ

theorem ideal_mul_coprime (m I J : Ideal (𝓞 F))
    (hIm : I ⊔ m = ⊤) (hJm : J ⊔ m = ⊤) :
    (I * J) ⊔ m = ⊤ := by
  have hcomm : m ⊔ I = ⊤ := by rw [sup_comm]; exact hIm
  have h : m ⊔ I * J = ⊤ := by
    rw [Ideal.sup_mul_eq_of_coprime_left hcomm, sup_comm, hJm]
  rw [sup_comm]
  exact h

@[simp] theorem idealToPrimeTo_top (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    idealToPrimeTo m hm ⊤ (by exact top_ne_bot) (by simp) = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_one, idealToPrimeTo_coe]
  apply Units.ext
  show ((⊤ : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1
  exact FractionalIdeal.coeIdeal_top (nonZeroDivisors (𝓞 F))

@[simp] theorem idealClass_top (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    idealClass m hm ⊤ (by exact top_ne_bot) (by simp) = 1 := by
  rw [idealClass, idealToPrimeTo_top, map_one]

@[simp] theorem idealToPrimeTo_mul (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIm : I ⊔ m = ⊤) (hJm : J ⊔ m = ⊤)
    (hIJ : I * J ≠ ⊥) (hIJm : (I * J) ⊔ m = ⊤) :
    idealToPrimeTo m hm (I * J) hIJ hIJm =
      idealToPrimeTo m hm I hI hIm * idealToPrimeTo m hm J hJ hJm := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, idealToPrimeTo_coe]
  exact integralIdealUnit_mul I J hI hJ hIJ

@[simp] theorem idealClass_mul (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIm : I ⊔ m = ⊤) (hJm : J ⊔ m = ⊤)
    (hIJ : I * J ≠ ⊥) (hIJm : (I * J) ⊔ m = ⊤) :
    idealClass m hm (I * J) hIJ hIJm =
      idealClass m hm I hI hIm * idealClass m hm J hJ hJm := by
  rw [idealClass, idealClass, idealClass, idealToPrimeTo_mul, map_mul]

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
