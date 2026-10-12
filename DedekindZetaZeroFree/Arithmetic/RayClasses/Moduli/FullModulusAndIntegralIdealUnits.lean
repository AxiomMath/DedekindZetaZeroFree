module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

def fullModulus (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    ClassFieldTheory.RayClassModulus F where
  finitePart := Finsupp.onFinset (Ideal.finite_factors hm).toFinset
    (fun v => (Associates.mk v.asIdeal).count (Associates.mk m).factors)
    (by
      intro v hv
      exact (Ideal.finite_factors hm).mem_toFinset.mpr
        ((Associates.count_ne_zero_iff_dvd hm v.irreducible).mp hv))
  infinitePart := Finset.univ

@[simp] theorem fullModulus_finitePart (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (fullModulus m hm).finitePart v =
      (Associates.mk v.asIdeal).count (Associates.mk m).factors := by
  simp [fullModulus]

@[simp] theorem fullModulus_infinitePart (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    (fullModulus m hm).infinitePart = Finset.univ := by
  rw [fullModulus]

@[simp] theorem mem_fullModulus_infinitePart (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (v : ClassFieldTheory.RayClassRealPlace F) :
    v ∈ (fullModulus m hm).infinitePart := by
  rw [fullModulus_infinitePart]
  exact Finset.mem_univ v

def integralIdealUnit (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

@[simp] theorem integralIdealUnit_one (h : (1 : Ideal (𝓞 F)) ≠ ⊥) :
    integralIdealUnit (1 : Ideal (𝓞 F)) h = 1 := by
  simp [integralIdealUnit, Ideal.one_eq_top]

@[simp] theorem integralIdealUnit_mul (I J : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I * J ≠ ⊥) :
    integralIdealUnit (I * J) hIJ = integralIdealUnit I hI * integralIdealUnit J hJ := by
  ext
  simp only [integralIdealUnit, Units.val_mk0, Units.val_mul, FractionalIdeal.coeIdeal_mul]

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
