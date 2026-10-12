module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PrimeToIntegralIdealClasses
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealModulusProjectionSurjective

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

theorem fullModulus_le_of_le (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) (hmf : m ≤ f) :
    fullModulus f hf ≤ fullModulus m hm := by
  rw [ClassFieldTheory.RayClassModulus.le_iff]
  refine ⟨fun v => ?_, ?_⟩
  · simp only [fullModulus_finitePart]
    exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr (by simpa using hm))
      v.associates_irreducible
      (by rw [Associates.mk_le_mk_iff_dvd]; exact Ideal.dvd_iff_le.mpr hmf)
  · intro x hx
    simpa using Finset.mem_univ x

def modulusReduction (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) (hmf : m ≤ f) :
    ClassFieldTheory.RayClassGroup (fullModulus m hm) →*
      ClassFieldTheory.RayClassGroup (fullModulus f hf) :=
  ClassFieldTheory.rayClassIdealModulusProjection F
    (fullModulus_le_of_le m hm f hf hmf)

theorem modulusReduction_surjective (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) (hmf : m ≤ f) :
    Function.Surjective (modulusReduction m hm f hf hmf) := by
  exact ClassFieldTheory.rayClassIdealModulusProjection_surjective F
    (fullModulus_le_of_le m hm f hf hmf)

@[simp] theorem modulusReduction_apply_idealClass
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) (hmf : m ≤ f)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    modulusReduction m hm f hf hmf (idealClass m hm I hI hcop) =
      idealClass f hf I hI (by
        apply top_unique
        rw [← hcop]
        exact sup_le_sup_left hmf I) := by
  unfold modulusReduction idealClass
  rw [ClassFieldTheory.rayClassIdealModulusProjection]
  simp only [QuotientGroup.map_mk', QuotientGroup.mk'_apply]
  apply congrArg (fun z : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus f hf) =>
    (z : ClassFieldTheory.RayClassGroup (fullModulus f hf)))
  apply Subtype.ext
  simp only [Subgroup.coe_inclusion, idealToPrimeTo_coe]

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
