module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.AbelianQuotient

theorem narrowIdealModulus_finiteSupport
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    (Function.support (fun v : HeightOneSpectrum (𝓞 K) =>
      Multiset.count v.asIdeal (normalizedFactors m))).Finite := by
  have hf := (normalizedFactors m).toFinset.finite_toSet
  apply (hf.preimage HeightOneSpectrum.asIdeal_injective.injOn).subset
  intro v hv
  exact Multiset.mem_toFinset.mpr (Multiset.count_ne_zero.mp hv)

def narrowIdealModulus
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) : ClassFieldTheory.RayClassModulus K where
  finitePart := Finsupp.ofSupportFinite
    (fun v => Multiset.count v.asIdeal (normalizedFactors m))
    (narrowIdealModulus_finiteSupport K m hm)
  infinitePart := Finset.univ

@[simp] theorem narrowIdealModulus_finitePart
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    (narrowIdealModulus K m hm).finitePart v =
      Multiset.count v.asIdeal (normalizedFactors m) := by
  exact congrFun Finsupp.ofSupportFinite_coe v

@[simp] theorem narrowIdealModulus_infinitePart
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    (narrowIdealModulus K m hm).infinitePart = Finset.univ := by
  rfl

abbrev RayIdealClass
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :=
  ClassFieldTheory.RayClassGroup (narrowIdealModulus K m hm)

def rayIdealFractionalIdeal
    (K : Type) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ClassFieldTheory.NumberFieldFractionalIdealGroup K :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

@[simp] theorem rayIdealFractionalIdeal_coe
    (K : Type) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (rayIdealFractionalIdeal K I hI : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  rfl

theorem rayIdealFractionalIdeal_mem_primeTo
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hcoprime : I ⊔ m = ⊤) :
    rayIdealFractionalIdeal K I hI ∈
      ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus K m hm) := by
  intro v hv
  rw [rayIdealFractionalIdeal_coe, FractionalIdeal.count_coe K v hI]
  apply Int.natCast_eq_zero.mpr
  by_contra hc
  have hIv : I ≤ v.asIdeal := Ideal.dvd_iff_le.mp
    ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc)
  have hcount : Multiset.count v.asIdeal (normalizedFactors m) ≠ 0 := by
    simpa using (Finsupp.mem_support_iff.mp hv)
  have hmv : m ≤ v.asIdeal :=
    ((Ideal.mem_normalizedFactors_iff hm).mp
      (Multiset.count_ne_zero.mp hcount)).2
  have hsup := sup_le hIv hmv
  rw [hcoprime] at hsup
  exact v.isPrime.ne_top (top_unique hsup)

def rayIdealClassRepresentative
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hcoprime : I ⊔ m = ⊤) :
    ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus K m hm) :=
  ⟨rayIdealFractionalIdeal K I hI,
    rayIdealFractionalIdeal_mem_primeTo K m hm I hI hcoprime⟩

def rayIdealClass
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (I : Ideal (𝓞 K)) :
    Option (RayIdealClass K m hm) :=
  if h : I = ⊥ ∨ I ⊔ m ≠ ⊤ then none
  else some (QuotientGroup.mk'
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (narrowIdealModulus K m hm))
    (rayIdealClassRepresentative K m hm I
      (fun hI => h (Or.inl hI))
      (not_not.mp (fun hcoprime => h (Or.inr hcoprime)))))

theorem rayIdealClass_eq_none
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (I : Ideal (𝓞 K))
    (h : I = ⊥ ∨ I ⊔ m ≠ ⊤) :
    rayIdealClass K m hm I = none := by
  simp [rayIdealClass, h]

@[simp] theorem rayIdealClass_eq_none_iff
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (I : Ideal (𝓞 K)) :
    rayIdealClass K m hm I = none ↔ I = ⊥ ∨ I ⊔ m ≠ ⊤ := by
  by_cases h : I = ⊥ ∨ I ⊔ m ≠ ⊤ <;> simp [rayIdealClass, h]

theorem rayIdealClass_eq_some
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hcoprime : I ⊔ m = ⊤) :
    rayIdealClass K m hm I = some (QuotientGroup.mk'
      (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (narrowIdealModulus K m hm))
      (rayIdealClassRepresentative K m hm I hI hcoprime)) := by
  simp [rayIdealClass, hI, hcoprime]

theorem rayIdealClass_of_finitePrime
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (narrowIdealModulus K m hm).finitePart.support) :
    rayIdealClass K m hm v.asIdeal =
      some (ClassFieldTheory.rayClassOfFinitePrime (narrowIdealModulus K m hm) v hv) := by
  have hnot : ¬ m ≤ v.asIdeal := by
    intro hle
    apply hv
    apply Finsupp.mem_support_iff.mpr
    rw [narrowIdealModulus_finitePart]
    exact Multiset.count_ne_zero.mpr
      ((Ideal.mem_normalizedFactors_iff hm).mpr ⟨v.isPrime, hle⟩)
  have hcoprime : v.asIdeal ⊔ m = ⊤ := by
    by_contra hne
    have heq := v.isMaximal.eq_of_le hne le_sup_left
    exact hnot (heq ▸ le_sup_right)
  rw [rayIdealClass_eq_some K m hm v.asIdeal v.ne_bot hcoprime]
  rfl

end DedekindZetaZeroFree.AbelianQuotient

end
