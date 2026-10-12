module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralCongruence
public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdeals.EulerWeights

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

def M (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) : ClassFieldTheory.RayClassModulus F where
  finitePart := (RayClassBridge.narrowIdealModulus F m hm).finitePart
  infinitePart := ∅

@[simp] theorem M_finitePart (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    (M F m hm).finitePart v = idealPrimeExponent v.asIdeal m := by
  change Int.toNat (FractionalIdeal.count F v
    (m : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) = _
  rw [FractionalIdeal.count_coe F v hm, Int.toNat_natCast]
  exact Ideal.count_associates_factors_eq hm v.isPrime v.ne_bot

@[simp] theorem M_infinitePart (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) : (M F m hm).infinitePart = ∅ := rfl

def frozenIntegralPrimeTo (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    ClassFieldTheory.rayClassPrimeToIdeals (M F m hm) :=
  ⟨RayClassBridge.integralUnit F I hI,
    (RayClassBridge.integralUnit_mem_primeTo_iff F m hm I hI).mpr hcop⟩

def frozenIntegralRayClass (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    ClassFieldTheory.RayClassGroup (M F m hm) :=
  QuotientGroup.mk (frozenIntegralPrimeTo F m hm I hI hcop)

def frozenRayValue (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ)
    (I : Ideal (𝓞 F)) : ℂ :=
  if h : I ≠ ⊥ ∧ I ⊔ m = ⊤ then
    (rho (frozenIntegralRayClass F m hm I h.1 h.2) : ℂ)
  else 0

theorem frozenRayValue_of_primeTo (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    frozenRayValue F m hm rho I =
      (rho (frozenIntegralRayClass F m hm I hI hcop) : ℂ) := by
  simp [frozenRayValue, hI, hcop]

theorem frozenRayValue_of_not_primeTo (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ)
    (I : Ideal (𝓞 F)) (hI : I = ⊥ ∨ I ⊔ m ≠ ⊤) :
    frozenRayValue F m hm rho I = 0 := by
  unfold frozenRayValue
  split_ifs with h
  · rcases hI with hI | hI
    · exact (h.1 hI).elim
    · exact (hI h.2).elim
  · rfl

theorem frozenRayValue_eq_zero_iff (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ) (I : Ideal (𝓞 F)) :
    frozenRayValue F m hm rho I = 0 ↔ I = ⊥ ∨ I ⊔ m ≠ ⊤ := by
  unfold frozenRayValue
  split_ifs with h
  · simp only [Units.ne_zero, false_iff]
    exact not_or.mpr ⟨h.1, not_not.mpr h.2⟩
  · simp only [true_iff]
    tauto

@[simp] theorem frozenRayValue_top (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ) :
    frozenRayValue F m hm rho ⊤ = 1 := by
  rw [frozenRayValue_of_primeTo F m hm rho ⊤ top_ne_bot (by simp)]
  have h : frozenIntegralRayClass F m hm ⊤ top_ne_bot (by simp) = 1 := by
    have h' : frozenIntegralPrimeTo F m hm ⊤ top_ne_bot (by simp) = 1 := by
      apply Subtype.ext
      exact RayClassBridge.integralUnit_top F top_ne_bot
    simp [frozenIntegralRayClass, h']
  simp [h]

theorem frozenRayValue_mul (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ)
    (I J : Ideal (𝓞 F)) :
    frozenRayValue F m hm rho (I * J) =
      frozenRayValue F m hm rho I * frozenRayValue F m hm rho J := by
  have hc : I * J ⊔ m = ⊤ ↔ I ⊔ m = ⊤ ∧ J ⊔ m = ⊤ := by
    simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_left_iff]
  by_cases hI : I ≠ ⊥ ∧ I ⊔ m = ⊤
  · by_cases hJ : J ≠ ⊥ ∧ J ⊔ m = ⊤
    · have hIJ : I * J ≠ ⊥ := by simpa [Ideal.mul_eq_bot] using And.intro hI.1 hJ.1
      have hcIJ := hc.mpr ⟨hI.2, hJ.2⟩
      rw [frozenRayValue_of_primeTo F m hm rho (I * J) hIJ hcIJ,
        frozenRayValue_of_primeTo F m hm rho I hI.1 hI.2,
        frozenRayValue_of_primeTo F m hm rho J hJ.1 hJ.2]
      have hp : frozenIntegralPrimeTo F m hm (I * J) hIJ hcIJ =
          frozenIntegralPrimeTo F m hm I hI.1 hI.2 *
            frozenIntegralPrimeTo F m hm J hJ.1 hJ.2 := by
        apply Subtype.ext
        exact RayClassBridge.integralUnit_mul F I J hI.1 hJ.1 hIJ
      simp only [frozenIntegralRayClass, hp, QuotientGroup.mk_mul, map_mul, Units.val_mul]
    · have hzJ : J = ⊥ ∨ J ⊔ m ≠ ⊤ := by tauto
      have hzIJ : I * J = ⊥ ∨ I * J ⊔ m ≠ ⊤ := by
        rcases hzJ with hzJ | hzJ
        · left; simp [hzJ]
        · right; exact fun h => hzJ (hc.mp h).2
      rw [frozenRayValue_of_not_primeTo F m hm rho (I * J) hzIJ,
        frozenRayValue_of_not_primeTo F m hm rho J hzJ, mul_zero]
  · have hzI : I = ⊥ ∨ I ⊔ m ≠ ⊤ := by tauto
    have hzIJ : I * J = ⊥ ∨ I * J ⊔ m ≠ ⊤ := by
      rcases hzI with hzI | hzI
      · left; simp [hzI]
      · right; exact fun h => hzI (hc.mp h).1
    rw [frozenRayValue_of_not_primeTo F m hm rho (I * J) hzIJ,
      frozenRayValue_of_not_primeTo F m hm rho I hzI, zero_mul]

theorem frozenIntegralRayClass_span (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (α : 𝓞 F) (hα : α ≠ 0) (hcα : α - 1 ∈ m)
    (hI : Ideal.span {α} ≠ ⊥) (hcop : Ideal.span {α} ⊔ m = ⊤) :
    frozenIntegralRayClass F m hm (Ideal.span {α}) hI hcop = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change RayClassBridge.integralUnit F (Ideal.span {α}) hI ∈
    ClassFieldTheory.rayPrincipalIdealSubgroup (M F m hm)
  apply Subgroup.subset_closure
  have hαF : (α : F) ≠ 0 := by exact_mod_cast hα
  let x : Fˣ := Units.mk0 (α : F) hαF
  refine ⟨x, ?_, ?_⟩
  · constructor
    · exact (RayClassBridge.integral_finite_ray_congruent_iff
        F m hm α hα x rfl).mpr hcα
    · simp only [M_infinitePart, Finset.notMem_empty, false_implies, implies_true]
  · apply Units.ext
    rw [coe_toPrincipalIdeal, RayClassBridge.integralUnit_val,
      FractionalIdeal.coeIdeal_span_singleton]
    rfl

theorem frozenRayValue_span (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ)
    (α : 𝓞 F) (hα : α ≠ 0) (hcα : α - 1 ∈ m) :
    frozenRayValue F m hm rho (Ideal.span {α}) = 1 := by
  have hI : Ideal.span {α} ≠ ⊥ := fun h => hα (Ideal.span_singleton_eq_bot.mp h)
  have hcop := RayClassBridge.span_add_modulus_eq_top_of_sub_one_mem F m α hcα
  rw [frozenRayValue_of_primeTo F m hm rho _ hI hcop,
    frozenIntegralRayClass_span F m hm α hα hcα hI hcop, map_one, Units.val_one]

theorem M_le_iff (F : Type) [Field F] [NumberField F]
    (m n : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hn : n ≠ ⊥) :
    M F m hm ≤ M F n hn ↔ n ≤ m := by
  rw [ClassFieldTheory.RayClassModulus.le_iff]
  simp only [M_finitePart, M_infinitePart, Finset.empty_subset, and_true]
  have hexp (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
      idealPrimeExponent v.asIdeal I =
        (Associates.mk v.asIdeal).count (Associates.mk I).factors :=
    (Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot).symm
  simp only [hexp _ m hm, hexp _ n hn]
  constructor
  · intro h
    rw [← Ideal.iInf_maxPowDividing_eq hm, ← Ideal.iInf_maxPowDividing_eq hn]
    exact iInf_mono fun v => Ideal.pow_le_pow_right (h v)
  · intro h v
    apply Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hn)
      v.associates_irreducible
    exact Associates.mk_dvd_mk.mpr (Ideal.dvd_iff_le.mpr h)

def frozenRay (F : Type) [Field F] [NumberField F]
    (_htc : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ) :
    RayClassCharacter F m where
  toFun := frozenRayValue F m hm rho
  map_mul' := frozenRayValue_mul F m hm rho
  map_top' := frozenRayValue_top F m hm rho
  eq_zero_iff' := frozenRayValue_eq_zero_iff F m hm rho
  map_span' := fun α hα hcα _ => frozenRayValue_span F m hm rho α hα hcα

theorem frozenRay_apply (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (rho : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ)
    (I : Ideal (𝓞 F)) :
    frozenRay F htc m hm rho I =
      if h : I ≠ ⊥ ∧ I ⊔ m = ⊤ then
        (rho (frozenIntegralRayClass F m hm I h.1 h.2) : ℂ)
      else 0 := rfl

end
end DedekindZetaZeroFree
