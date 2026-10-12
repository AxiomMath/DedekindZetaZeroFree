module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IdelicCharacterLift
public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.RayClassBridge

variable (F : Type) [Field F] [NumberField F]

 theorem integral_orders_support_finite (I : Ideal (𝓞 F)) :
    (Function.support (fun v : HeightOneSpectrum (𝓞 F) =>
      FractionalIdeal.count F v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))).Finite := by
  have hf := FractionalIdeal.finite_factors
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  rw [Filter.eventually_cofinite] at hf
  exact hf

def integralIdealOrders (I : Ideal (𝓞 F)) :
    HeightOneSpectrum (𝓞 F) →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun v => FractionalIdeal.count F v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))
    (integral_orders_support_finite F I)

def idealIdele (I : Ideal (𝓞 F)) (_hI : I ≠ ⊥) : IdeleGroup F :=
  ∏ v ∈ (integralIdealOrders F I).support,
    IdeleGroup.finitePrimeIdele v ^ (integralIdealOrders F I v)

private theorem order_eq_count (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) :
    integralIdealOrders F I v =
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) := by
  exact FractionalIdeal.count_coe F v hI

private theorem support_le_ideal (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ (integralIdealOrders F I).support) :
    I ≤ v.asIdeal := by
  have hn := Finsupp.mem_support_iff.mp hv
  rw [order_eq_count F I hI v, Int.natCast_ne_zero] at hn
  exact Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hn)

private theorem support_not_dvd_modulus (𝔪 I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hcop : I ⊔ 𝔪 = ⊤) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∈ (integralIdealOrders F I).support) : ¬ 𝔪 ≤ v.asIdeal := by
  intro hm
  have hh := sup_le (support_le_ideal F I hI v hv) hm
  rw [hcop] at hh
  exact v.isMaximal.ne_top (top_unique hh)

 def coefficientHom (𝔪 : Ideal (𝓞 F)) (η : RayClassCharacter F 𝔪) :
    Ideal (𝓞 F) →* ℂ where
  toFun := η
  map_one' := by simpa only [Ideal.one_eq_top] using η.map_top'
  map_mul' := η.map_mul'

private theorem ideal_factorization (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (∏ v ∈ (integralIdealOrders F I).support,
      v.asIdeal ^ (integralIdealOrders F I v).toNat) = I := by
  have hfac := Ideal.finprod_heightOneSpectrum_factorization hI
  rw [finprod_eq_finsetProd_of_mulSupport_subset
    (fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I)] at hfac
  · convert hfac using 1
    apply Finset.prod_congr rfl
    intro v hv
    simp [order_eq_count F I hI v, HeightOneSpectrum.maxPowDividing]
  · intro v hv
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have : v.maxPowDividing I = 1 := by
      simp [HeightOneSpectrum.maxPowDividing, order_eq_count F I hI v,
        Int.natCast_eq_zero.mp (by simpa [order_eq_count F I hI v] using hz)]
    exact hv this

theorem ideleClassCharacter_idealIdele
    (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) :
    (ideleClassCharacter F hcomplex 𝔪 h𝔪 η
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
        (idealIdele F I hI)) : ℂ) = η I := by
  have heq : ∀ v ∈ (integralIdealOrders F I).support,
      (ideleClassCharacter F hcomplex 𝔪 h𝔪 η
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
          (IdeleGroup.finitePrimeIdele v)) : ℂ) = η v.asIdeal := by
    intro v hv
    apply ideleClassCharacter_finitePrimeIdele F hcomplex 𝔪 h𝔪 η v
    have hnd := support_not_dvd_modulus F 𝔪 I hI hcop v hv
    simpa only [← Finset.mem_coe, narrowIdealModulus_support,
      Set.mem_setOf_eq] using hnd
  calc
    (ideleClassCharacter F hcomplex 𝔪 h𝔪 η
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
          (idealIdele F I hI)) : ℂ) =
      ∏ v ∈ (integralIdealOrders F I).support,
        (ideleClassCharacter F hcomplex 𝔪 h𝔪 η
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
            (IdeleGroup.finitePrimeIdele v)) : ℂ) ^
          (integralIdealOrders F I v).toNat := by
      rw [idealIdele, map_prod, map_prod]
      simp only [map_zpow]
      change (Units.coeHom ℂ) (∏ v ∈ (integralIdealOrders F I).support,
          ideleClassCharacter F hcomplex 𝔪 h𝔪 η
            (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
              (IdeleGroup.finitePrimeIdele v)) ^ (integralIdealOrders F I v)) = _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro v hv
      have hn : 0 ≤ integralIdealOrders F I v :=
        FractionalIdeal.count_coe_nonneg F v I
      rw [map_zpow, ← zpow_natCast, Int.toNat_of_nonneg hn]
      rfl
    _ = ∏ v ∈ (integralIdealOrders F I).support,
        η v.asIdeal ^ (integralIdealOrders F I v).toNat := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [heq v hv]
    _ = η I := by
      conv_rhs => rw [← ideal_factorization F I hI]
      change (∏ v ∈ (integralIdealOrders F I).support,
        (coefficientHom F 𝔪 η) v.asIdeal ^ (integralIdealOrders F I v).toNat) =
        (coefficientHom F 𝔪 η) (∏ v ∈ (integralIdealOrders F I).support,
          v.asIdeal ^ (integralIdealOrders F I v).toNat)
      simp

end DedekindZetaZeroFree.RayClassBridge

end
