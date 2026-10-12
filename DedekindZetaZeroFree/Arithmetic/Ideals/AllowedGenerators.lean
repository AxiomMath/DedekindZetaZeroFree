module

public import DedekindZetaZeroFree.Arithmetic.Units.SUnitLagrangianComplements
public import DedekindZetaZeroFree.Arithmetic.Units.LocalPowerInjection

@[expose] public section

open scoped NumberField nonZeroDivisors

noncomputable section

set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree
namespace SArithmeticData

variable {F : Type} [Field F] [NumberField F]

def sClass (A : SArithmeticData F) : Fˣ →* A.V :=
  (QuotientGroup.mk' A.sixthPowers).comp A.diagonal

def IsAllowed (A : SArithmeticData F) (B : Subgroup A.V) (a : Fˣ) : Prop :=
  A.sClass a ∈ B

def IsAllowedGenerator (A : SArithmeticData F) (B : Subgroup A.V)
    (I : FractionalIdeal A.R⁰ F) (a : Fˣ) : Prop :=
  I = FractionalIdeal.spanSingleton A.R⁰ (a : F) ∧ A.IsAllowed B a

def sUnitSixthPowers (A : SArithmeticData F) : Subgroup Fˣ :=
  A.U.map (powMonoidHom 6)

private lemma mem_E_iff (A : SArithmeticData F) (v : A.V) :
    v ∈ A.E ↔ ∃ u : A.U, A.sClass (u : Fˣ) = v := by
  have hE : A.E = Subgroup.map A.sClass A.U := by
    show (A.U.map A.diagonal).map (QuotientGroup.mk' A.sixthPowers) = _
    rw [Subgroup.map_map]
    rfl
  rw [hE, Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, hxe⟩ => ⟨⟨x, hx⟩, hxe⟩, fun ⟨u, hu⟩ => ⟨u.val, u.property, hu⟩⟩

private lemma spanSingleton_unit (A : SArithmeticData F) (u : A.U) :
    FractionalIdeal.spanSingleton A.R⁰ ((u : Fˣ) : F) = 1 := by
  have h : ((u : Fˣ) : F) = algebraMap A.R F ((A.unitEquiv u : A.Rˣ) : A.R) := rfl
  rw [h, ← FractionalIdeal.coeIdeal_span_singleton,
    Ideal.span_singleton_eq_top.mpr (Units.isUnit _), FractionalIdeal.coeIdeal_top]

theorem exists_allowed_generator_of_isUnit (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (B : Subgroup A.V) (hB : A.IsSUnitIsotropicComplement H B)
    (I : FractionalIdeal A.R⁰ F) (hI : IsUnit I) :
    ∃ a : Fˣ, A.IsAllowedGenerator B I a := by
  letI : Subsingleton (ClassGroup A.R) := hCl
  letI : Submodule.IsPrincipal (I : Submodule A.R F) :=
    ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI
  let x : F := Submodule.IsPrincipal.generator (I : Submodule A.R F)
  have hx : I = FractionalIdeal.spanSingleton A.R⁰ x :=
    FractionalIdeal.eq_spanSingleton_of_principal I
  have hx0 : x ≠ 0 := by
    intro hz
    apply hI.ne_zero
    simpa [hz] using hx
  let a₀ : Fˣ := Units.mk0 x hx0
  obtain ⟨p, hp, _⟩ := hB.2.2 (A.sClass a₀)
  obtain ⟨u, hu⟩ := (mem_E_iff A p.1.val).mp p.1.property
  refine ⟨a₀ * u.val⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val,
      ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.spanSingleton_inv, spanSingleton_unit A u, inv_one, mul_one]
    exact hx
  · change A.sClass (a₀ * u.val⁻¹) ∈ B
    rw [map_mul, map_inv, hu, ← hp]
    rw [mul_comm p.1.val p.2.val, mul_assoc, mul_inv_cancel, mul_one]
    exact p.2.property

theorem exists_allowed_generator (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (B : Subgroup A.V) (hB : A.IsSUnitIsotropicComplement H B)
    (I : FractionalIdeal A.R⁰ F) (hI : I ≠ 0) :
    ∃ a : Fˣ, A.IsAllowedGenerator B I a := by
  have hnum : I.num ≠ ⊥ := (FractionalIdeal.num_eq_zero_iff.not).mpr hI
  let E : A.Exterior := A.exteriorIdealEquiv.symm ⟨I.num, hnum⟩
  have hext : A.extendIdeal E = I.num := by
    rw [← A.exteriorIdealEquiv_apply]
    simp [E]
  have hO : IsUnit (E.val : FractionalIdeal (𝓞 F)⁰ F) := by
    exact isUnit_iff_ne_zero.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr E.property.1)
  have hnumunit : IsUnit (I.num : FractionalIdeal A.R⁰ F) := by
    rw [← hext]
    change IsUnit ((Ideal.map (algebraMap (𝓞 F) A.R) E.val : Ideal A.R) : FractionalIdeal A.R⁰ F)
    rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := F) F A.R E.val]
    exact hO.map (FractionalIdeal.extendedHom F A.R)
  have hprod : IsUnit (FractionalIdeal.spanSingleton A.R⁰
      (algebraMap A.R F I.den) * I) := by
    rw [FractionalIdeal.den_mul_self_eq_num']
    exact hnumunit
  exact A.exists_allowed_generator_of_isUnit hCl H B hB I
    (isUnit_of_mul_isUnit_right hprod)

theorem allowed_generator_unique_mod_sixth (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (B : Subgroup A.V) (hB : A.IsSUnitIsotropicComplement H B)
    (I : FractionalIdeal A.R⁰ F) (a a' : Fˣ)
    (ha : A.IsAllowedGenerator B I a) (ha' : A.IsAllowedGenerator B I a') :
    a / a' ∈ A.sUnitSixthPowers := by
  have heq : FractionalIdeal.spanSingleton A.R⁰ (a' : F) =
      FractionalIdeal.spanSingleton A.R⁰ (a : F) := ha'.1.symm.trans ha.1
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp heq
  let ε : A.U := A.unitEquiv.symm z
  have hzval : (ε.val : F) = ((z : A.R) : F) := by
    simp [ε, unitEquiv, Set.unitEquivUnitsInteger]
  have hratio : a / a' = ε.val := by
    apply Units.ext
    rw [Units.val_div_eq_div_val]
    rw [div_eq_iff a'.ne_zero, hzval]
    exact hz.symm
  have hE : A.sClass ε.val ∈ A.E := by
    exact ⟨A.diagonal ε.val, ⟨ε.val, ε.property, rfl⟩, rfl⟩
  have hmemB : A.sClass ε.val ∈ B := by
    rw [← hratio, map_div]
    exact B.div_mem ha.2 ha'.2
  have hc : A.sClass ε.val = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hB.1.disjoint.eq_bot]
    exact ⟨hE, hmemB⟩
  have hpow : A.diagonal ε.val ∈ A.sixthPowers :=
    (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨g, hg⟩ := hpow
  have hloc :
      (∀ w, ∃ b, b ^ 6 = (A.diagonal ε.val).1 w) ∧
      (∀ v, ∃ b, b ^ 6 = (A.diagonal ε.val).2 v) := by
    constructor
    · intro w
      exact ⟨g.1 w, congrArg (fun x : A.G => x.1 w) hg⟩
    · intro v
      exact ⟨g.2 v, congrArg (fun x : A.G => x.2 v) hg⟩
  obtain ⟨b, hb⟩ := A.local_power_injection F hCl 6 (by simp) ε hloc
  rw [hratio]
  exact ⟨b.val, b.property, congrArg Subtype.val hb⟩

theorem allowed_generator_mul (A : SArithmeticData F) (B : Subgroup A.V)
    (I J : FractionalIdeal A.R⁰ F) (a b : Fˣ)
    (ha : A.IsAllowedGenerator B I a) (hb : A.IsAllowedGenerator B J b) :
    A.IsAllowedGenerator B (I * J) (a * b) := by
  obtain ⟨hI, haB⟩ := ha
  obtain ⟨hJ, hbB⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [hI, hJ, FractionalIdeal.spanSingleton_mul_spanSingleton, Units.val_mul]
  · rw [IsAllowed, map_mul]
    exact B.mul_mem haB hbB

theorem allowed_generator_integral (A : SArithmeticData F) (B : Subgroup A.V)
    (J : Ideal A.R) (a : Fˣ)
    (ha : A.IsAllowedGenerator B (J : FractionalIdeal A.R⁰ F) a) :
    ∃ r : A.R, r ≠ 0 ∧ (r : F) = (a : F) ∧ Ideal.span {r} = J := by
  have hm : (a : F) ∈ (J : FractionalIdeal A.R⁰ F) := by
    rw [ha.1]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨r, hr, heq⟩ := (FractionalIdeal.mem_coeIdeal A.R⁰).mp hm
  refine ⟨r, ?_, heq, ?_⟩
  · intro hz
    exact a.ne_zero (by simpa [hz] using heq.symm)
  · apply FractionalIdeal.coeIdeal_injective (K := F)
    change (Ideal.span {r} : FractionalIdeal A.R⁰ F) = (J : FractionalIdeal A.R⁰ F)
    rw [FractionalIdeal.coeIdeal_span_singleton, heq, ← ha.1]

theorem exists_allowed_integral_generator (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (B : Subgroup A.V) (hB : A.IsSUnitIsotropicComplement H B)
    (I : A.Exterior) :
    ∃ (r : A.R) (a : Fˣ), A.Generates I r ∧ (a : F) = (r : F) ∧
      A.IsAllowed B a := by
  have hne : (A.extendIdeal I : FractionalIdeal A.R⁰ F) ≠ 0 := by
    rw [FractionalIdeal.coeIdeal_ne_zero]
    exact A.extendIdeal_ne_zero I
  obtain ⟨a, ha⟩ :=
    A.exists_allowed_generator hCl H B hB (A.extendIdeal I : FractionalIdeal A.R⁰ F) hne
  obtain ⟨r, hr0, hra, hspan⟩ := A.allowed_generator_integral B (A.extendIdeal I) a ha
  exact ⟨r, a, ⟨hr0, hspan⟩, hra.symm, ha.2⟩

end SArithmeticData
end DedekindZetaZeroFree

end
