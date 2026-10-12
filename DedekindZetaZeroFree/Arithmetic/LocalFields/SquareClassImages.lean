module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.Arithmetic.LocalFields.UniformSquareUnitModulus

@[expose] public section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree
noncomputable section
set_option autoImplicit false
namespace SArithmeticData
variable {F : Type} [Field F] [NumberField F]

abbrev FiniteSquareClasses (A : SArithmeticData F) :=
  (v : {v // v ∈ A.Sf}) → ClassFieldTheory.PowerClassGroup (v.val.adicCompletion F) 2

def finiteSquareClass (A : SArithmeticData F) : A.G →* A.FiniteSquareClasses where
  toFun x v := ClassFieldTheory.powerClass (v.val.adicCompletion F) 2 (x.2 v)
  map_one' := by ext v; exact map_one _
  map_mul' := by intros; ext v; exact map_mul _ _ _

def pi₂ (A : SArithmeticData F) : A.V →* A.FiniteSquareClasses :=
  QuotientGroup.lift A.sixthPowers A.finiteSquareClass (by
    rintro x ⟨y, rfl⟩
    ext v
    apply (ClassFieldTheory.powerClass_eq_one_iff _ 2 _).mpr
    refine ⟨(y.2 v) ^ 3, ?_⟩
    change ((y.2 v) ^ 3) ^ 2 = (y ^ 6).2 v
    simp [← pow_mul])

def B₂ (A : SArithmeticData F) (B : Subgroup A.V) : Subgroup A.FiniteSquareClasses :=
  Subgroup.map A.pi₂ B

theorem finiteSquareClasses_finite (A : SArithmeticData F) : Finite A.FiniteSquareClasses := by
  letI (v : {v // v ∈ A.Sf}) : Finite
      (ClassFieldTheory.PowerClassGroup (v.val.adicCompletion F) 2) := by
    letI := ClassFieldTheory.finitePlaceCompletionValuativeRel F v.val
    letI := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v.val
    letI : CharZero (v.val.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F _).injective
    exact ClassFieldTheory.powerClassGroup_finite _ 2 (by norm_num)
  infer_instance

theorem B₂_finite (A : SArithmeticData F) (B : Subgroup A.V) : Finite (A.B₂ B) := by
  letI := A.finiteSquareClasses_finite
  infer_instance

theorem finiteSquareClass_gamma_independent (A : SArithmeticData F)
    (x y : A.G) (hxy : x / y ∈ A.Gamma) :
    A.finiteSquareClass x = A.finiteSquareClass y := by
  have hker : A.finiteSquareClass (x / y) = 1 := by
    obtain ⟨z, ⟨u, hu, rfl⟩, hz⟩ := hxy
    rw [← hz]
    ext v
    apply (ClassFieldTheory.powerClass_eq_one_iff _ 2 _).mpr
    refine ⟨(A.diagonal u).2 v ^ 3, ?_⟩
    change ((A.diagonal u).2 v ^ 3) ^ 2 = (A.diagonal (u ^ 6)).2 v
    simp [map_pow, ← pow_mul]
  rw [map_div] at hker
  exact div_eq_one.mp hker

abbrev ExteriorFractional (A : SArithmeticData F) := (FractionalIdeal A.R⁰ F)ˣ

def exteriorFractional (A : SArithmeticData F) (I : A.Exterior) : A.ExteriorFractional :=
  (show IsUnit (A.extendIdeal I : FractionalIdeal A.R⁰ F) from by
    have hO : IsUnit (I.val : FractionalIdeal (𝓞 F)⁰ F) :=
      isUnit_iff_ne_zero.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr I.property.1)
    change IsUnit ((Ideal.map (algebraMap (𝓞 F) A.R) I.val : Ideal A.R) :
      FractionalIdeal A.R⁰ F)
    rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := F) F A.R I.val]
    exact hO.map (FractionalIdeal.extendedHom F A.R)).unit

theorem exteriorFractional_val (A : SArithmeticData F) (I : A.Exterior) :
    (A.exteriorFractional I : FractionalIdeal A.R⁰ F) = A.extendIdeal I := by
  exact IsUnit.unit_spec _

namespace GeneralArithmeticContext
variable {A : SArithmeticData F} {σ : F →+* ℂ}
  {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

def squareClsGenerator (C : A.GeneralArithmeticContext σ η hS)
    (I : A.ExteriorFractional) : Fˣ :=
  Classical.choose (A.exists_allowed_generator_of_isUnit C.classGroup_trivial
    C.correction.H C.correction.B C.correction.B_complement I.val I.isUnit)

theorem squareClsGenerator_spec (C : A.GeneralArithmeticContext σ η hS)
    (I : A.ExteriorFractional) :
    A.IsAllowedGenerator C.correction.B I.val (C.squareClsGenerator I) :=
  Classical.choose_spec (A.exists_allowed_generator_of_isUnit C.classGroup_trivial
    C.correction.H C.correction.B C.correction.B_complement I.val I.isUnit)

def cls (C : A.GeneralArithmeticContext σ η hS)
    (I : A.ExteriorFractional) : A.B₂ C.correction.B :=
  ⟨A.pi₂ (A.sClass (C.squareClsGenerator I)),
    ⟨A.sClass (C.squareClsGenerator I), (C.squareClsGenerator_spec I).2, rfl⟩⟩

private theorem generator_class_independent (C : A.GeneralArithmeticContext σ η hS)
    (I : A.ExteriorFractional) (x : Fˣ)
    (hx : A.IsAllowedGenerator C.correction.B I.val x) :
    A.finiteSquareClass (A.diagonal (C.squareClsGenerator I)) =
      A.finiteSquareClass (A.diagonal x) := by
  apply A.finiteSquareClass_gamma_independent
  rw [← map_div]
  exact ⟨_, C.allowed_unique I.val _ _ (C.squareClsGenerator_spec I) hx, rfl⟩

theorem cls_top (C : A.GeneralArithmeticContext σ η hS) : C.cls 1 = 1 := by
  apply Subtype.ext
  change A.finiteSquareClass (A.diagonal (C.squareClsGenerator 1)) = 1
  have hx : A.IsAllowedGenerator C.correction.B (1 : A.ExteriorFractional).val 1 := by
    constructor
    · simp [FractionalIdeal.spanSingleton_one]
    · exact C.correction.B.one_mem
  simpa using generator_class_independent C 1 1 hx

theorem cls_mul (C : A.GeneralArithmeticContext σ η hS)
    (I J : A.ExteriorFractional) : C.cls (I * J) = C.cls I * C.cls J := by
  apply Subtype.ext
  change A.finiteSquareClass (A.diagonal (C.squareClsGenerator (I * J))) =
    A.finiteSquareClass (A.diagonal (C.squareClsGenerator I)) *
      A.finiteSquareClass (A.diagonal (C.squareClsGenerator J))
  rw [← map_mul, ← map_mul]
  apply generator_class_independent
  exact A.allowed_generator_mul C.correction.B I.val J.val _ _
    (C.squareClsGenerator_spec I) (C.squareClsGenerator_spec J)

theorem cls_allowed_generator (C : A.GeneralArithmeticContext σ η hS)
    (I : A.ExteriorFractional) (x : Fˣ)
    (hx : A.IsAllowedGenerator C.correction.B I.val x) :
    (C.cls I).val = A.finiteSquareClass (A.diagonal x) := by
  exact generator_class_independent C I x hx

def integralCls (C : A.GeneralArithmeticContext σ η hS)
    (a : Ideal (𝓞 F)) : A.B₂ C.correction.B :=
  if ha : a ≠ ⊥ ∧ a ⊔ A.cS = ⊤ then
    C.cls (A.exteriorFractional ⟨a, ha.1, ha.2⟩)
  else 1

theorem integralCls_exterior (C : A.GeneralArithmeticContext σ η hS)
    (I : A.Exterior) : C.integralCls I.val = C.cls (A.exteriorFractional I) := by
  simp only [integralCls, dif_pos I.property]
  rfl

theorem integralCls_top (C : A.GeneralArithmeticContext σ η hS) :
    C.integralCls ⊤ = 1 := by
  let T : A.Exterior := ⟨⊤, top_ne_bot, by simp⟩
  have hT : A.exteriorFractional T = 1 := by
    apply Units.ext
    rw [A.exteriorFractional_val]
    change ((Ideal.map (algebraMap (𝓞 F) A.R) ⊤ : Ideal A.R) : FractionalIdeal A.R⁰ F) = 1
    rw [Ideal.map_top, FractionalIdeal.coeIdeal_top]
  rw [show (⊤ : Ideal (𝓞 F)) = T.val from rfl, C.integralCls_exterior, hT, C.cls_top]

private theorem supported_coprime_exterior (A : SArithmeticData F)
    (qS : Ideal (𝓞 F)) (hqS : qS ≠ ⊥)
    (hsupport : ∀ v : HeightOneSpectrum (𝓞 F), qS ≤ v.asIdeal ↔ v ∈ A.Sf)
    (a : Ideal (𝓞 F)) (ha : a ⊔ qS = ⊤) : a ≠ ⊥ ∧ a ⊔ A.cS = ⊤ := by
  have hsix : Ideal.span {(6 : 𝓞 F)} ≠ ⊤ := by
    rw [ne_eq, Ideal.span_singleton_eq_top]
    letI := Algebra.IsIntegral.isLocalHom ℤ (𝓞 F)
    have hn : ¬ IsUnit (6 : ℤ) := by norm_num [Int.isUnit_iff]
    simpa only [map_ofNat] using
      ((isUnit_map_iff (algebraMap ℤ (𝓞 F)) (6 : ℤ)).not.mpr hn)
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hsix
  have hp0 : p ≠ ⊥ := by
    intro hz
    have h6 : (6 : 𝓞 F) ∈ p := hle (Ideal.mem_span_singleton_self _)
    rw [hz, Ideal.mem_bot] at h6
    norm_num at h6
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp.isPrime, hp0⟩
  have hv : v ∈ A.Sf := A.above_six v (hle (Ideal.mem_span_singleton_self _))
  have hqnot : qS ≠ ⊤ := by
    intro he
    have hqv := (hsupport v).mpr hv
    rw [he] at hqv
    exact hp.ne_top (top_unique hqv)
  have ha0 : a ≠ ⊥ := by
    intro he
    rw [he, bot_sup_eq] at ha
    exact hqnot ha
  refine ⟨ha0, (A.exterior_iff ⟨a, ha0⟩).mpr ?_⟩
  intro w hw
  apply top_unique
  rw [← ha]
  exact sup_le_sup_left ((hsupport w).mpr hw) a

theorem integralCls_mul (C : A.GeneralArithmeticContext σ η hS)
    (qS : Ideal (𝓞 F)) (hqS : qS ≠ ⊥)
    (hsupport : ∀ v : HeightOneSpectrum (𝓞 F), qS ≤ v.asIdeal ↔ v ∈ A.Sf)
    (a b : Ideal (𝓞 F)) (ha : a ⊔ qS = ⊤) (hb : b ⊔ qS = ⊤) :
    C.integralCls (a * b) = C.integralCls a * C.integralCls b := by
  obtain ⟨ha0, hac⟩ := supported_coprime_exterior A qS hqS hsupport a ha
  obtain ⟨hb0, hbc⟩ := supported_coprime_exterior A qS hqS hsupport b hb
  have hab0 : a * b ≠ ⊥ := mul_ne_zero ha0 hb0
  have habc : a * b ⊔ A.cS = ⊤ := by
    rw [Ideal.mul_sup_eq_of_coprime_left hac, hbc]
  let I : A.Exterior := ⟨a, ha0, hac⟩
  let J : A.Exterior := ⟨b, hb0, hbc⟩
  let K : A.Exterior := ⟨a * b, hab0, habc⟩
  have hmul : A.exteriorFractional K = A.exteriorFractional I * A.exteriorFractional J := by
    apply Units.ext
    change (A.exteriorFractional K).val =
      (A.exteriorFractional I).val * (A.exteriorFractional J).val
    rw [A.exteriorFractional_val, A.exteriorFractional_val, A.exteriorFractional_val]
    change ((Ideal.map (algebraMap (𝓞 F) A.R) (a * b) : Ideal A.R) :
      FractionalIdeal A.R⁰ F) = _
    rw [Ideal.map_mul, FractionalIdeal.coeIdeal_mul]
    rfl
  rw [show a * b = K.val from rfl, C.integralCls_exterior,
    show a = I.val from rfl, C.integralCls_exterior,
    show b = J.val from rfl, C.integralCls_exterior, hmul, C.cls_mul]

theorem integralCls_mul_uniform (C : A.GeneralArithmeticContext σ η hS)
    (a b : Ideal (𝓞 F))
    (ha : a ⊔ uniformSquareUnitModulus A.Sf = ⊤)
    (hb : b ⊔ uniformSquareUnitModulus A.Sf = ⊤) :
    C.integralCls (a * b) = C.integralCls a * C.integralCls b := by
  exact C.integralCls_mul _ (uniformSquareUnitModulus_spec A.Sf).1
    (uniformSquareUnitModulus_spec A.Sf).2.1 a b ha hb

end GeneralArithmeticContext
end SArithmeticData
end
end DedekindZetaZeroFree
