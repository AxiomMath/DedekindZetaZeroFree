module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.RootsOfUnityAndPowerClasses
public import DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators

@[expose] public section

section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

private theorem finite_open (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen ((powMonoidHom 6 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range : Set (v.adicCompletion F)ˣ) := by
  letI : ValuativeRel (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  letI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have h6 : (6 : v.adicCompletion F) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (by decide : 6 ≠ 0)
  obtain ⟨E, hE⟩ :=
    LocalClassFieldTheory.exists_finiteGalois_normSubgroup_le_powMonoidHom_range
      (v.adicCompletion F) 6 h6
  letI := E.finiteDimensional
  letI := E.isGalois
  exact Subgroup.isOpen_mono hE
    (LocalClassFieldTheory.localNormSubgroup_isOpen (v.adicCompletion F)
      (E : IntermediateField (v.adicCompletion F) (SeparableClosure (v.adicCompletion F))))

theorem local_character_continuous (A : SArithmeticData F) (χ : A.G →* Circle)
    (hχ : ∀ y : A.G, χ y ^ 6 = 1) : Continuous χ := by
  let P : Set A.G := Set.univ ×ˢ
    Set.pi Set.univ (fun v : {v // v ∈ A.Sf} =>
      ((powMonoidHom 6 : (v.val.adicCompletion F)ˣ →* _).range : Set _))
  have hP : IsOpen P := isOpen_univ.prod
    (isOpen_set_pi Set.finite_univ (fun v _ => finite_open v.val))
  have h1 : (1 : A.G) ∈ P := by
    constructor
    · trivial
    · intro v _
      exact MonoidHom.mem_range.mpr ⟨1, by simp⟩
  have htriv : ∀ x ∈ P, χ x = 1 := by
    intro x hx
    have hinf : ∀ w, ∃ y : w.Completionˣ, y ^ 6 = x.1 w :=
      fun w => A.infinite_unit_isPower w 6 (Or.inr (Or.inr rfl)) (x.1 w)
    have hfin : ∀ v : {v // v ∈ A.Sf}, ∃ y : (v.val.adicCompletion F)ˣ,
        y ^ 6 = x.2 v := by
      intro v
      exact MonoidHom.mem_range.mp (hx.2 v (Set.mem_univ v))
    choose yi hyi using hinf
    choose yf hyf using hfin
    let y : A.G := (yi, yf)
    have hy : y ^ 6 = x := by
      apply Prod.ext <;> funext v
      · exact hyi v
      · exact hyf v
    rw [← hy, map_pow, hχ]
  apply continuous_of_continuousAt_one χ
  have heq : (χ : A.G → Circle) =ᶠ[nhds 1] (fun _ => 1) :=
    Filter.eventually_of_mem (hP.mem_nhds h1) htriv
  exact (continuousAt_const.congr_of_eventuallyEq heq)

end
end DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps

end

section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

def sRestriction (A : SArithmeticData F) : NumberField.IdeleGroup (𝓞 F) F →* A.G :=
  (MonoidHom.pi fun w : InfinitePlace F =>
    Units.map ((Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) w).toMonoidHom.comp
      (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom)).prod
  (MonoidHom.pi fun v : {v // v ∈ A.Sf} =>
    Units.map (({ toFun := fun x : FiniteAdeleRing (𝓞 F) F => x v.val
                  map_one' := rfl
                  map_mul' := fun _ _ => rfl } :
        FiniteAdeleRing (𝓞 F) F →* v.val.adicCompletion F).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom))

def exteriorIdealMap (A : SArithmeticData F) :
    NumberField.IdeleGroup (𝓞 F) F →* (FractionalIdeal A.R⁰ F)ˣ :=
  (Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom).comp
    (FiniteIdeleGroup.fractionalIdeal.comp
      ((MonoidHom.snd (_root_.InfiniteIdeleGroup F) (_root_.FiniteIdeleGroup F)).comp
        (_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm.toMonoidHom))

def rawCharacter (A : SArithmeticData F) (χ : A.G →* Circle)
    (κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle) :
    NumberField.IdeleGroup (𝓞 F) F →* Circle where
  toFun x := κ (exteriorIdealMap A x) * (χ (sRestriction A x))⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

def principalIdealMap (A : SArithmeticData F) : Fˣ →* (FractionalIdeal A.R⁰ F)ˣ :=
  Units.map ({ toFun := FractionalIdeal.spanSingleton A.R⁰
               map_one' := FractionalIdeal.spanSingleton_one
               map_mul' := fun x y => (FractionalIdeal.spanSingleton_mul_spanSingleton _ _).symm }
    : F →* FractionalIdeal A.R⁰ F)

theorem glue_on_idele_classes (A : SArithmeticData F) (χ : A.G →* Circle)
    (κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle)
    (hprincipal : ∀ a : Fˣ, κ (principalIdealMap A a) = χ (A.diagonal a))
    (n : ℕ) (hχ : ∀ y : A.G, χ y ^ n = 1)
    (hκ : ∀ I : (FractionalIdeal A.R⁰ F)ˣ, κ I ^ n = 1) :
    ∃ Φ : NumberField.IdeleClassGroup (𝓞 F) F →* Circle,
      (∀ x : NumberField.IdeleGroup (𝓞 F) F,
        Φ (QuotientGroup.mk x) = rawCharacter A χ κ x) ∧
      (∀ z : NumberField.IdeleClassGroup (𝓞 F) F, Φ z ^ n = 1) := by
  have hs (a : Fˣ) :
      sRestriction A (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = A.diagonal a := by
    ext <;> rfl
  have hi (a : Fˣ) :
      exteriorIdealMap A (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
        principalIdealMap A a := by
    change Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom
      (_root_.IdeleGroup.fractionalIdeal (_root_.IdeleGroup.principalIdele F a)) = _
    rw [_root_.IdeleGroup.fractionalIdeal_principalIdele]
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe, coe_toPrincipalIdeal]
    change (FractionalIdeal.extendedHom F A.R)
      (FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F)) =
        FractionalIdeal.spanSingleton A.R⁰ (a : F)
    rw [FractionalIdeal.extendedHom_spanSingleton (A := 𝓞 F) (K := F) F A.R]
    congr 1
    have hm : (IsFractionRing.map (K := F) (L := F)
        (FaithfulSMul.algebraMap_injective (𝓞 F) A.R)) = RingHom.id F := by
      apply IsLocalization.ringHom_ext (𝓞 F)⁰
      ext x
      simp only [RingHom.comp_apply, RingHom.id_apply, IsFractionRing.map,
        IsLocalization.map_eq]
      exact (IsScalarTower.algebraMap_apply (𝓞 F) A.R F x).symm
    rw [hm]
    rfl
  have hker : NumberField.IdeleGroup.principalSubgroup (𝓞 F) F ≤
      (rawCharacter A χ κ).ker := by
    rintro x ⟨a, rfl⟩
    change κ (exteriorIdealMap A _) * (χ (sRestriction A _))⁻¹ = 1
    rw [hi, hs, hprincipal]
    exact mul_inv_cancel _
  refine ⟨QuotientGroup.lift _ (rawCharacter A χ κ) hker, ?_, ?_⟩
  · intro x
    rfl
  · intro z
    induction z using Quotient.inductionOn with
    | h x =>
      change (κ (exteriorIdealMap A x) * (χ (sRestriction A x))⁻¹) ^ n = 1
      rw [mul_pow, inv_pow, hκ, hχ]
      simp

end
end DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps

end

section

open scoped NumberField Classical nonZeroDivisors Topology
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

private theorem finite_char_cont (A : SArithmeticData F)
    (κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle) :
    Continuous ((κ.comp (Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom)).comp
      (FiniteIdeleGroup.fractionalIdeal (K := F))) := by
  let f := (κ.comp (Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom)).comp
      (FiniteIdeleGroup.fractionalIdeal (K := F))
  apply continuous_of_continuousAt_one f
  have hopen : IsOpen (FiniteIdeleGroup.integralSubgroup (K := F) : Set (FiniteIdeleGroup F)) :=
    RestrictedProduct.isOpen_forall_mem (_root_.isOpen_finiteLocalUnits F)
  have heq : (fun x : FiniteIdeleGroup F => f x) =ᶠ[𝓝 1] (fun _ => (1 : Circle)) := by
    filter_upwards [hopen.mem_nhds (FiniteIdeleGroup.integralSubgroup.one_mem)] with x hx
    have hi : FiniteIdeleGroup.fractionalIdeal x = 1 := by
      exact MonoidHom.mem_ker.mp (by rwa [FiniteIdeleGroup.fractionalIdeal_ker])
    change κ (Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom
      (FiniteIdeleGroup.fractionalIdeal x)) = 1
    simp [hi]
  exact continuousAt_const.congr_of_eventuallyEq heq

private theorem sRestr_cont (A : SArithmeticData F) : Continuous (sRestriction A) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    apply Continuous.units_map
    exact (continuous_apply w).comp continuous_fst
  · apply continuous_pi
    intro v
    apply Continuous.units_map
    exact (RestrictedProduct.continuous_eval v.val).comp continuous_snd

theorem glued_character_continuous (A : SArithmeticData F) (χ : A.G →* Circle)
    (κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle)
    (Φ : NumberField.IdeleClassGroup (𝓞 F) F →* Circle)
    (heval : ∀ x : NumberField.IdeleGroup (𝓞 F) F,
      Φ (QuotientGroup.mk x) = rawCharacter A χ κ x)
    (hχ : Continuous χ) : Continuous Φ := by
  apply (QuotientGroup.isQuotientMap_mk
    (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  have hext : Continuous (fun x : NumberField.IdeleGroup (𝓞 F) F =>
      κ (exteriorIdealMap A x)) := by
    exact ((finite_char_cont A κ).comp continuous_snd).comp
      (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm.continuous
  have hraw : Continuous (rawCharacter A χ κ) :=
    hext.mul (hχ.comp (sRestr_cont A)).inv
  exact hraw.congr (fun x => (heval x).symm)

end
end DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps

end

section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
private theorem inv_prime_integer (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∈ A.Sf) {x : F} (hx : x ∈ (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)⁻¹) :
    x ∈ A.R := by
  intro w hw
  have hne : v ≠ w := by intro h; subst w; exact hw hv
  have hnotle : ¬ v.asIdeal ≤ w.asIdeal := by
    intro h
    exact hne (HeightOneSpectrum.ext ((v.isMaximal.eq_of_le w.isPrime.ne_top h)))
  obtain ⟨r, hr, hwr⟩ := Set.not_subset.mp hnotle
  have hm := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)).mp hx
    (algebraMap (𝓞 F) F r) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨r, hr, rfl⟩)
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hm
  have hh := w.valuation_le_one (K := F) a
  change (w.valuation F) (algebraMap (𝓞 F) F a) ≤ 1 at hh
  rw [ha, map_mul, (w.valuation_eq_one_iff_notMem (K := F)).mpr hwr, mul_one] at hh
  exact hh

private theorem ext_prime (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∈ A.Sf) :
    (Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom)
      (FractionalIdealGroup.prime v) = 1 := by
  let E := FractionalIdeal.extendedHom (A := 𝓞 F) (K := F) F A.R
  have hi : E ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)⁻¹) ≤ 1 := by
    change Submodule.span A.R _ ≤ (1 : FractionalIdeal A.R⁰ F).val
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxR := inv_prime_integer A v hv hx
    apply (FractionalIdeal.mem_one_iff _).mpr
    refine ⟨⟨x, hxR⟩, ?_⟩
    have hm : (𝓞 F)⁰ ≤ Submonoid.comap (algebraMap (𝓞 F) A.R) A.R⁰ :=
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective (𝓞 F) A.R)
    have hid : IsLocalization.map F (algebraMap (𝓞 F) A.R) hm = RingHom.id F :=
      IsLocalization.map_unique (M := (𝓞 F)⁰) (S := F) (T := A.R⁰) hm (RingHom.id F)
        (fun r => rfl)
    rw [hid]
    rfl
  apply Units.ext
  change E (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) = 1
  apply le_antisymm
  · exact FractionalIdeal.extended_le_one_of_le_one F _ _ FractionalIdeal.coeIdeal_le_one
  · have hh := mul_le_mul_of_nonneg_left hi (show (0 : FractionalIdeal A.R⁰ F) ≤ E (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) from bot_le)
    simpa only [← map_mul, FractionalIdeal.coe_ideal_mul_inv v.asIdeal v.ne_bot, map_one, mul_one] using hh

private theorem finite_component_val (x : NumberField.IdeleGroup (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2 v) : v.adicCompletion F) =
      (x : NumberField.AdeleRing (𝓞 F) F).2 v := by
  rfl

private theorem ext_supported (A : SArithmeticData F) (x : NumberField.IdeleGroup (𝓞 F) F)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      Valued.v ((x : NumberField.AdeleRing (𝓞 F) F).2 v) = 1) : exteriorIdealMap A x = 1 := by
  let a := ((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2
  change (Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom)
    (FiniteIdeleGroup.fractionalIdeal a) = 1
  change (Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom)
    ((FiniteIdeleGroup.valuationVector a).toAdd.prod fun v n => FractionalIdealGroup.prime v ^ n) = 1
  rw [Finsupp.prod, map_prod]
  apply Finset.prod_eq_one
  intro v hv
  by_cases hvs : v ∈ A.Sf
  · rw [map_zpow, ext_prime A v hvs, one_zpow]
  · have ho : (FiniteIdeleGroup.valuationVector a).toAdd v = 0 := by
      change -WithZero.log (Valued.v (a v : v.adicCompletion F)) = 0
      rw [finite_component_val x v, hx v hvs]
      rfl
    simp [ho]

private theorem adic_val (v u : HeightOneSpectrum (𝓞 F)) (z : (v.adicCompletion F)ˣ) :
    ((NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v z : NumberField.AdeleRing (𝓞 F) F).2 u) = Pi.mulSingle v (z : v.adicCompletion F) u := by
  change ((Units.map (NumberField.AdeleRing.ofAdicCompletion (𝓞 F) F v)) z : NumberField.AdeleRing (𝓞 F) F).2 u = _
  rw [Units.coe_map]
  rfl
private theorem inf_finite_val (w : InfinitePlace F) (z : w.Completionˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((NumberField.IdeleGroup.ofCompletion (𝓞 F) F w z : NumberField.AdeleRing (𝓞 F) F).2 v) = 1 := rfl
private theorem ext_inf (A : SArithmeticData F) (w : InfinitePlace F) (z : w.Completionˣ) :
    exteriorIdealMap A (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w z) = 1 := by
  apply ext_supported A
  intro v hv
  rw [inf_finite_val, map_one]
private theorem ext_fin (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (z : (v.adicCompletion F)ˣ)
    (hz : v ∈ A.Sf ∨ Valued.v (z : v.adicCompletion F) = 1) :
    exteriorIdealMap A (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v z) = 1 := by
  apply ext_supported A
  intro u hu
  rw [adic_val]
  by_cases h : u = v
  · subst u
    rw [Pi.mulSingle_eq_same]
    exact hz.resolve_left hu
  · rw [Pi.mulSingle_eq_of_ne h, map_one]

private theorem sr_inf_val (A : SArithmeticData F) (x : NumberField.IdeleGroup (𝓞 F) F)
    (w : InfinitePlace F) : ((sRestriction A x).1 w : w.Completion) = (x : NumberField.AdeleRing (𝓞 F) F).1 w := rfl
private theorem sr_fin_val (A : SArithmeticData F) (x : NumberField.IdeleGroup (𝓞 F) F)
    (v : {v // v ∈ A.Sf}) : ((sRestriction A x).2 v : v.val.adicCompletion F) = (x : NumberField.AdeleRing (𝓞 F) F).2 v.val := rfl

private theorem sr_inf (A : SArithmeticData F) (w : InfinitePlace F) (z : w.Completionˣ) :
    sRestriction A (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w z) = (Pi.mulSingle w z, 1) := by
  apply Prod.ext
  · funext u
    apply Units.ext
    rw [sr_inf_val]
    change ((Units.map (NumberField.AdeleRing.ofCompletion (𝓞 F) F w)) z : NumberField.AdeleRing (𝓞 F) F).1 u = ((Pi.mulSingle (M := fun w : InfinitePlace F => w.Completionˣ) w z u) : u.Completion)
    rw [Units.coe_map]
    change Pi.mulSingle w (z : w.Completion) u = ((Pi.mulSingle (M := fun w : InfinitePlace F => w.Completionˣ) w z u) : u.Completion)
    by_cases h : w = u
    · subst u; simp
    · simp [Pi.mulSingle_eq_of_ne (Ne.symm h)]
  · funext v
    apply Units.ext
    rw [sr_fin_val]
    rfl
private theorem sr_fin (A : SArithmeticData F) (v : {v // v ∈ A.Sf}) (z : (v.val.adicCompletion F)ˣ) :
    sRestriction A (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v.val z) = (1, Pi.mulSingle v z) := by
  apply Prod.ext
  · funext u
    apply Units.ext
    rw [sr_inf_val]
    rfl
  · funext u
    apply Units.ext
    rw [sr_fin_val]
    change ((Units.map (NumberField.AdeleRing.ofAdicCompletion (𝓞 F) F v.val)) z : NumberField.AdeleRing (𝓞 F) F).2 u.val = ((Pi.mulSingle (M := fun v : {v // v ∈ A.Sf} => (v.val.adicCompletion F)ˣ) v z u) : u.val.adicCompletion F)
    rw [Units.coe_map]
    change (RestrictedProduct.mulSingle (fun w => w.adicCompletionIntegers F) v.val (z : v.val.adicCompletion F)) u.val = ((Pi.mulSingle (M := fun v : {v // v ∈ A.Sf} => (v.val.adicCompletion F)ˣ) v z u) : u.val.adicCompletion F)
    by_cases h : v = u
    · subst u; simp
    · have h' : v.val ≠ u.val := fun e => h (Subtype.ext e)
      simp [Pi.mulSingle_eq_of_ne (Ne.symm h), RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_of_ne (Ne.symm h')]
private theorem sr_product (A : SArithmeticData F) (y : A.G) :
    sRestriction A ((∏ w : InfinitePlace F, NumberField.IdeleGroup.ofCompletion (𝓞 F) F w (y.1 w)) *
      (∏ v : {v // v ∈ A.Sf}, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v.val (y.2 v))) = y := by
  simp only [map_mul, map_prod, sr_inf, sr_fin]
  apply Prod.ext <;> simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_prod, Prod.snd_prod, Finset.attach_eq_univ,
    Finset.prod_const_one, mul_one, one_mul, Finset.univ_prod_mulSingle]
private theorem sr_outside (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf)
    (z : (v.adicCompletion F)ˣ) : sRestriction A (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v z) = 1 := by
  apply Prod.ext
  · funext w
    apply Units.ext
    rw [sr_inf_val]
    rfl
  · funext u
    apply Units.ext
    rw [sr_fin_val, adic_val]
    have h : u.val ≠ v := fun e => hv (e ▸ u.property)
    exact Pi.mulSingle_eq_of_ne h _

theorem glued_character_local_components (A : SArithmeticData F) (χ : A.G →* Circle)
    (κ : (FractionalIdeal A.R⁰ F)ˣ →* Circle)
    (Φ : NumberField.IdeleClassGroup (𝓞 F) F →* Circle)
    (heval : ∀ x : NumberField.IdeleGroup (𝓞 F) F,
      Φ (QuotientGroup.mk x) = rawCharacter A χ κ x) :
    (∀ y : A.G,
      (∏ w : InfinitePlace F,
        (Φ (NumberField.IdeleClassGroup.ofCompletion (𝓞 F) F w (y.1 w)))⁻¹) *
      (∏ v : {v // v ∈ A.Sf},
        (Φ (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 F) F v.val (y.2 v)))⁻¹) = χ y) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)), v ∉ A.Sf →
      ∀ x : (v.adicCompletion F)ˣ, Valued.v (x : v.adicCompletion F) = 1 →
        Φ (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x) = 1) := by
  constructor
  · intro y
    let x : NumberField.IdeleGroup (𝓞 F) F :=
      (∏ w : InfinitePlace F, NumberField.IdeleGroup.ofCompletion (𝓞 F) F w (y.1 w)) *
      (∏ v : {v // v ∈ A.Sf}, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v.val (y.2 v))
    have hs : sRestriction A x = y := sr_product A y
    have he : exteriorIdealMap A x = 1 := by
      simp only [x, map_mul, map_prod, ext_inf]
      simp only [ext_fin A _ _ (Or.inl (Subtype.property _)), Finset.prod_const_one, mul_one]
    have hh := heval x
    have hf : Φ (QuotientGroup.mk x) = (χ y)⁻¹ := by
      change Φ (QuotientGroup.mk x) = κ (exteriorIdealMap A x) * (χ (sRestriction A x))⁻¹ at hh
      simpa only [he, map_one, hs, one_mul] using hh
    have hi := congrArg Inv.inv hf
    rw [inv_inv] at hi
    rw [← hi]
    change _ = (Φ ((QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)) x))⁻¹
    simp only [x, map_mul, map_prod, Finset.prod_inv_distrib, mul_inv_rev,
      NumberField.IdeleClassGroup.ofCompletion, NumberField.IdeleClassGroup.ofAdicCompletion,
      MonoidHom.comp_apply]
    exact mul_comm _ _
  · intro v hv x hx
    change Φ (QuotientGroup.mk (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v x)) = 1
    rw [heval]
    change κ (exteriorIdealMap A (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v x)) *
      (χ (sRestriction A (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v x)))⁻¹ = 1
    rw [ext_fin A v x (Or.inr hx), sr_outside A v hv x]
    simp

end
end DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps

end

section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem exterior_representative_maps (A : SArithmeticData F) (I : A.Exterior)
    (x : NumberField.IdeleGroup (𝓞 F) F)
    (hw : ∀ w : InfinitePlace F, x.val.1 w = 1)
    (hs : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ A.Sf → x.val.2 v = 1)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      Valued.v (x.val.2 v) =
        (((Multiplicative.ofAdd (-(idealPrimeExponent v.asIdeal I.val : ℤ))) :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    sRestriction A x = 1 ∧
    exteriorIdealMap A x =
      Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom
        (Units.mk0 (I.val : FractionalIdeal (𝓞 F)⁰ F)
          (FractionalIdeal.coeIdeal_ne_zero.mpr I.property.1)) := by
  have hr : sRestriction A x = 1 := by
    apply Prod.ext
    · funext w
      apply Units.ext
      exact hw w
    · funext v
      apply Units.ext
      exact hs v.val v.property
  have hi : FiniteIdeleGroup.fractionalIdeal
      (((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2) =
      Units.mk0 (I.val : FractionalIdeal (𝓞 F)⁰ F)
        (FractionalIdeal.coeIdeal_ne_zero.mpr I.property.1) := by
    apply FractionalIdealGroup.ext_count
    intro v
    rw [show FractionalIdeal.count F v
        ((FiniteIdeleGroup.fractionalIdeal
          (((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2) : FractionalIdealGroup F) :
            FractionalIdeal (𝓞 F)⁰ F) =
        (FiniteIdeleGroup.localOrder v
          (((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2 v)).toAdd from by
          change FractionalIdeal.count F v
            ((FractionalIdealGroup.factorization (FiniteIdeleGroup.valuationVector
              (((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2)) : FractionalIdealGroup F) :
                FractionalIdeal (𝓞 F)⁰ F) = _
          rw [FractionalIdealGroup.count_factorization]
          rfl]
    rw [show FractionalIdeal.count F v
        ((Units.mk0 (I.val : FractionalIdeal (𝓞 F)⁰ F)
            (FractionalIdeal.coeIdeal_ne_zero.mpr I.property.1) : FractionalIdealGroup F) :
          FractionalIdeal (𝓞 F)⁰ F) = (idealPrimeExponent v.asIdeal I.val : ℤ) from by
            exact (show FractionalIdeal.count F v (I.val : FractionalIdeal (𝓞 F)⁰ F) = _ from by
              rw [FractionalIdeal.count_coe F v I.property.1]
              unfold idealPrimeExponent
              congr 1
              rw [Associates.factors_mk _ I.property.1,
                Associates.count_some (Associates.irreducible_mk.mpr v.irreducible),
                ← Multiset.count_map_eq_count' _ _ Subtype.val_injective,
                Associates.map_subtype_coe_factors',
                UniqueFactorizationMonoid.factors_eq_normalizedFactors,
                ← Multiset.count_map_eq_count' _ _ (Associates.mk_injective (M := Ideal (𝓞 F)))])]
    rw [FiniteIdeleGroup.localOrder_apply]
    by_cases h : v ∈ A.Sf
    · have hi : I.val ⊔ v.asIdeal = ⊤ := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v h
      have hz : idealPrimeExponent v.asIdeal I.val = 0 := by
        unfold idealPrimeExponent
        apply Multiset.count_eq_zero.mpr
        intro hp
        have hd : v.asIdeal ∣ I.val := (UniqueFactorizationMonoid.mem_normalizedFactors_iff I.property.1).mp hp |>.2
        have hle : I.val ≤ v.asIdeal := Ideal.le_of_dvd hd
        have hh : v.asIdeal = ⊤ := by simpa [sup_eq_right.mpr hle] using hi
        exact v.isPrime.ne_top hh
      rw [hz]
      have hx : (((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2 v).val = 1 := by
        simpa only [show (((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2 v).val = x.val.2 v from rfl] using hs v h
      simp [hx]
    · have hx : (((_root_.IdeleGroup.equivAdeleRingUnits (K := F)).symm x).2 v).val = x.val.2 v := rfl
      rw [hx, hv v h]
      change -(-(idealPrimeExponent v.asIdeal I.val : ℤ)) = _
      exact neg_neg _
  constructor
  · exact hr
  · exact congrArg (Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom) hi

end
end DedekindZetaZeroFree.SArithmeticData.ClassCharacterSteps

end

section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData

noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

abbrev ArithmeticIdeleClasses (A : SArithmeticData F) :=
  NumberField.IdeleClassGroup (𝓞 F) F

def IdeleCharacterHasFiniteOrder (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : A.ArithmeticIdeleClasses, Φ x ^ n = 1

def ideleInfiniteComponent (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) (w : InfinitePlace F) :
    w.Completionˣ →* Circle :=
  Φ.comp (NumberField.IdeleClassGroup.ofCompletion (𝓞 F) F w)

def ideleFiniteComponent (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* Circle :=
  Φ.comp (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 F) F v)

def IdeleCharacterUnramifiedOutside (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)), v ∉ A.Sf →
    ∀ x : (v.adicCompletion F)ˣ,
      Valued.v (x : v.adicCompletion F) = 1 → A.ideleFiniteComponent Φ v x = 1

def ideleSInverseProduct (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) (y : A.G) : Circle :=
  (∏ w : InfinitePlace F, (A.ideleInfiniteComponent Φ w (y.1 w))⁻¹) *
    ∏ v : {v // v ∈ A.Sf}, (A.ideleFiniteComponent Φ v.val (y.2 v))⁻¹

def RepresentsExteriorIdeal (A : SArithmeticData F) (I : A.Exterior)
    (x : NumberField.IdeleGroup (𝓞 F) F) : Prop :=
  (∀ w : InfinitePlace F, x.val.1 w = 1) ∧
  (∀ v : HeightOneSpectrum (𝓞 F), v ∈ A.Sf → x.val.2 v = 1) ∧
  (∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
    Valued.v (x.val.2 v) =
      (((Multiplicative.ofAdd (-(idealPrimeExponent v.asIdeal I.val : ℤ))) :
        Multiplicative ℤ) : WithZero (Multiplicative ℤ)))

theorem exists_exterior_ideal_representative (A : SArithmeticData F)
    (I : A.Exterior) :
    ∃ x : NumberField.IdeleGroup (𝓞 F) F, A.RepresentsExteriorIdeal I x := by
  have hs : {v : HeightOneSpectrum (𝓞 F) |
      idealPrimeExponent v.asIdeal I.val ≠ 0}.Finite := by
    have hf := (DedekindZetaZeroFree.idealPrimeSupport I.val).finite_toSet
    have hp := Set.Finite.preimage
      HeightOneSpectrum.asIdeal_injective.injOn hf
    apply hp.subset
    intro v hv
    change v.asIdeal ∈ (UniqueFactorizationMonoid.normalizedFactors I.val).toFinset
    rw [Multiset.mem_toFinset, ← Multiset.count_ne_zero]
    exact hv
  let a : _root_.FiniteIdeleGroup F :=
    ⟨fun v => if v ∈ A.Sf then 1 else
      FiniteIdeleGroup.chosenLocalOrderSection v (idealPrimeExponent v.asIdeal I.val), by
        filter_upwards [hs.eventually_cofinite_notMem] with v hv
        dsimp
        split_ifs
        · exact one_mem _
        · apply (FiniteIdeleGroup.localOrder_eq_zero_iff v _).mp
          rw [FiniteIdeleGroup.localOrder_chosenLocalOrderSection]
          simp_all⟩
  refine ⟨_root_.IdeleGroup.equivAdeleRingUnits (1, a), ?_, ?_, ?_⟩
  · intro w
    rfl
  · intro v hv
    change ((_root_.IdeleGroup.finiteEquivFiniteAdeleUnits a :
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) v = 1
    have he : ((_root_.IdeleGroup.finiteEquivFiniteAdeleUnits a :
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) v = (a v : v.adicCompletion F) := rfl
    rw [he]
    have ha : a v = 1 := by
      change (if v ∈ A.Sf then 1 else _) = _
      rw [if_pos hv]
    rw [ha]
    rfl
  · intro v hv
    change Valued.v (↑(a v) : v.adicCompletion F) = _
    have ha : a v = FiniteIdeleGroup.chosenLocalOrderSection v
      (idealPrimeExponent v.asIdeal I.val) := by
      change (if v ∈ A.Sf then 1 else _) = _
      rw [if_neg hv]
    rw [ha]
    have h := FiniteIdeleGroup.localOrder_chosenLocalOrderSection v
      (idealPrimeExponent v.asIdeal I.val)
    rw [FiniteIdeleGroup.localOrder_apply] at h
    have h' := congrArg (fun z : ℤ => WithZero.exp (-z)) h
    have hz : Valued.v (FiniteIdeleGroup.chosenLocalOrderSection v
        (idealPrimeExponent v.asIdeal I.val) : v.adicCompletion F) ≠ 0 := by simp
    rw [neg_neg, WithZero.exp_log hz] at h'
    exact h'

structure ClassCharacterExtension (A : SArithmeticData F) (B : Subgroup A.V)
    (φ : B →* ℂˣ) where
  ideleCharacter : A.ArithmeticIdeleClasses →* Circle
  continuous : Continuous ideleCharacter
  finiteOrder : A.IdeleCharacterHasFiniteOrder ideleCharacter
  unramified : A.IdeleCharacterUnramifiedOutside ideleCharacter
  idealValue : A.Exterior → Circle
  ideal_multiplicative : ∀ I J K : A.Exterior, K.val = I.val * J.val →
    idealValue K = idealValue I * idealValue J
  ideal_idelic : ∀ (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F),
    A.RepresentsExteriorIdeal I x →
      ideleCharacter (QuotientGroup.mk x) = idealValue I
  allowed_value : ∀ (I : A.Exterior) (a : Fˣ) (r : A.R)
    (ha : A.IsAllowed B a), A.Generates I r → (a : F) = (r : F) →
      Circle.toUnits (idealValue I) = φ ⟨A.sClass a, ha⟩
  local_split_value : ∀ (y : A.G) (p : A.E × B),
    QuotientGroup.mk y = (p.1 : A.V) * (p.2 : A.V) →
      Circle.toUnits (A.ideleSInverseProduct ideleCharacter y) = φ p.2
  ideal_local : ∀ (I : A.Exterior) (a : Fˣ) (r : A.R),
    A.IsAllowed B a → A.Generates I r → (a : F) = (r : F) →
      idealValue I = A.ideleSInverseProduct ideleCharacter (A.diagonal a)
  unit_trivial : ∀ ε : A.U,
    A.ideleSInverseProduct ideleCharacter (A.diagonal ε.val) = 1

namespace ClassCharacterGluing

variable (A : SArithmeticData F) (B : Subgroup A.V)
variable (hFactor : ∀ v : A.V, ∃! p : A.E × B, (p.1 : A.V) * (p.2 : A.V) = v)
def splitting : A.E × B ≃* A.V :=
  MulEquiv.ofBijective
    ({ toFun := fun p => (p.1 : A.V) * (p.2 : A.V)
       map_one' := by simp
       map_mul' := by
         intro p q
         change ((p.1 : A.V) * q.1) * ((p.2 : A.V) * q.2) = _
         exact mul_mul_mul_comm (p.1 : A.V) (q.1 : A.V) (p.2 : A.V) (q.2 : A.V) } : A.E × B →* A.V)
    ⟨fun p q h => (hFactor _).unique rfl h.symm,
      fun v => ⟨(hFactor v).exists.choose, (hFactor v).exists.choose_spec⟩⟩

def projection : A.V →* B :=
  (MonoidHom.snd A.E B).comp (splitting A B hFactor).symm.toMonoidHom

lemma projection_split (p : A.E × B) :
    projection A B hFactor ((p.1 : A.V) * (p.2 : A.V)) = p.2 := by
  change ((splitting A B hFactor).symm ((splitting A B hFactor) p)).2 = p.2
  rw [MulEquiv.symm_apply_apply]

lemma sixth_power (v : A.V) : v ^ 6 = 1 := by
  induction v using QuotientGroup.induction_on with
  | H y =>
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩

lemma character_sixth (φ : B →* ℂˣ) (b : B) : φ b ^ 6 = 1 := by
  rw [← map_pow]
  have hb : b ^ 6 = 1 := by
    apply Subtype.ext
    exact sixth_power A (b : A.V)
  rw [hb, map_one]

lemma character_norm (φ : B →* ℂˣ) (b : B) : ‖(φ b : ℂ)‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6 : ℕ) ≠ 0)).mp
  rw [← Complex.norm_pow]
  have h := congrArg (fun u : ℂˣ => (u : ℂ)) (character_sixth A B φ b)
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, norm_one] using congrArg (fun z : ℂ => ‖z‖) h

def circleCharacter (φ : B →* ℂˣ) : B →* Circle where
  toFun b := ⟨φ b, by
    change (φ b : ℂ) ∈ Metric.sphere 0 1
    simpa using character_norm A B φ b⟩
  map_one' := by apply Subtype.ext; exact congrArg (fun u : ℂˣ => (u : ℂ)) φ.map_one
  map_mul' x y := by apply Subtype.ext; exact congrArg (fun u : ℂˣ => (u : ℂ)) (φ.map_mul x y)

lemma circleCharacter_toUnits (φ : B →* ℂˣ) (b : B) :
    Circle.toUnits (circleCharacter A B φ b) = φ b := by
  apply Units.ext
  rfl

def localCharacter (φ : B →* ℂˣ) : A.G →* Circle :=
  ((circleCharacter A B φ).comp (projection A B hFactor)).comp
    (QuotientGroup.mk' A.sixthPowers)

lemma localCharacter_split (φ : B →* ℂˣ) (y : A.G) (p : A.E × B)
    (hp : QuotientGroup.mk y = (p.1 : A.V) * (p.2 : A.V)) :
    Circle.toUnits (localCharacter A B hFactor φ y) = φ p.2 := by
  change Circle.toUnits (circleCharacter A B φ
    (projection A B hFactor (QuotientGroup.mk y))) = _
  rw [hp, projection_split, circleCharacter_toUnits]

lemma localCharacter_unit (φ : B →* ℂˣ) (u : A.U) :
    localCharacter A B hFactor φ (A.diagonal u.val) = 1 := by
  have hu : A.sClass u.val ∈ A.E :=
    ⟨A.diagonal u.val, ⟨u.val, u.property, rfl⟩, rfl⟩
  have hp : projection A B hFactor (A.sClass u.val) = 1 := by
    simpa using projection_split A B hFactor (⟨A.sClass u.val, hu⟩, 1)
  change circleCharacter A B φ (projection A B hFactor (A.sClass u.val)) = 1
  rw [hp, map_one]

lemma localCharacter_sixth (φ : B →* ℂˣ) (y : A.G) :
    localCharacter A B hFactor φ y ^ 6 = 1 := by
  apply Subtype.ext
  change (φ (projection A B hFactor (QuotientGroup.mk y)) : ℂ) ^ 6 = 1
  exact congrArg (fun u : ℂˣ => (u : ℂ))
    (character_sixth A B φ (projection A B hFactor (QuotientGroup.mk y)))

variable (A : SArithmeticData F)

def principalMap : Fˣ →* (FractionalIdeal A.R⁰ F)ˣ :=
  Units.map ({ toFun := FractionalIdeal.spanSingleton A.R⁰
               map_one' := FractionalIdeal.spanSingleton_one
               map_mul' := fun x y => (FractionalIdeal.spanSingleton_mul_spanSingleton _ _).symm }
    : F →* FractionalIdeal A.R⁰ F)

lemma principalMap_surjective (hCl : Subsingleton (ClassGroup A.R)) :
    Function.Surjective (principalMap A) := by
  letI : Subsingleton (ClassGroup A.R) := hCl
  intro I
  letI : Submodule.IsPrincipal ((I : FractionalIdeal A.R⁰ F) : Submodule A.R F) :=
    ClassGroup.isPrincipal_coeSubmodule_of_isUnit _ I.isUnit
  let x : F := Submodule.IsPrincipal.generator ((I : FractionalIdeal A.R⁰ F) : Submodule A.R F)
  have hx : (I : FractionalIdeal A.R⁰ F) = FractionalIdeal.spanSingleton A.R⁰ x :=
    FractionalIdeal.eq_spanSingleton_of_principal _
  have hx0 : x ≠ 0 := by
    intro hz
    apply I.ne_zero
    simpa [hz] using hx
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  exact hx.symm

variable (B : Subgroup A.V)
variable (hFactor : ∀ v : A.V, ∃! p : A.E × B, (p.1 : A.V) * (p.2 : A.V) = v)
lemma principalMap_ker (φ : B →* ℂˣ) :
    (principalMap A).ker ≤ ((localCharacter A B hFactor φ).comp A.diagonal).ker := by
  intro a ha
  have hs : FractionalIdeal.spanSingleton A.R⁰ (1 : F) =
      FractionalIdeal.spanSingleton A.R⁰ (a : F) := by
    change principalMap A a = 1 at ha
    exact FractionalIdeal.spanSingleton_one.trans (congrArg Units.val ha).symm
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hs
  let ε : A.U := A.unitEquiv.symm u
  have huval : (ε.val : F) = ((u : A.R) : F) := by
    simp [ε, unitEquiv, Set.unitEquivUnitsInteger]
  have hae : a = ε.val := by
    apply Units.ext
    rw [huval]
    change (a : F) = algebraMap A.R F (u : A.R)
    simpa only [Units.smul_def, Algebra.smul_def, mul_one] using hu.symm
  change localCharacter A B hFactor φ (A.diagonal a) = 1
  rw [hae, localCharacter_unit]

def fractionalIdealCharacter (hCl : Subsingleton (ClassGroup A.R)) (φ : B →* ℂˣ) :
    (FractionalIdeal A.R⁰ F)ˣ →* Circle :=
  (principalMap A).liftOfSurjective (principalMap_surjective A hCl)
    ⟨(localCharacter A B hFactor φ).comp A.diagonal, principalMap_ker A B hFactor φ⟩

lemma fractionalIdealCharacter_principal (hCl : Subsingleton (ClassGroup A.R))
    (φ : B →* ℂˣ) (a : Fˣ) :
    fractionalIdealCharacter A B hFactor hCl φ (principalMap A a) =
      localCharacter A B hFactor φ (A.diagonal a) := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

lemma fractionalIdealCharacter_sixth (hCl : Subsingleton (ClassGroup A.R))
    (φ : B →* ℂˣ) (I : (FractionalIdeal A.R⁰ F)ˣ) :
    fractionalIdealCharacter A B hFactor hCl φ I ^ 6 = 1 := by
  obtain ⟨a, rfl⟩ := principalMap_surjective A hCl I
  rw [fractionalIdealCharacter_principal]
  exact localCharacter_sixth A B hFactor φ _

lemma fractionalIdealCharacter_allowed (hCl : Subsingleton (ClassGroup A.R))
    (φ : B →* ℂˣ) (I : (FractionalIdeal A.R⁰ F)ˣ) (a : Fˣ)
    (ha : A.IsAllowed B a)
    (hI : (I : FractionalIdeal A.R⁰ F) = FractionalIdeal.spanSingleton A.R⁰ (a : F)) :
    Circle.toUnits (fractionalIdealCharacter A B hFactor hCl φ I) = φ ⟨A.sClass a, ha⟩ := by
  have hp : I = principalMap A a := Units.ext hI
  rw [hp, fractionalIdealCharacter_principal]
  apply localCharacter_split A B hFactor φ _ (1, ⟨A.sClass a, ha⟩)
  exact (one_mul (A.sClass a)).symm

variable (A : SArithmeticData F)
def exteriorFractionalUnit (I : A.Exterior) : (FractionalIdeal A.R⁰ F)ˣ :=
  Units.map (FractionalIdeal.extendedHom (K := F) F A.R).toMonoidHom
    (Units.mk0 (I.val : FractionalIdeal (𝓞 F)⁰ F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr I.property.1))

lemma exteriorFractionalUnit_val (I : A.Exterior) :
    (exteriorFractionalUnit A I : FractionalIdeal A.R⁰ F) = A.extendIdeal I := by
  change FractionalIdeal.extendedHom (K := F) F A.R (I.val : FractionalIdeal (𝓞 F)⁰ F) = _
  rw [FractionalIdeal.extendedHom_coeIdeal_eq_map]
  rfl

lemma exteriorFractionalUnit_mul (I J K : A.Exterior) (hK : K.val = I.val * J.val) :
    exteriorFractionalUnit A K = exteriorFractionalUnit A I * exteriorFractionalUnit A J := by
  apply Units.ext
  simp only [Units.val_mul, exteriorFractionalUnit_val, ← FractionalIdeal.coeIdeal_mul]
  congr 1
  change Ideal.map _ K.val = Ideal.map _ I.val * Ideal.map _ J.val
  rw [hK, Ideal.map_mul]

variable (B : Subgroup A.V)
variable (hFactor : ∀ v : A.V, ∃! p : A.E × B, (p.1 : A.V) * (p.2 : A.V) = v)
def exteriorIdealValue (hCl : Subsingleton (ClassGroup A.R)) (φ : B →* ℂˣ)
    (I : A.Exterior) : Circle :=
  fractionalIdealCharacter A B hFactor hCl φ (exteriorFractionalUnit A I)

lemma exteriorIdealValue_mul (hCl : Subsingleton (ClassGroup A.R)) (φ : B →* ℂˣ)
    (I J K : A.Exterior) (hK : K.val = I.val * J.val) :
    exteriorIdealValue A B hFactor hCl φ K =
      exteriorIdealValue A B hFactor hCl φ I * exteriorIdealValue A B hFactor hCl φ J := by
  unfold exteriorIdealValue
  rw [exteriorFractionalUnit_mul A I J K hK, map_mul]

lemma exteriorFractionalUnit_generator (I : A.Exterior) (a : Fˣ) (r : A.R)
    (hr : A.Generates I r) (har : (a : F) = (r : F)) :
    exteriorFractionalUnit A I = principalMap A a := by
  apply Units.ext
  rw [exteriorFractionalUnit_val, ← hr.2]
  change (Ideal.span {r} : FractionalIdeal A.R⁰ F) =
    FractionalIdeal.spanSingleton A.R⁰ (a : F)
  rw [FractionalIdeal.coeIdeal_span_singleton]
  congr 1
  exact har.symm

lemma exteriorIdealValue_local (hCl : Subsingleton (ClassGroup A.R)) (φ : B →* ℂˣ)
    (I : A.Exterior) (a : Fˣ) (r : A.R)
    (hr : A.Generates I r) (har : (a : F) = (r : F)) :
    exteriorIdealValue A B hFactor hCl φ I =
      localCharacter A B hFactor φ (A.diagonal a) := by
  unfold exteriorIdealValue
  rw [exteriorFractionalUnit_generator A I a r hr har, fractionalIdealCharacter_principal]

lemma exteriorIdealValue_allowed (hCl : Subsingleton (ClassGroup A.R)) (φ : B →* ℂˣ)
    (I : A.Exterior) (a : Fˣ) (r : A.R) (ha : A.IsAllowed B a)
    (hr : A.Generates I r) (har : (a : F) = (r : F)) :
    Circle.toUnits (exteriorIdealValue A B hFactor hCl φ I) = φ ⟨A.sClass a, ha⟩ := by
  apply fractionalIdealCharacter_allowed A B hFactor hCl φ _ a ha
  have h := congrArg Units.val (exteriorFractionalUnit_generator A I a r hr har)
  exact h

end ClassCharacterGluing

theorem exists_class_character_extension (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (B : Subgroup A.V)
    (hSplit : IsCompl A.E B)
    (hFactor : ∀ v : A.V, ∃! p : A.E × B, (p.1 : A.V) * (p.2 : A.V) = v)
    (φ : B →* ℂˣ) (hφ : (Set.range φ).Finite) :
    Nonempty (A.ClassCharacterExtension B φ) := by
  let χ := ClassCharacterGluing.localCharacter A B hFactor φ
  let κ := ClassCharacterGluing.fractionalIdealCharacter A B hFactor hCl φ
  have hχ : ∀ y : A.G, χ y ^ 6 = 1 :=
    ClassCharacterGluing.localCharacter_sixth A B hFactor φ
  have hκ : ∀ I : (FractionalIdeal A.R⁰ F)ˣ, κ I ^ 6 = 1 :=
    ClassCharacterGluing.fractionalIdealCharacter_sixth A B hFactor hCl φ
  have hprincipal : ∀ a : Fˣ,
      κ (ClassCharacterSteps.principalIdealMap A a) = χ (A.diagonal a) :=
    ClassCharacterGluing.fractionalIdealCharacter_principal A B hFactor hCl φ
  obtain ⟨Φ, heval, hΦ⟩ :=
    ClassCharacterSteps.glue_on_idele_classes A χ κ hprincipal 6 hχ hκ
  have hcontinuous : Continuous Φ :=
    ClassCharacterSteps.glued_character_continuous A χ κ Φ heval
      (ClassCharacterSteps.local_character_continuous A χ hχ)
  obtain ⟨hlocal, hunramified⟩ :=
    ClassCharacterSteps.glued_character_local_components A χ κ Φ heval
  have hlocal' : ∀ y : A.G, A.ideleSInverseProduct Φ y = χ y := hlocal
  refine ⟨{
    ideleCharacter := Φ
    continuous := hcontinuous
    finiteOrder := ⟨6, by decide, hΦ⟩
    unramified := hunramified
    idealValue := ClassCharacterGluing.exteriorIdealValue A B hFactor hCl φ
    ideal_multiplicative :=
      ClassCharacterGluing.exteriorIdealValue_mul A B hFactor hCl φ
    ideal_idelic := ?_
    allowed_value := ClassCharacterGluing.exteriorIdealValue_allowed A B hFactor hCl φ
    local_split_value := ?_
    ideal_local := ?_
    unit_trivial := ?_ }⟩
  · intro I x hx
    obtain ⟨hs, hI⟩ :=
      ClassCharacterSteps.exterior_representative_maps A I x hx.1 hx.2.1 hx.2.2
    rw [heval]
    change κ (ClassCharacterSteps.exteriorIdealMap A x) *
      (χ (ClassCharacterSteps.sRestriction A x))⁻¹ = _
    rw [hs, map_one, inv_one, mul_one, hI]
    rfl
  · intro y p hp
    rw [hlocal']
    exact ClassCharacterGluing.localCharacter_split A B hFactor φ y p hp
  · intro I a r ha hr har
    rw [hlocal']
    exact ClassCharacterGluing.exteriorIdealValue_local A B hFactor hCl φ I a r hr har
  · intro ε
    rw [hlocal']
    exact ClassCharacterGluing.localCharacter_unit A B hFactor φ ε

end
end DedekindZetaZeroFree.SArithmeticData

end
