module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IdealIdelesAndLocalFactors
public import DedekindZetaZeroFree.Arithmetic.Kummer.HilbertPairingLagrangianComplement
public import DedekindZetaZeroFree.Adeles.Characters.PrimaryIdealPhase
public import DedekindZetaZeroFree.Metaplectic.Weil.CubicCorrection.CharacterExtension
public import DedekindZetaZeroFree.Metaplectic.Weil.CubicCorrection.PrimeGaussIdentities

@[expose] public section

section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

private lemma count_eq (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (idealPrimeExponent v.asIdeal I : ℤ) := by
  rw [FractionalIdeal.count_coe F v hI]
  unfold idealPrimeExponent
  congr 1
  rw [Associates.factors_mk _ hI,
    Associates.count_some (Associates.irreducible_mk.mpr v.irreducible),
    ← Multiset.count_map_eq_count' _ _ Subtype.val_injective,
    Associates.map_subtype_coe_factors', UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    ← Multiset.count_map_eq_count' _ _ (Associates.mk_injective (M := Ideal (𝓞 F)))]

private lemma exterior_coprime (A : SArithmeticData F) (I : A.Exterior) :
    I.val ⊔ A.modulus = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (I.val ⊔ A.modulus) h
  have hp0 : p ≠ ⊥ := by
    intro he
    apply I.property.1
    apply bot_unique
    have hh : I.val ≤ p := le_trans le_sup_left hle
    simpa only [he] using hh
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp.isPrime, hp0⟩
  have hv : v ∈ A.Sf := A.modulus_support v (le_trans le_sup_right hle)
  have hi := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hv
  have : I.val ⊔ v.asIdeal ≤ p := sup_le (le_trans le_sup_left hle) le_rfl
  rw [hi] at this
  exact hp.ne_top (top_unique this)

private lemma representative_fractional (A : SArithmeticData F) (I : A.Exterior)
    (x : NumberField.IdeleGroup (𝓞 F) F) (hx : A.RepresentsExteriorIdeal I x) :
    _root_.IdeleGroup.fractionalIdeal ((_root_.IdeleGroup.equivAdeleRingUnits).symm x) =
      RayClassBridge.integralUnit F I.val I.property.1 := by
  apply _root_.FractionalIdealGroup.ext_count
  intro v
  change FractionalIdeal.count F v
    ((FractionalIdealGroup.factorization (FiniteIdeleGroup.valuationVector
      (((_root_.IdeleGroup.equivAdeleRingUnits).symm x).2))) : FractionalIdeal _ F) = _
  rw [FractionalIdealGroup.count_factorization]
  change (FiniteIdeleGroup.localOrder v (((_root_.IdeleGroup.equivAdeleRingUnits).symm x).2 v)).toAdd =
    FractionalIdeal.count F v (I.val : FractionalIdeal _ F)
  rw [count_eq I.val I.property.1 v, FiniteIdeleGroup.localOrder_apply]
  change -WithZero.log (Valued.v (x.val.2 v)) = _
  by_cases hv : v ∈ A.Sf
  · rw [hx.2.1 v hv]
    have hi := (A.exterior_iff ⟨I.val, I.property.1⟩).mp I.property.2 v hv
    have hn : ¬ v.asIdeal ∣ I.val := by
      intro hh
      have ht := sup_le (Ideal.dvd_iff_le.mp hh) le_rfl
      rw [hi] at ht
      exact v.isMaximal.ne_top (top_unique ht)
    have hz : (Associates.mk v.asIdeal).count (Associates.mk I.val).factors = 0 := by
      simpa only [ne_eq, not_not] using (mt (Associates.count_ne_zero_iff_dvd I.property.1 v.irreducible).mp hn)
    have hh := FractionalIdeal.count_coe F v I.property.1
    rw [hz] at hh
    rw [← count_eq I.val I.property.1 v, hh]
    simp
  · rw [hx.2.2 v hv]
    change -WithZero.log (WithZero.exp (-(idealPrimeExponent v.asIdeal I.val : ℤ))) = _
    rw [WithZero.log_exp, neg_neg]

private lemma representative_primeTo (A : SArithmeticData F) (I : A.Exterior)
    (x : NumberField.IdeleGroup (𝓞 F) F) (hx : A.RepresentsExteriorIdeal I x) :
    (_root_.IdeleGroup.equivAdeleRingUnits).symm x ∈ RayClass.idelePrimeToModulusSubgroup
      (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
        (RayClassBridge.narrowIdealModulus F A.modulus A.modulus_ne_zero)) := by
  constructor
  · have h1 : ((_root_.IdeleGroup.equivAdeleRingUnits).symm x).1 = 1 := by
      apply Units.ext
      funext w
      exact hx.1 w
    rw [h1]
    exact one_mem _
  · intro v hv
    have hv' : v ∈ A.Sf := by
      apply A.modulus_support
      have hs := RayClassBridge.narrowIdealModulus_support F A.modulus A.modulus_ne_zero
      exact (Set.ext_iff.mp hs v).mp hv
    have h1 : ((_root_.IdeleGroup.equivAdeleRingUnits).symm x).2 v = 1 := by
      apply Units.ext
      exact hx.2.1 v hv'
    rw [h1]
    exact one_mem _

private lemma representative_evaluation (A : SArithmeticData F) (η : RayClassCharacter F A.modulus)
    (x : NumberField.IdeleGroup (𝓞 F) F) (I : A.Exterior)
    (hx : A.RepresentsExteriorIdeal I x) :
    (RayClassBridge.ideleClassCharacter F
      (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12)
      A.modulus A.modulus_ne_zero η
      (QuotientGroup.mk ((_root_.IdeleGroup.equivAdeleRingUnits).symm x)) : ℂ) = η I.val := by
  let m := RayClassBridge.narrowIdealModulus F A.modulus A.modulus_ne_zero
  let m' := ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F m
  let a : RayClass.idelePrimeToModulusSubgroup m' :=
    ⟨(_root_.IdeleGroup.equivAdeleRingUnits).symm x, representative_primeTo A I x hx⟩
  have hc := exterior_coprime A I
  have hm : RayClass.primeToIdealMap m' a =
      RayClassBridge.integralPrimeTo F A.modulus A.modulus_ne_zero I.val I.property.1 hc := by
    apply Subtype.ext
    exact representative_fractional A I x hx
  have he : ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginal F m
      (RayClassBridge.integralRayClass F A.modulus A.modulus_ne_zero I.val I.property.1 hc) =
      RayClass.idealRayProjection m' a := by
    rw [RayClass.idealRayProjection, MonoidHom.comp_apply, hm]
    rfl
  have hh : (ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F m).symm
      (QuotientGroup.mk' m'.congruenceSubgroup (QuotientGroup.mk' (_root_.IdeleGroup.principalSubgroup F) a.val)) =
      RayClassBridge.integralRayClass F A.modulus A.modulus_ne_zero I.val I.property.1 hc := by
    apply (ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F m).injective
    rw [MulEquiv.apply_symm_apply]
    apply (RayClass.rayClassGroupEquivIdealRayClassGroup m').injective
    rw [GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo]
    change _ = (RayClass.rayClassGroupEquivIdealRayClassGroup m')
      ((RayClass.rayClassGroupEquivIdealRayClassGroup m').symm
        (ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginal F m _))
    rw [MulEquiv.apply_symm_apply]
    exact he.symm
  change (RayClassBridge.rayCharacter F (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12) A.modulus A.modulus_ne_zero η
    ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F m).symm
      (QuotientGroup.mk' m'.congruenceSubgroup (QuotientGroup.mk' (_root_.IdeleGroup.principalSubgroup F) a.val))) : ℂ) = _
  rw [hh]
  exact RayClassBridge.rayCharacter_integral F _ A.modulus A.modulus_ne_zero η I.val I.property.1 hc

private lemma infinite_comparison (w : InfinitePlace F) (z : w.Completionˣ) :
    _root_.IdeleGroup.ideleClassGroupEquivMathlib F (_root_.IdeleGroup.infinitePlaceIdeleClass w z) =
      NumberField.IdeleClassGroup.ofCompletion (𝓞 F) F w z := by
  change QuotientGroup.mk (_root_.IdeleGroup.equivAdeleRingUnits (_root_.IdeleGroup.infinitePlaceIdele w z)) =
    QuotientGroup.mk (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w z)
  congr 1
  apply Units.ext
  apply Prod.ext
  · funext v
    change ((_root_.IdeleGroup.infiniteComponent v (_root_.IdeleGroup.infinitePlaceIdele w z)) : v.Completion) =
      (Pi.mulSingle w (z : w.Completion)) v
    by_cases hv : v = w
    · subst v
      rw [_root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same, Pi.mulSingle_eq_same]
    · rw [_root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne w v z hv,
        Pi.mulSingle_eq_of_ne hv]
      rfl
  · rfl

theorem rayExtension (A : SArithmeticData F)
    (η : RayClassCharacter F A.modulus) :
    ∃ η_id : A.ArithmeticIdeleClasses →* Circle,
      Continuous η_id ∧ A.IdeleCharacterHasFiniteOrder η_id ∧
      A.IdeleCharacterUnramifiedOutside η_id ∧
      (∀ (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F),
        A.RepresentsExteriorIdeal I x →
          (η_id (QuotientGroup.mk x) : ℂ) = η I.val) ∧
      (∀ (w : InfinitePlace F) (z : w.Completionˣ),
        A.ideleInfiniteComponent η_id w z = 1) := by
  let hc := primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  let e := (_root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib F).symm
  let χ := (RayClassBridge.ideleClassCharacter F hc A.modulus A.modulus_ne_zero η).comp e.toMonoidHom
  have hn : ∀ x, ‖(χ x : ℂ)‖ = 1 := fun x =>
    RayClassBridge.ideleClassCharacter_norm F hc A.modulus A.modulus_ne_zero η (e x)
  let Φ : A.ArithmeticIdeleClasses →* Circle :=
    { toFun := fun x => ⟨χ x, by change (χ x : ℂ) ∈ Metric.sphere 0 1; simpa using hn x⟩
      map_one' := by apply Subtype.ext; exact congrArg (fun u : ℂˣ => (u : ℂ)) χ.map_one
      map_mul' := by intro x y; apply Subtype.ext; exact congrArg (fun u : ℂˣ => (u : ℂ)) (χ.map_mul x y) }
  have hcΦ : Continuous Φ := by
    have hχ : Continuous χ := (RayClassBridge.ideleClassCharacter_continuous F hc A.modulus A.modulus_ne_zero η).comp e.continuous
    exact (Units.continuous_val.comp hχ).subtype_mk _
  refine ⟨Φ, hcΦ, ?_, ?_, ?_, ?_⟩
  · refine ⟨Nat.card (ClassFieldTheory.RayClassGroup (RayClassBridge.narrowIdealModulus F A.modulus A.modulus_ne_zero)),
      RayClassBridge.ideleClassCharacter_exponent_pos F A.modulus A.modulus_ne_zero, ?_⟩
    intro x
    apply Subtype.ext
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (RayClassBridge.ideleClassCharacter_pow_card F hc A.modulus A.modulus_ne_zero η (e x))
  · intro v hv u hu
    apply Subtype.ext
    change (RayClassBridge.ideleClassCharacter F hc A.modulus A.modulus_ne_zero η
      (e (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) : ℂ) = 1
    have he : e (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = _root_.IdeleGroup.finitePlaceIdeleClass v u := by
      apply (_root_.IdeleGroup.ideleClassGroupEquivMathlib F).injective
      change (_root_.IdeleGroup.ideleClassGroupEquivMathlib F) ((_root_.IdeleGroup.ideleClassGroupEquivMathlib F).symm _) = _
      rw [MulEquiv.apply_symm_apply, _root_.IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass]
    rw [he]
    have hm : ¬ A.modulus ≤ v.asIdeal := fun hm => hv (A.modulus_support v hm)
    have hu' : u ∈ (v.adicCompletionIntegers F).units :=
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hu
    exact congrArg (fun u : ℂˣ => (u : ℂ))
      (RayClassBridge.ideleClassCharacter_finitePlaceIdeleClass_unit_of_not_dvd F hc A.modulus A.modulus_ne_zero η v hm u hu')
  · intro I x hx
    exact representative_evaluation A η x I hx
  · intro w z
    apply Subtype.ext
    change (RayClassBridge.ideleClassCharacter F hc A.modulus A.modulus_ne_zero η
      (e (NumberField.IdeleClassGroup.ofCompletion (𝓞 F) F w z)) : ℂ) = 1
    have he : e (NumberField.IdeleClassGroup.ofCompletion (𝓞 F) F w z) = _root_.IdeleGroup.infinitePlaceIdeleClass w z := by
      apply (_root_.IdeleGroup.ideleClassGroupEquivMathlib F).injective
      change (_root_.IdeleGroup.ideleClassGroupEquivMathlib F) ((_root_.IdeleGroup.ideleClassGroupEquivMathlib F).symm _) = _
      rw [MulEquiv.apply_symm_apply, infinite_comparison]
    rw [he]
    exact congrArg (fun u : ℂˣ => (u : ℂ))
      (RayClassBridge.ideleClassCharacter_infinitePlaceIdeleClass F hc A.modulus A.modulus_ne_zero η w z)

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData

noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

def correctionTheta (A : SArithmeticData F)
    (Λ G η_id : A.ArithmeticIdeleClasses →* Circle) :
    A.ArithmeticIdeleClasses →* Circle :=
  Λ⁻¹ * G⁻¹ * η_id

def correctionLS (A : SArithmeticData F)
    (Λ G η_id : A.ArithmeticIdeleClasses →* Circle) (y : A.G) : Circle :=
  A.ideleSInverseProduct (A.correctionTheta Λ G η_id) y

structure GaussCorrectionOutput (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) where

  H : A.V → A.V → Fˣ
  H_actual : ∀ x y : A.G,
    H (QuotientGroup.mk' A.sixthPowers x)
        (QuotientGroup.mk' A.sixthPowers y) = (A.H_S x y : Fˣ)
  B : Subgroup A.V
  B_complement : A.IsSUnitIsotropicComplement H B
  Λ : A.ArithmeticIdeleClasses →* Circle
  G : A.ArithmeticIdeleClasses →* Circle
  η_id : A.ArithmeticIdeleClasses →* Circle
  Λ_continuous : Continuous Λ
  G_continuous : Continuous G
  eta_continuous : Continuous η_id
  G_finiteOrder : A.IdeleCharacterHasFiniteOrder G
  eta_finiteOrder : A.IdeleCharacterHasFiniteOrder η_id
  Λ_unramified : A.IdeleCharacterUnramifiedOutside Λ
  G_unramified : A.IdeleCharacterUnramifiedOutside G
  eta_unramified : A.IdeleCharacterUnramifiedOutside η_id

  Λ_ideal : ∀ (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F),
    A.RepresentsExteriorIdeal I x →
      (Λ (QuotientGroup.mk x) : ℂ) =
        DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val

  eta_ideal : ∀ (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F),
    A.RepresentsExteriorIdeal I x → (η_id (QuotientGroup.mk x) : ℂ) = η I.val

  G_prime : ∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (ha : A.IsAllowed B a) (hap : (a : F) = (p : F))
    (x : NumberField.IdeleGroup (𝓞 F) F), A.RepresentsExteriorIdeal I x →
      (G (QuotientGroup.mk x) : ℂ) =
        star (σ (A.sexticResidue I (4 : A.R))) * A.idealGauss σ hS I p hp 3

  Λ_infinity : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
    (A.ideleInfiniteComponent Λ w z : ℂ) =
      (DHCubic.infinityComponent (DHCubic.E0 F A) F
        (σ.comp (algebraMap (DHCubic.E0 F A) F)) w
        (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)))⁻¹
  G_infinity : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
    A.ideleInfiniteComponent G w z = 1
  eta_infinity : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
    A.ideleInfiniteComponent η_id w z = 1

  gammaTwo_cube : ∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (ha : A.IsAllowed B a) (hap : (a : F) = (p : F)),
      A.idealGauss σ hS I p hp 2 ^ 3 =
        -DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val

  gammaOne_gammaTwo : ∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (ha : A.IsAllowed B a) (hap : (a : F) = (p : F))
    (x : NumberField.IdeleGroup (𝓞 F) F), A.RepresentsExteriorIdeal I x →
      A.idealGauss σ hS I p hp 1 * A.idealGauss σ hS I p hp 2 =
        -DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val *
          (G (QuotientGroup.mk x) : ℂ)

  theta_ideal_local : ∀ (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F)
    (a : Fˣ) (r : A.R), A.RepresentsExteriorIdeal I x →
      A.Generates I r → (a : F) = (r : F) →
      A.correctionTheta Λ G η_id (QuotientGroup.mk x) =
        A.ideleSInverseProduct (A.correctionTheta Λ G η_id) (A.diagonal a)
  theta_unit : ∀ ε : A.U,
    A.ideleSInverseProduct (A.correctionTheta Λ G η_id) (A.diagonal ε.val) = 1
  theta_continuous : Continuous (A.correctionTheta Λ G η_id)
  theta_unramified : A.IdeleCharacterUnramifiedOutside (A.correctionTheta Λ G η_id)

  finite_locallyConstant : ∀ v : {v // v ∈ A.Sf},
    ∀ z : (v.val.adicCompletion F)ˣ,
      ∃ U : Set (v.val.adicCompletion F)ˣ, IsOpen U ∧ z ∈ U ∧
        ∀ t ∈ U,
          A.ideleFiniteComponent (A.correctionTheta Λ G η_id) v.val t =
            A.ideleFiniteComponent (A.correctionTheta Λ G η_id) v.val z

  infinity_angular : ∀ w : InfinitePlace F,
    ∃ n : ℤ, (n = 1 ∨ n = -1) ∧
      ∀ z : w.Completionˣ,
        (((A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w z)⁻¹ : Circle) : ℂ) =
          DHCubic.angular (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)) ^ n ∧
        (A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w z : ℂ) =
          DHCubic.angular (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)) ^ (-n)
  infinity_no_radial : ∀ (w : InfinitePlace F) (z u : w.Completionˣ) (r : ℝ),
    0 < r → InfinitePlace.Completion.extensionEmbedding w (u : w.Completion) = (r : ℂ) →
      A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w (z * u) =
        A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w z

theorem exists_gaussCorrectionOutput
    (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R))
    (hS : A.ContainsTraceBadPlaces) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) :
    Nonempty (A.GaussCorrectionOutput σ η hS) := by
  obtain ⟨H, B, hActual, hB⟩ := GaussCorrection.actualComplement A hCl
  obtain ⟨Λ, hΛcont, hΛunram, hΛideal, hΛinf⟩ :=
    GaussCorrection.eisensteinExtension A σ
  obtain ⟨η_id, hηcont, hηorder, hηunram, hηideal, hηinf⟩ :=
    GaussCorrection.rayExtension A η
  obtain ⟨W⟩ := GaussCorrection.correctedWeilExtension A hCl hS σ H B hActual hB
  obtain ⟨hcube, hdup⟩ :=
    GaussCorrection.corrected_primeGaussLaws A hS σ H B hActual hB W
  have hθcont : Continuous (A.correctionTheta Λ W.G η_id) := by
    change Continuous (Λ⁻¹ * W.G⁻¹ * η_id)
    have hGcont := W.continuous
    fun_prop
  have hθunram : A.IdeleCharacterUnramifiedOutside
      (A.correctionTheta Λ W.G η_id) := by
    intro v hv x hx
    change (A.ideleFiniteComponent Λ v x)⁻¹ *
      (A.ideleFiniteComponent W.G v x)⁻¹ *
      (A.ideleFiniteComponent η_id v x) = 1
    rw [hΛunram v hv x hx, W.unramified v hv x hx, hηunram v hv x hx]
    simp
  obtain ⟨hθideal, hθunit, hθfinite⟩ := GaussCorrection.localArithmeticLaws A
    (A.correctionTheta Λ W.G η_id) hθcont hθunram
  have hθinf (w : InfinitePlace F) (z : w.Completionˣ) :
      A.ideleInfiniteComponent (A.correctionTheta Λ W.G η_id) w z =
        (A.ideleInfiniteComponent Λ w z)⁻¹ := by
    change (A.ideleInfiniteComponent Λ w z)⁻¹ *
      (A.ideleInfiniteComponent W.G w z)⁻¹ *
      (A.ideleInfiniteComponent η_id w z) = _
    rw [W.infinity, hηinf]
    simp
  refine ⟨{
    H := H, H_actual := hActual, B := B, B_complement := hB
    Λ := Λ, G := W.G, η_id := η_id
    Λ_continuous := hΛcont, G_continuous := W.continuous, eta_continuous := hηcont
    G_finiteOrder := W.finiteOrder, eta_finiteOrder := hηorder
    Λ_unramified := hΛunram, G_unramified := W.unramified, eta_unramified := hηunram
    Λ_ideal := hΛideal, eta_ideal := hηideal, G_prime := W.prime
    Λ_infinity := hΛinf, G_infinity := W.infinity, eta_infinity := hηinf
    gammaTwo_cube := hcube, gammaOne_gammaTwo := hdup
    theta_ideal_local := hθideal, theta_unit := hθunit
    theta_continuous := hθcont, theta_unramified := hθunram
    finite_locallyConstant := hθfinite
    infinity_angular := ?_, infinity_no_radial := ?_ }⟩
  · intro w
    obtain ⟨_, m, hm, hang⟩ := DHCubic.infinity_angular (DHCubic.E0 F A) F A
      (σ.comp (algebraMap (DHCubic.E0 F A) F)) w
    refine ⟨-m, ?_, ?_⟩
    · rcases hm with rfl | rfl <;> simp
    · intro z
      have hz : InfinitePlace.Completion.extensionEmbedding w (z : w.Completion) ≠ 0 :=
        (map_ne_zero (InfinitePlace.Completion.extensionEmbedding w)).mpr (Units.ne_zero z)
      rw [hθinf]
      simp only [inv_inv, Circle.coe_inv]
      rw [hΛinf, hang _ hz, zpow_neg, neg_neg]
      simp
  · intro w z u r hr hu
    rw [hθinf, hθinf]
    apply congrArg Inv.inv
    apply Subtype.ext
    change (A.ideleInfiniteComponent Λ w (z * u) : ℂ) =
      (A.ideleInfiniteComponent Λ w z : ℂ)
    rw [hΛinf, hΛinf]
    simp only [Units.val_mul, map_mul, hu]
    rw [mul_comm, DHCubic.infinity_no_radial _ _ _ _ _ r hr]

theorem GaussCorrectionOutput.prime_theta
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    (D : A.GaussCorrectionOutput σ η hS)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (p : A.R) (hp : A.Generates I p) (a : Fˣ)
    (ha : A.IsAllowed D.B a) (hap : (a : F) = (p : F))
    (x : NumberField.IdeleGroup (𝓞 F) F) (hx : A.RepresentsExteriorIdeal I x) :
    A.idealGauss σ hS I p hp 1 * A.idealGauss σ hS I p hp 2 *
        (A.correctionTheta D.Λ D.G D.η_id (QuotientGroup.mk x) : ℂ) =
      -η I.val := by
  rw [D.gammaOne_gammaTwo I v hIv p hp a ha hap x hx,
    ← D.Λ_ideal I x hx]
  have hcancel :
      (D.Λ (QuotientGroup.mk x) : ℂ) * (D.G (QuotientGroup.mk x) : ℂ) *
        (A.correctionTheta D.Λ D.G D.η_id (QuotientGroup.mk x) : ℂ) =
      (D.η_id (QuotientGroup.mk x) : ℂ) := by
    simp only [correctionTheta, MonoidHom.mul_apply, MonoidHom.inv_apply,
      Circle.coe_mul, Circle.coe_inv]
    have hΛ := Circle.coe_ne_zero (D.Λ (QuotientGroup.mk x))
    have hG := Circle.coe_ne_zero (D.G (QuotientGroup.mk x))
    field_simp
  calc
    _ = -((D.Λ (QuotientGroup.mk x) : ℂ) * (D.G (QuotientGroup.mk x) : ℂ) *
        (A.correctionTheta D.Λ D.G D.η_id (QuotientGroup.mk x) : ℂ)) := by ring
    _ = -η I.val := by rw [hcancel, D.eta_ideal I x hx]

namespace CorrectionAssembly

theorem correctionTheta_continuous (A : SArithmeticData F)
    (Λ G η_id : A.ArithmeticIdeleClasses →* Circle)
    (hΛ : Continuous Λ) (hG : Continuous G) (hη : Continuous η_id) :
    Continuous (A.correctionTheta Λ G η_id) := by
  change Continuous (Λ⁻¹ * G⁻¹ * η_id)
  fun_prop

theorem correctionTheta_unramified (A : SArithmeticData F)
    (Λ G η_id : A.ArithmeticIdeleClasses →* Circle)
    (hΛ : A.IdeleCharacterUnramifiedOutside Λ)
    (hG : A.IdeleCharacterUnramifiedOutside G)
    (hη : A.IdeleCharacterUnramifiedOutside η_id) :
    A.IdeleCharacterUnramifiedOutside (A.correctionTheta Λ G η_id) := by
  intro v hv x hx
  change (A.ideleFiniteComponent Λ v x)⁻¹ *
    (A.ideleFiniteComponent G v x)⁻¹ *
    (A.ideleFiniteComponent η_id v x) = 1
  rw [hΛ v hv x hx, hG v hv x hx, hη v hv x hx]
  simp

theorem correctionTheta_infinity (A : SArithmeticData F)
    (Λ G η_id : A.ArithmeticIdeleClasses →* Circle)
    (hG : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      A.ideleInfiniteComponent G w z = 1)
    (hη : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      A.ideleInfiniteComponent η_id w z = 1)
    (w : InfinitePlace F) (z : w.Completionˣ) :
    A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w z =
      (A.ideleInfiniteComponent Λ w z)⁻¹ := by
  change (A.ideleInfiniteComponent Λ w z)⁻¹ *
    (A.ideleInfiniteComponent G w z)⁻¹ *
    (A.ideleInfiniteComponent η_id w z) = _
  rw [hG, hη]
  simp

theorem correctionTheta_infinity_angular (A : SArithmeticData F)
    (σ : F →+* ℂ) (Λ G η_id : A.ArithmeticIdeleClasses →* Circle)
    (hΛ : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      (A.ideleInfiniteComponent Λ w z : ℂ) =
        (DHCubic.infinityComponent (DHCubic.E0 F A) F
          (σ.comp (algebraMap (DHCubic.E0 F A) F)) w
          (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)))⁻¹)
    (hG : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      A.ideleInfiniteComponent G w z = 1)
    (hη : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      A.ideleInfiniteComponent η_id w z = 1)
    (w : InfinitePlace F) :
    ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ ∀ z : w.Completionˣ,
      (((A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w z)⁻¹ : Circle) : ℂ) =
        DHCubic.angular (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)) ^ n ∧
      (A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w z : ℂ) =
        DHCubic.angular (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)) ^ (-n) := by
  obtain ⟨_, m, hm, hang⟩ := DHCubic.infinity_angular (DHCubic.E0 F A) F A
    (σ.comp (algebraMap (DHCubic.E0 F A) F)) w
  refine ⟨-m, ?_, ?_⟩
  · rcases hm with rfl | rfl <;> simp
  · intro z
    have hz : InfinitePlace.Completion.extensionEmbedding w (z : w.Completion) ≠ 0 :=
      (map_ne_zero (InfinitePlace.Completion.extensionEmbedding w)).mpr (Units.ne_zero z)
    rw [correctionTheta_infinity A Λ G η_id hG hη]
    simp only [inv_inv, Circle.coe_inv]
    rw [hΛ, hang _ hz, zpow_neg, neg_neg]
    simp

theorem correctionTheta_infinity_no_radial (A : SArithmeticData F)
    (σ : F →+* ℂ) (Λ G η_id : A.ArithmeticIdeleClasses →* Circle)
    (hΛ : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      (A.ideleInfiniteComponent Λ w z : ℂ) =
        (DHCubic.infinityComponent (DHCubic.E0 F A) F
          (σ.comp (algebraMap (DHCubic.E0 F A) F)) w
          (InfinitePlace.Completion.extensionEmbedding w (z : w.Completion)))⁻¹)
    (hG : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      A.ideleInfiniteComponent G w z = 1)
    (hη : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
      A.ideleInfiniteComponent η_id w z = 1)
    (w : InfinitePlace F) (z u : w.Completionˣ) (r : ℝ) (hr : 0 < r)
    (hu : InfinitePlace.Completion.extensionEmbedding w (u : w.Completion) = (r : ℂ)) :
    A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w (z * u) =
      A.ideleInfiniteComponent (A.correctionTheta Λ G η_id) w z := by
  rw [correctionTheta_infinity A Λ G η_id hG hη,
    correctionTheta_infinity A Λ G η_id hG hη]
  apply congrArg Inv.inv
  apply Subtype.ext
  change (A.ideleInfiniteComponent Λ w (z * u) : ℂ) =
    (A.ideleInfiniteComponent Λ w z : ℂ)
  rw [hΛ, hΛ]
  simp only [Units.val_mul, map_mul, hu]
  rw [mul_comm, DHCubic.infinity_no_radial _ _ _ _ _ r hr]

end CorrectionAssembly

end
end DedekindZetaZeroFree.SArithmeticData

end
