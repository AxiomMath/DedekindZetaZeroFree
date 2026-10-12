module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SexticReciprocityAndIdealCharacters
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.ResidueTracePhases

@[expose] public section

open scoped NumberField Classical nonZeroDivisors
open NumberField

namespace DedekindZetaZeroFree.SArithmeticData

noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

def sexticExponent (j : ℤ) : ℕ := (j % 6).toNat

def sexticResiduePowerChar (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (j : ℤ) : MulChar (A.R ⧸ A.extendIdeal I) ℂ :=
  MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp (A.sexticResidueFamily I)) ^
    sexticExponent j

theorem exteriorResidue_card (A : SArithmeticData F) (I : A.Exterior) :
    Nat.card (A.R ⧸ A.extendIdeal I) = Ideal.absNorm I.val := by
  rw [← Nat.card_congr (ArithGaussCRT.exteriorQuotientEquiv A I).toEquiv]
  exact (Submodule.cardQuot_apply I.val).symm

theorem exteriorResidue_finite (A : SArithmeticData F) (I : A.Exterior) :
    Finite (A.R ⧸ A.extendIdeal I) := by
  apply Nat.finite_of_card_ne_zero
  rw [A.exteriorResidue_card I]
  exact fun h => I.property.1 (Ideal.absNorm_eq_zero_iff.mp h)

def idealGauss (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (j : ℤ) : ℂ :=
  letI : Finite (A.R ⧸ A.extendIdeal I) := A.exteriorResidue_finite I
  letI : Fintype (A.R ⧸ A.extendIdeal I) := Fintype.ofFinite _
  (Real.sqrt (A.exteriorNorm I) : ℂ)⁻¹ *
    ∑ x : A.R ⧸ A.extendIdeal I,
      A.sexticResiduePowerChar σ I j x *
        (A.residueTraceCharacter hS I a ha x : ℂ)

theorem sexticResiduePowerChar_nonunit (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (j : ℤ) (x : A.R ⧸ A.extendIdeal I) (hx : ¬ IsUnit x) :
    A.sexticResiduePowerChar σ I j x = 0 := by
  exact MulChar.map_nonunit _ hx

theorem idealGauss_top (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior) (hI : I.val = ⊤)
    (a : A.R) (ha : A.Generates I a) (j : ℤ) :
    A.idealGauss σ hS I a ha j = 1 := by
  have htop : A.extendIdeal I = ⊤ := by rw [extendIdeal, hI, Ideal.map_top]
  letI : Subsingleton (A.R ⧸ A.extendIdeal I) := Ideal.Quotient.subsingleton_iff.mpr htop
  letI : Finite (A.R ⧸ A.extendIdeal I) := A.exteriorResidue_finite I
  letI : Fintype (A.R ⧸ A.extendIdeal I) := Fintype.ofFinite _
  unfold idealGauss
  rw [Fintype.sum_subsingleton _ (1 : A.R ⧸ A.extendIdeal I)]
  simp only [exteriorNorm, idealNorm, hI, Ideal.absNorm_top, Nat.cast_one, Real.sqrt_one,
    Complex.ofReal_one, inv_one, one_mul, map_one]
  rw [Subsingleton.elim (1 : A.R ⧸ A.extendIdeal I) 0]
  simp

theorem idealGauss_sixth_unit_translate (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) (u : A.U)
    (ha' : A.Generates I (a * (A.unitEquiv u : A.R) ^ 6)) (j : ℤ) :
    A.idealGauss σ hS I (a * (A.unitEquiv u : A.R) ^ 6) ha' j =
      A.idealGauss σ hS I a ha j := by
  letI : Finite (A.R ⧸ A.extendIdeal I) := A.exteriorResidue_finite I
  letI : Fintype (A.R ⧸ A.extendIdeal I) := Fintype.ofFinite _
  let v : (A.R ⧸ A.extendIdeal I)ˣ :=
    Units.map (Ideal.Quotient.mk (A.extendIdeal I)).toMonoidHom (A.unitEquiv u)
  have hv : A.sexticResiduePowerChar σ I j ((v ^ 6 : (A.R ⧸ A.extendIdeal I)ˣ) :
      A.R ⧸ A.extendIdeal I) = 1 := by
    unfold sexticResiduePowerChar
    rw [MulChar.pow_apply_coe, MulChar.ofUnitHom_coe]
    have h6 := congrArg (Units.map σ.toMonoidHom) (A.sexticResidueFamily_normalized.1 I v)
    simp only [map_pow, map_one] at h6
    have hval := congrArg Units.val h6
    simpa only [map_pow, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, Units.val_one,
      one_pow] using congrArg (fun z : ℂˣ => (z : ℂ) ^ sexticExponent j) h6
  have hphase : ∀ x : A.R ⧸ A.extendIdeal I,
      A.residueTraceCharacter hS I (a * (A.unitEquiv u : A.R) ^ 6) ha'
        (x * ↑(v ^ 6)) = A.residueTraceCharacter hS I a ha x := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.residueTraceCharacter hS I (a * (A.unitEquiv u : A.R) ^ 6) ha'
      (Ideal.Quotient.mk (A.extendIdeal I) (r * (A.unitEquiv u : A.R) ^ 6)) = _
    rw [A.residueTraceCharacter_apply, A.residueTraceCharacter_apply]
    congr 1
    have huF : ((A.unitEquiv u : A.R) : F) ≠ 0 := by
      exact_mod_cast (A.unitEquiv u).ne_zero
    push_cast
    field_simp
  unfold idealGauss
  congr 1
  symm
  apply Fintype.sum_equiv (Units.mulRight (v ^ 6))
  intro x
  change _ = A.sexticResiduePowerChar σ I j (x * ↑(v ^ 6)) * _
  rw [map_mul, hv, mul_one]
  congr 1
  exact congrArg (fun z : Circle => (z : ℂ)) (hphase x).symm

theorem idealGauss_generator_independent (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior) (a a' : A.R)
    (ha : A.Generates I a) (ha' : A.Generates I a')
    (hchange : ∃ u : A.U, a' = a * (A.unitEquiv u : A.R) ^ 6) (j : ℤ) :
    A.idealGauss σ hS I a' ha' j = A.idealGauss σ hS I a ha j := by
  obtain ⟨u, rfl⟩ := hchange
  exact A.idealGauss_sixth_unit_translate σ hS I a ha u ha' j

theorem idealGauss_allowed_generator_independent (A : SArithmeticData F)
    (σ : F →+* ℂ) (hS : A.ContainsTraceBadPlaces)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (B : Subgroup A.V) (hB : A.IsSUnitIsotropicComplement H B)
    (I : A.Exterior) (a a' : A.R)
    (ha : A.Generates I a) (ha' : A.Generates I a') (ua ua' : Fˣ)
    (hua : (ua : F) = (a : F)) (hua' : (ua' : F) = (a' : F))
    (hallowed : A.IsAllowed B ua) (hallowed' : A.IsAllowed B ua') (j : ℤ) :
    A.idealGauss σ hS I a' ha' j = A.idealGauss σ hS I a ha j := by
  have hu : A.IsAllowedGenerator B (A.extendIdeal I : FractionalIdeal A.R⁰ F) ua := by
    refine ⟨?_, hallowed⟩
    rw [← ha.2, FractionalIdeal.coeIdeal_span_singleton, hua]
    rfl
  have hu' : A.IsAllowedGenerator B (A.extendIdeal I : FractionalIdeal A.R⁰ F) ua' := by
    refine ⟨?_, hallowed'⟩
    rw [← ha'.2, FractionalIdeal.coeIdeal_span_singleton, hua']
    rfl
  have h := A.allowed_generator_unique_mod_sixth hCl H B hB _ ua' ua hu' hu
  obtain ⟨ε, hε, heq⟩ := h
  let u : A.U := ⟨ε, hε⟩
  have hratio : ua' / ua = u.val ^ 6 := heq.symm
  apply A.idealGauss_generator_independent σ hS I a a' ha ha' _ j
  refine ⟨u, ?_⟩
  apply Subtype.ext
  have hval := congrArg Units.val hratio
  have hunit : ((A.unitEquiv u : A.R) : F) = (u.val : F) := by
    simp [unitEquiv, Set.unitEquivUnitsInteger]
  change (a' : F) = (a : F) * ((A.unitEquiv u : A.R) : F) ^ 6
  rw [hunit]
  simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, hua, hua'] at hval
  exact (div_eq_iff (by simpa [hua] using ua.ne_zero)).mp hval |>.trans (mul_comm _ _)

private theorem gaussCRT_char_base (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : A.R) :
    MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp (A.sexticResidueFamily I))
      (Ideal.Quotient.mk (A.extendIdeal I) x) = σ (A.sexticResidue I x) := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x)
  · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx]
    change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [MulChar.map_nonunit _ hx, map_zero]
private theorem gaussCRT_char_mul_modulus (A : SArithmeticData F) (σ : F →+* ℂ)
    (I J K : A.Exterior) (hK : K.val = I.val * J.val) (x : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal K) x) ↔
      IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x) ∧
      IsUnit (Ideal.Quotient.mk (A.extendIdeal J) x)) (j : ℤ) :
    A.sexticResiduePowerChar σ K j (Ideal.Quotient.mk (A.extendIdeal K) x) =
      A.sexticResiduePowerChar σ I j (Ideal.Quotient.mk (A.extendIdeal I) x) *
      A.sexticResiduePowerChar σ J j (Ideal.Quotient.mk (A.extendIdeal J) x) := by
  by_cases hn : sexticExponent j = 0
  · simp only [sexticResiduePowerChar, hn, pow_zero]
    by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal K) x)
    · have h := hu.mp hx
      rw [MulChar.one_apply hx, MulChar.one_apply h.1, MulChar.one_apply h.2, mul_one]
    · rw [MulChar.map_nonunit _ hx]
      have h := not_and_or.mp (mt hu.mpr hx)
      rcases h with h | h
      · rw [MulChar.map_nonunit _ h, zero_mul]
      · rw [MulChar.map_nonunit _ h, mul_zero]
  · simp only [sexticResiduePowerChar, MulChar.pow_apply' _ hn, gaussCRT_char_base]
    rw [show A.sexticResidue K x = A.sexticResidue I x * A.sexticResidue J x from
      A.sexticResidueFamily_normalized.2.2 I J K hK x, map_mul, mul_pow]
private theorem gaussCRT_char_unit (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : A.R) (hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x))
    (j : ℤ) : A.sexticResiduePowerChar σ I j (Ideal.Quotient.mk (A.extendIdeal I) x) =
    σ (A.sexticResidue I x) ^ sexticExponent j := by
  unfold sexticResiduePowerChar
  rw [← hx.unit_spec, MulChar.pow_apply_coe]
  rw [hx.unit_spec, gaussCRT_char_base]

set_option maxHeartbeats 800000 in

theorem idealGauss_squarefree_crt (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (I J K : A.Exterior)
    (hI : Squarefree I.val) (hJ : Squarefree J.val)
    (hcoprime : I.val ⊔ J.val = ⊤) (hK : K.val = I.val * J.val)
    (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (hab : A.Generates K (a * b)) (j : ℤ) :
    A.idealGauss σ hS K (a * b) hab j =
      σ (A.sexticResidue I b) ^ sexticExponent j *
      σ (A.sexticResidue J a) ^ sexticExponent j *
      A.idealGauss σ hS I a ha j * A.idealGauss σ hS J b hb j := by
  have hcop : IsCoprime (A.extendIdeal I) (A.extendIdeal J) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    change Ideal.map (algebraMap (𝓞 F) A.R) I.val ⊔
      Ideal.map (algebraMap (𝓞 F) A.R) J.val = ⊤
    rw [← Ideal.map_sup, hcoprime, Ideal.map_top]
  have hmul : A.extendIdeal K = A.extendIdeal I * A.extendIdeal J := by
    simp only [extendIdeal, hK, Ideal.map_mul]
  let E := (Ideal.quotEquivOfEq hmul).trans
    (Ideal.quotientMulEquivQuotientProd (A.extendIdeal I) (A.extendIdeal J) hcop)
  have hE (x : A.R) : E (Ideal.Quotient.mk (A.extendIdeal K) x) =
      (Ideal.Quotient.mk (A.extendIdeal I) x, Ideal.Quotient.mk (A.extendIdeal J) x) := by
    rfl
  have haz : Ideal.Quotient.mk (A.extendIdeal I) a = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← ha.2]
    exact Ideal.subset_span (by simp)
  have hbz : Ideal.Quotient.mk (A.extendIdeal J) b = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hb.2]
    exact Ideal.subset_span (by simp)
  have hu (x : A.R) : IsUnit (Ideal.Quotient.mk (A.extendIdeal K) x) ↔
      IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x) ∧
      IsUnit (Ideal.Quotient.mk (A.extendIdeal J) x) := by
    rw [← @Prod.isUnit_iff _ _ _ _ (Ideal.Quotient.mk (A.extendIdeal I) x, Ideal.Quotient.mk (A.extendIdeal J) x)]
    rw [← hE]
    constructor
    · exact fun h => h.map E.toMonoidHom
    · intro h
      simpa using h.map E.symm.toMonoidHom
  have habcop : IsCoprime a b := by
    apply (Ideal.sup_eq_top_iff_isCoprime a b).mp
    rw [ha.2, hb.2]
    exact hcop.sup_eq
  obtain ⟨r, s, hrs⟩ := habcop
  have hub : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) b) := by
    apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (A.extendIdeal I) s)
    have h := congrArg (Ideal.Quotient.mk (A.extendIdeal I)) hrs
    simpa [map_add, map_mul, haz, mul_comm] using h
  have hua : IsUnit (Ideal.Quotient.mk (A.extendIdeal J) a) := by
    apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (A.extendIdeal J) r)
    have h := congrArg (Ideal.Quotient.mk (A.extendIdeal J)) hrs
    simpa [map_add, map_mul, hbz, mul_comm] using h
  let e : ((A.R ⧸ A.extendIdeal I) × (A.R ⧸ A.extendIdeal J)) ≃
      (A.R ⧸ A.extendIdeal K) :=
    ((Units.mulLeft hub.unit).prodCongr (Units.mulLeft hua.unit)).trans E.symm.toEquiv
  have he (x y : A.R) :
      e (Ideal.Quotient.mk (A.extendIdeal I) x, Ideal.Quotient.mk (A.extendIdeal J) y) =
      Ideal.Quotient.mk (A.extendIdeal K) (b * x + a * y) := by
    apply E.injective
    change E (E.symm _) = E _
    rw [E.apply_symm_apply, hE]
    simp only [Equiv.prodCongr_apply, Units.mulLeft_apply, hub.unit_spec, hua.unit_spec,
      map_add, map_mul, haz, hbz, zero_mul, mul_zero, add_zero, zero_add]
    rfl
  have hphase (x y : A.R) :
      A.residueTraceCharacter hS K (a * b) hab
        (Ideal.Quotient.mk (A.extendIdeal K) (b * x + a * y)) =
      A.residueTraceCharacter hS I a ha (Ideal.Quotient.mk (A.extendIdeal I) x) *
      A.residueTraceCharacter hS J b hb (Ideal.Quotient.mk (A.extendIdeal J) y) := by
    rw [A.residueTraceCharacter_apply, A.residueTraceCharacter_apply,
      A.residueTraceCharacter_apply, ← AddChar.map_add_eq_mul]
    congr 1
    have haF : (a : F) ≠ 0 := by exact_mod_cast ha.1
    have hbF : (b : F) ≠ 0 := by exact_mod_cast hb.1
    push_cast
    field_simp
    <;> ring
  have hchar (x y : A.R) :
      A.sexticResiduePowerChar σ K j
        (Ideal.Quotient.mk (A.extendIdeal K) (b * x + a * y)) =
      (σ (A.sexticResidue I b) ^ sexticExponent j *
        A.sexticResiduePowerChar σ I j (Ideal.Quotient.mk (A.extendIdeal I) x)) *
      (σ (A.sexticResidue J a) ^ sexticExponent j *
        A.sexticResiduePowerChar σ J j (Ideal.Quotient.mk (A.extendIdeal J) y)) := by
    rw [gaussCRT_char_mul_modulus A σ I J K hK _ (hu _) j]
    simp only [map_add, map_mul, haz, hbz, zero_mul, mul_zero, add_zero, zero_add]
    rw [gaussCRT_char_unit A σ I b hub j, gaussCRT_char_unit A σ J a hua j]
  letI : Finite (A.R ⧸ A.extendIdeal I) := A.exteriorResidue_finite I
  letI : Finite (A.R ⧸ A.extendIdeal J) := A.exteriorResidue_finite J
  letI : Finite (A.R ⧸ A.extendIdeal K) := A.exteriorResidue_finite K
  letI : Fintype (A.R ⧸ A.extendIdeal I) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ A.extendIdeal J) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ A.extendIdeal K) := Fintype.ofFinite _
  have hsum : (∑ z : A.R ⧸ A.extendIdeal K,
      A.sexticResiduePowerChar σ K j z * (A.residueTraceCharacter hS K (a * b) hab z : ℂ)) =
      (σ (A.sexticResidue I b) ^ sexticExponent j *
        σ (A.sexticResidue J a) ^ sexticExponent j) *
      (∑ x : A.R ⧸ A.extendIdeal I,
        A.sexticResiduePowerChar σ I j x * (A.residueTraceCharacter hS I a ha x : ℂ)) *
      (∑ y : A.R ⧸ A.extendIdeal J,
        A.sexticResiduePowerChar σ J j y * (A.residueTraceCharacter hS J b hb y : ℂ)) := by
    rw [← Fintype.sum_equiv e (fun z =>
      (σ (A.sexticResidue I b) ^ sexticExponent j *
        σ (A.sexticResidue J a) ^ sexticExponent j) *
      (A.sexticResiduePowerChar σ I j z.1 * (A.residueTraceCharacter hS I a ha z.1 : ℂ)) *
      (A.sexticResiduePowerChar σ J j z.2 * (A.residueTraceCharacter hS J b hb z.2 : ℂ))) _ ?_]
    · simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    · intro z
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective z.1
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective z.2
      rcases z with ⟨z₁, z₂⟩
      dsimp at hx hy
      subst z₁ z₂
      rw [he, hchar, hphase, Circle.coe_mul]
      ring
  have hnorm : (Real.sqrt (A.exteriorNorm K) : ℂ) =
      (Real.sqrt (A.exteriorNorm I) : ℂ) * (Real.sqrt (A.exteriorNorm J) : ℂ) := by
    simp only [exteriorNorm, idealNorm, hK, map_mul, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  unfold idealGauss
  rw [hsum, hnorm, mul_inv]
  ring

end
end DedekindZetaZeroFree.SArithmeticData
