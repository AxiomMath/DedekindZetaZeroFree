module

public import DedekindZetaZeroFree.Adeles.Characters.FiniteOrderClassCharacters
public import DedekindZetaZeroFree.Metaplectic.Weil.IsotropicComplementSignCharacter
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SexticHilbertPairing

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.CubicWeilCorrection
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]

def fourS : Fˣ := Units.mk0 4 (by norm_num)

 def twoS : Fˣ := Units.mk0 2 (by norm_num)

private lemma fourS_eq_square : fourS (F := F) = twoS ^ 2 := by
  apply Units.ext
  norm_num [fourS, twoS]

def rawFourS (A : SArithmeticData F) : A.V →* rootsOfUnity 6 F :=
  A.H_S6 (QuotientGroup.mk' A.sixthPowers (A.diagonal fourS))

def cubicUnits (A : SArithmeticData F) (σ : F →+* ℂ) : A.V →* ℂˣ :=
  ((Units.map σ.toMonoidHom).comp
    ((rootsOfUnity 6 F).subtype.comp (rawFourS A)))⁻¹

lemma cubicUnits_cube (A : SArithmeticData F) (σ : F →+* ℂ) (x : A.V) :
    cubicUnits A σ x ^ 3 = 1 := by
  have hf : rawFourS A x ^ 3 = 1 := by
    have hx : (A.H_S6 (QuotientGroup.mk' A.sixthPowers (A.diagonal twoS)) x : Fˣ) ^ 6 = 1 :=
      (mem_rootsOfUnity 6 _).mp (A.H_S6 _ x).property
    apply Subtype.ext
    change (rawFourS A x : Fˣ) ^ 3 = 1
    unfold rawFourS
    rw [fourS_eq_square, map_pow, map_pow, map_pow, MonoidHom.pow_apply]
    simpa only [SubmonoidClass.coe_pow, ← pow_mul] using hx
  change ((Units.map σ.toMonoidHom) (rawFourS A x : Fˣ))⁻¹ ^ 3 = 1
  rw [inv_pow, ← map_pow]
  have he := congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) hf
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at he
  rw [he, map_one, inv_one]

 lemma cubicUnits_norm (A : SArithmeticData F) (σ : F →+* ℂ) (x : A.V) :
    ‖(cubicUnits A σ x : ℂ)‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
  rw [← Complex.norm_pow]
  have h := congrArg (fun u : ℂˣ => (u : ℂ)) (cubicUnits_cube A σ x)
  simpa using congrArg (fun z : ℂ => ‖z‖) h

def cubicClass (A : SArithmeticData F) (σ : F →+* ℂ) : A.V →* Circle where
  toFun x := ⟨cubicUnits A σ x, mem_sphere_zero_iff_norm.mpr (cubicUnits_norm A σ x)⟩
  map_one' := by apply Circle.ext; exact congrArg Units.val (map_one (cubicUnits A σ))
  map_mul' x y := by apply Circle.ext; exact congrArg Units.val (map_mul (cubicUnits A σ) x y)

def cubicS (A : SArithmeticData F) (σ : F →+* ℂ) : A.G →* Circle :=
  (cubicClass A σ).comp (QuotientGroup.mk' A.sixthPowers)

lemma cubicS_coe (A : SArithmeticData F) (σ : F →+* ℂ) (y : A.G) :
    (cubicS A σ y : ℂ) =
      (σ (((A.H_S (A.diagonal fourS) y : Fˣ) : F)))⁻¹ := by
  change (cubicUnits A σ (QuotientGroup.mk' A.sixthPowers y) : ℂ) = _
  simp only [cubicUnits, MonoidHom.inv_apply, MonoidHom.comp_apply,
    Units.val_inv_eq_inv_val, Units.coe_map]
  change (σ (((rawFourS A (QuotientGroup.mk' A.sixthPowers y) : Fˣ) : F)))⁻¹ = _
  rw [rawFourS, A.H_S6_on_representatives]

theorem phaseClassExtension (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (σ : F →+* ℂ)
    (H : A.V → A.V → Fˣ) (B : Subgroup A.V)
    (hB : A.IsSUnitIsotropicComplement H B)
    (wInf : (v : InfinitePlace F) → v.Completionˣ → ℂ)
    (wFin : (v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ → ℂ)
    (h : A.WeilSStructuralLaws H σ wInf wFin) :
    ∃ (φ : B →* ℂˣ) (D : A.ClassCharacterExtension B φ),
      (∀ b : B, φ b ^ 6 = 1) ∧
      (∀ (y : A.G) (hy : QuotientGroup.mk' A.sixthPowers y ∈ B),
        (A.ideleSInverseProduct D.ideleCharacter y : ℂ) =
          (cubicS A σ y : ℂ) * A.weilSCorrection wInf wFin y) := by
  obtain ⟨c, hc, hrecipe⟩ := A.exists_weilBCharacter_of_structural_laws H σ B hB wInf wFin h
  let φ : B →* ℂˣ := ((cubicUnits A σ).comp B.subtype) * c.toHomUnits
  have hφ : (Set.range φ).Finite := by
    apply (Set.finite_range ((rootsOfUnity 6 ℂ).subtype)).subset
    rintro z ⟨b, rfl⟩
    exact ⟨⟨φ b, (mem_rootsOfUnity 6 _).mpr
      (ClassCharacterGluing.character_sixth A B φ b)⟩, rfl⟩
  obtain ⟨D⟩ := A.exists_class_character_extension hCl B hB.1 hB.2.2 φ hφ
  refine ⟨φ, D, ClassCharacterGluing.character_sixth A B φ, ?_⟩
  intro y hy
  have hs := D.local_split_value y (1, ⟨QuotientGroup.mk' A.sixthPowers y, hy⟩) (by simp)
  have hs' := congrArg (fun z : ℂˣ => (z : ℂ)) hs
  change (A.ideleSInverseProduct D.ideleCharacter y : ℂ) =
    (cubicUnits A σ (QuotientGroup.mk' A.sixthPowers y) : ℂ) *
      c ⟨QuotientGroup.mk' A.sixthPowers y, hy⟩ at hs'
  rw [hrecipe y hy] at hs'
  exact hs'
end
end DedekindZetaZeroFree.SArithmeticData.CubicWeilCorrection
