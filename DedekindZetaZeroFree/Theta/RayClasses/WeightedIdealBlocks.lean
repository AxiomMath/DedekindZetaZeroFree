module

public import DedekindZetaZeroFree.Theta.RayClasses.NormalizedCharacterAggregates
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.ResidueUnitCharacters
public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.CoprimeGeneratorLifts
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealModulusProjectionSurjective
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.OrdinaryRayClassGroupEquivClassGroup

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

theorem existsUnique_integralElementIdeal
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) :
    ∃! a : Ideal (𝓞 F), (a : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val *
        (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val *
      (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
    simpa using mul_le_mul (FractionalIdeal.spanSingleton_le_iff_mem.mpr x.property)
      (le_refl ((I : FractionalIdeal (𝓞 F)⁰ F)⁻¹))
  obtain ⟨a, ha⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact FractionalIdeal.coeIdeal_injective (hb.trans ha.symm)

def integralElementIdeal (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) : Ideal (𝓞 F) :=
  Classical.choose (existsUnique_integralElementIdeal I x)

theorem integralElementIdeal_coe (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) :
    (integralElementIdeal I x : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ x.val *
        (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
  exact (Classical.choose_spec (existsUnique_integralElementIdeal I x)).1

theorem integralElementIdeal_integral_coe (a : Ideal (𝓞 F)) (ha : a ≠ ⊥)
    (x : 𝓞 F) (hx : x ∈ a) :
    ∀ hmem : (algebraMap (𝓞 F) F) x ∈
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F),
    (integralElementIdeal (rayIdealFractionalIdeal F a ha)
      ⟨(algebraMap (𝓞 F) F) x, hmem⟩ : FractionalIdeal (𝓞 F)⁰ F) =
      (Ideal.span {x} : FractionalIdeal (𝓞 F)⁰ F) *
        (a : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
  intro hmem
  simpa only [rayIdealFractionalIdeal_coe, FractionalIdeal.coeIdeal_span_singleton]
    using integralElementIdeal_coe (rayIdealFractionalIdeal F a ha)
      ⟨(algebraMap (𝓞 F) F) x, hmem⟩

def residueUnitImage (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) : Subgroup (𝓞 F ⧸ m)ˣ :=
  (Units.map (Ideal.Quotient.mk m).toMonoidHom).range

def residueUnitImageCard (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) : ℕ :=
  Nat.card (residueUnitImage F m)

theorem residueUnitImageCard_pos {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) :
    0 < residueUnitImageCard F m := by
  letI : Finite (𝓞 F ⧸ m) := m.finiteQuotientOfFreeOfNeBot hm
  exact Nat.card_pos

def weightedIdealBlock (hF : NumberField.IsTotallyComplex F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (u : ℝ) : ℂ :=
  if 0 < u then
    ((residueUnitImageCard F m * RayCoset.rayUnitTorsionCard F m : ℕ) : ℂ)⁻¹ *
      ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
        ∑' x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)},
          η (integralElementIdeal I x) *
            RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
              ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
                (-1 / (Module.finrank ℚ F : ℝ)) •
                  DedekindZetaZeroFree.AbelianQuotient.Theta.traceEmbedding F x.val))
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F
  else 0

def weightedIdealBlockNeg (hF : NumberField.IsTotallyComplex F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (u : ℝ) : ℂ :=
  if 0 < u then
    ((residueUnitImageCard F m * RayCoset.rayUnitTorsionCard F m : ℕ) : ℂ)⁻¹ *
      ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
        ∑' x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)},
          η (integralElementIdeal I x) *
            RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h))
              ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
                (-1 / (Module.finrank ℚ F : ℝ)) •
                  DedekindZetaZeroFree.AbelianQuotient.Theta.traceEmbedding F x.val))
        ∂DedekindZetaZeroFree.AbelianQuotient.Theta.normalizedLogHaar F
  else 0

def rayToOrdinary (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    RayIdealClass F m hm →* ClassGroup (𝓞 F) :=
  ClassFieldTheory.ordinaryRayClassGroupEquivClassGroup.toMonoidHom.comp
    (ClassFieldTheory.rayClassIdealModulusProjection F
      (ClassFieldTheory.ordinaryRayClassModulus_le F (narrowIdealModulus F m hm)))

theorem rayToOrdinary_rayIdealClass {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hcop : a ⊔ m = ⊤)
    (c : RayIdealClass F m hm) (hc : rayIdealClass F m hm a = some c) :
    rayToOrdinary F m hm c = ClassGroup.mk F (rayIdealFractionalIdeal F a ha) := by
  rw [rayIdealClass_eq_some F m hm a ha hcop] at hc
  rw [← Option.some.inj hc]
  apply (ClassGroup.equiv F).injective
  simp only [rayToOrdinary, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ClassFieldTheory.ordinaryRayClassGroupEquivClassGroup,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply, ClassGroup.equiv_mk,
    ClassFieldTheory.rayClassIdealModulusProjection]
  rw [QuotientGroup.map_mk']
  rw [QuotientGroup.congr_mk]
  simp only [FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl]
  rfl

end DedekindZetaZeroFree.Hecke.Theta

end
