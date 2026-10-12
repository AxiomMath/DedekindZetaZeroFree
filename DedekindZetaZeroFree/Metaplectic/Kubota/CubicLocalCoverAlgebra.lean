module

public import DedekindZetaZeroFree.Metaplectic.Kubota.DeterminantTwistedCocycle

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree
namespace KPLocalCover

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev LocalGL2 (v : KPHilbert.Place F) := KubotaRankTwo.GL2 (KPHilbert.Completion F v)

def sigmaTwo (v : KPHilbert.Place F) (g h : LocalGL2 F v) : rootsOfUnity 3 F :=
  KubotaElementaryLastArgument.tau (KPHilbert.Completion F v) (rootsOfUnity 3 F)
      (KPHilbert.B3 F ζ hζ v) g h *
    KPHilbert.B3 F ζ hζ v
      (KubotaRankTwo.det (KPHilbert.Completion F v) g)
      (KubotaRankTwo.det (KPHilbert.Completion F v) h) ^ 2

theorem sigmaTwo_cocycle (v : KPHilbert.Place F) (g h k : LocalGL2 F v) :
    sigmaTwo F ζ hζ v g h * sigmaTwo F ζ hζ v (g * h) k =
      sigmaTwo F ζ hζ v h k * sigmaTwo F ζ hζ v g (h * k) := by
  obtain ⟨hL, hR, _, hSt, _, hAlt⟩ := KPHilbert.B3_laws F ζ hζ v
  exact KubotaCocycleAlgebra.sigmaTwo_cocycle _ _ _ hL hR
    (fun a => (hAlt a).1)
    (fun a b => by
      apply Subtype.ext
      exact (KPHilbert.B3 F ζ hζ v a b).property)
    (fun a ha => hSt a _ (by simp)) g h k

@[simp] theorem sigmaTwo_one_left (v : KPHilbert.Place F) (g : LocalGL2 F v) :
    sigmaTwo F ζ hζ v 1 g = 1 := by
  exact KubotaCocycleAlgebra.sigmaTwo_one_left _ _ _
    (KPHilbert.B3_laws F ζ hζ v).1 (KPHilbert.B3_laws F ζ hζ v).2.1 g

@[simp] theorem sigmaTwo_one_right (v : KPHilbert.Place F) (g : LocalGL2 F v) :
    sigmaTwo F ζ hζ v g 1 = 1 := by
  exact KubotaCocycleAlgebra.sigmaTwo_one_right _ _ _
    (KPHilbert.B3_laws F ζ hζ v).1 (KPHilbert.B3_laws F ζ hζ v).2.1 g

structure CubicGL2Raw (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (v : KPHilbert.Place F) where
  g : LocalGL2 F v
  epsilon : rootsOfUnity 3 F

variable (v : KPHilbert.Place F)

def rawMul (x y : CubicGL2Raw F ζ hζ v) : CubicGL2Raw F ζ hζ v :=
  ⟨x.g * y.g, x.epsilon * y.epsilon * sigmaTwo F ζ hζ v x.g y.g⟩

def rawOne : CubicGL2Raw F ζ hζ v := ⟨1, 1⟩

def rawInv (x : CubicGL2Raw F ζ hζ v) : CubicGL2Raw F ζ hζ v :=
  ⟨x.g⁻¹, x.epsilon⁻¹ * (sigmaTwo F ζ hζ v x.g x.g⁻¹)⁻¹⟩

theorem rawMul_assoc (x y z : CubicGL2Raw F ζ hζ v) :
    rawMul F ζ hζ v (rawMul F ζ hζ v x y) z =
      rawMul F ζ hζ v x (rawMul F ζ hζ v y z) := by
  cases x with | mk gx ex =>
    cases y with | mk gy ey =>
      cases z with | mk gz ez =>
        unfold rawMul
        congr 1
        · exact mul_assoc _ _ _
        · simp only
          calc
            (ex * ey * sigmaTwo F ζ hζ v gx gy) * ez * sigmaTwo F ζ hζ v (gx * gy) gz =
                (ex * ey * ez) * (sigmaTwo F ζ hζ v gx gy * sigmaTwo F ζ hζ v (gx * gy) gz) := by ac_rfl
            _ = (ex * ey * ez) * (sigmaTwo F ζ hζ v gy gz * sigmaTwo F ζ hζ v gx (gy * gz)) := by rw [sigmaTwo_cocycle]
            _ = ex * (ey * ez * sigmaTwo F ζ hζ v gy gz) * sigmaTwo F ζ hζ v gx (gy * gz) := by ac_rfl

theorem rawOne_mul (x : CubicGL2Raw F ζ hζ v) :
    rawMul F ζ hζ v (rawOne F ζ hζ v) x = x := by
  cases x
  simp [rawMul, rawOne]

theorem rawMul_one (x : CubicGL2Raw F ζ hζ v) :
    rawMul F ζ hζ v x (rawOne F ζ hζ v) = x := by
  cases x
  simp [rawMul, rawOne]

theorem rawInv_mul_cancel (x : CubicGL2Raw F ζ hζ v) :
    rawMul F ζ hζ v (rawInv F ζ hζ v x) x = rawOne F ζ hζ v := by
  have hi : sigmaTwo F ζ hζ v x.g⁻¹ x.g = sigmaTwo F ζ hζ v x.g x.g⁻¹ := by
    have hc := sigmaTwo_cocycle F ζ hζ v x.g x.g⁻¹ x.g
    simpa using hc.symm
  cases x
  simp [rawMul, rawInv, rawOne, hi, mul_assoc, mul_left_comm, mul_comm]

instance rawGroup : Group (CubicGL2Raw F ζ hζ v) where
  mul := rawMul F ζ hζ v
  one := rawOne F ζ hζ v
  inv := rawInv F ζ hζ v
  mul_assoc := rawMul_assoc F ζ hζ v
  one_mul := rawOne_mul F ζ hζ v
  mul_one := rawMul_one F ζ hζ v
  inv_mul_cancel := rawInv_mul_cancel F ζ hζ v

@[simp] theorem mul_g (x y : CubicGL2Raw F ζ hζ v) :
    (x * y).g = x.g * y.g := rfl

@[simp] theorem mul_epsilon (x y : CubicGL2Raw F ζ hζ v) :
    (x * y).epsilon = x.epsilon * y.epsilon * sigmaTwo F ζ hζ v x.g y.g := rfl

@[simp] theorem one_g : (1 : CubicGL2Raw F ζ hζ v).g = 1 := rfl
@[simp] theorem one_epsilon : (1 : CubicGL2Raw F ζ hζ v).epsilon = 1 := rfl

@[simp] theorem inv_g (x : CubicGL2Raw F ζ hζ v) : (x⁻¹).g = x.g⁻¹ := rfl
@[simp] theorem inv_epsilon (x : CubicGL2Raw F ζ hζ v) :
    (x⁻¹).epsilon = x.epsilon⁻¹ * (sigmaTwo F ζ hζ v x.g x.g⁻¹)⁻¹ := rfl

def centralInjection : rootsOfUnity 3 F →* CubicGL2Raw F ζ hζ v where
  toFun epsilon := ⟨1, epsilon⟩
  map_one' := rfl
  map_mul' := by
    intro x y
    change CubicGL2Raw.mk 1 (x * y) = CubicGL2Raw.mk (1 * 1)
      (x * y * sigmaTwo F ζ hζ v 1 1)
    simp

def projection : CubicGL2Raw F ζ hζ v →* LocalGL2 F v where
  toFun x := x.g
  map_one' := rfl
  map_mul' := by intros; rfl

def sectionMap (g : LocalGL2 F v) : CubicGL2Raw F ζ hζ v := ⟨g, 1⟩

@[simp] theorem centralInjection_g (epsilon : rootsOfUnity 3 F) :
    (centralInjection F ζ hζ v epsilon).g = 1 := rfl
@[simp] theorem centralInjection_epsilon (epsilon : rootsOfUnity 3 F) :
    (centralInjection F ζ hζ v epsilon).epsilon = epsilon := rfl
@[simp] theorem projection_apply (x : CubicGL2Raw F ζ hζ v) :
    projection F ζ hζ v x = x.g := rfl
@[simp] theorem sectionMap_g (g : LocalGL2 F v) :
    (sectionMap F ζ hζ v g).g = g := rfl
@[simp] theorem sectionMap_epsilon (g : LocalGL2 F v) :
    (sectionMap F ζ hζ v g).epsilon = 1 := rfl

theorem centralInjection_injective : Function.Injective (centralInjection F ζ hζ v) := by
  intro a b h
  exact congrArg CubicGL2Raw.epsilon h

theorem projection_surjective : Function.Surjective (projection F ζ hζ v) := by
  intro g
  exact ⟨sectionMap F ζ hζ v g, rfl⟩

theorem centralInjection_range_le_center :
    (centralInjection F ζ hζ v).range ≤ Subgroup.center (CubicGL2Raw F ζ hζ v) := by
  rintro x ⟨z, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  change CubicGL2Raw.mk (y.g * 1) (y.epsilon * z * sigmaTwo F ζ hζ v y.g 1) =
    CubicGL2Raw.mk (1 * y.g) (z * y.epsilon * sigmaTwo F ζ hζ v 1 y.g)
  simp [mul_comm]

theorem sectionMap_mul (g h : LocalGL2 F v) :
    sectionMap F ζ hζ v g * sectionMap F ζ hζ v h =
      centralInjection F ζ hζ v (sigmaTwo F ζ hζ v g h) *
        sectionMap F ζ hζ v (g * h) := by
  change CubicGL2Raw.mk (g * h) (1 * 1 * sigmaTwo F ζ hζ v g h) =
    CubicGL2Raw.mk (1 * (g * h))
      (sigmaTwo F ζ hζ v g h * 1 * sigmaTwo F ζ hζ v 1 (g * h))
  simp

def complexSixthGenerator : ℂˣ :=
  Units.mk0 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6)) (Complex.exp_ne_zero _)

theorem exists_sixthExponent (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (z : rootsOfUnity 6 F) :
    ∃ i : ℕ, i < 6 ∧ (ζ ^ 2) ^ i = ((z : Fˣ) : F) := by
  apply (KPHilbert.primitive_six F ζ hζ).eq_pow_of_pow_eq_one
  exact congrArg (fun a : Fˣ => (a : F)) z.property

def sixthExponent (z : rootsOfUnity 6 F) : ℕ :=
  Classical.choose (exists_sixthExponent F ζ hζ z)

def coefficientValue (z : rootsOfUnity 6 F) : ℂˣ :=
  complexSixthGenerator ^ sixthExponent F ζ hζ z

private theorem sixthExponent_lt (z : rootsOfUnity 6 F) :
    sixthExponent F ζ hζ z < 6 :=
  (Classical.choose_spec (exists_sixthExponent F ζ hζ z)).1

private theorem sixthExponent_spec (z : rootsOfUnity 6 F) :
    (ζ ^ 2) ^ sixthExponent F ζ hζ z = ((z : Fˣ) : F) :=
  (Classical.choose_spec (exists_sixthExponent F ζ hζ z)).2

private theorem complexSixthGenerator_primitive :
    IsPrimitiveRoot (complexSixthGenerator : ℂˣ) 6 :=
  IsPrimitiveRoot.coe_units_iff.mp (by
    exact Complex.isPrimitiveRoot_exp 6 (by decide))

theorem coefficientValue_one : coefficientValue F ζ hζ 1 = 1 := by
  have he : sixthExponent F ζ hζ 1 = 0 :=
    (KPHilbert.primitive_six F ζ hζ).pow_inj
      (sixthExponent_lt F ζ hζ 1) (by decide)
      (by simpa using sixthExponent_spec F ζ hζ 1)
  simp [coefficientValue, he]

theorem coefficientValue_mul (x y : rootsOfUnity 6 F) :
    coefficientValue F ζ hζ (x * y) =
      coefficientValue F ζ hζ x * coefficientValue F ζ hζ y := by
  let i := sixthExponent F ζ hζ x
  let j := sixthExponent F ζ hζ y
  have hxy : sixthExponent F ζ hζ (x * y) = (i + j) % 6 := by
    apply (KPHilbert.primitive_six F ζ hζ).pow_inj
      (sixthExponent_lt F ζ hζ (x * y)) (Nat.mod_lt _ (by decide))
    rw [← pow_eq_pow_mod (i + j) (KPHilbert.primitive_six F ζ hζ).pow_eq_one]
    rw [pow_add, sixthExponent_spec F ζ hζ (x * y)]
    simp only [i, j, sixthExponent_spec F ζ hζ]
    rfl
  unfold coefficientValue
  rw [hxy, ← pow_eq_pow_mod (i + j) complexSixthGenerator_primitive.pow_eq_one, pow_add]

def coefficientEmbedding : rootsOfUnity 6 F →* ℂˣ where
  toFun := coefficientValue F ζ hζ
  map_one' := coefficientValue_one F ζ hζ
  map_mul' := coefficientValue_mul F ζ hζ

theorem coefficientEmbedding_injective : Function.Injective (coefficientEmbedding F ζ hζ) := by
  intro x y h
  have hi : sixthExponent F ζ hζ x = sixthExponent F ζ hζ y :=
    complexSixthGenerator_primitive.pow_inj
      (sixthExponent_lt F ζ hζ x) (sixthExponent_lt F ζ hζ y) h
  apply rootsOfUnity.coe_injective
  change ((x : Fˣ) : F) = ((y : Fˣ) : F)
  rw [← sixthExponent_spec F ζ hζ x, ← sixthExponent_spec F ζ hζ y, hi]

def threeToSix : rootsOfUnity 3 F →* rootsOfUnity 6 F where
  toFun z := ⟨(z : Fˣ), by
    change (z : Fˣ) ^ 6 = 1
    calc
      (z : Fˣ) ^ 6 = ((z : Fˣ) ^ 3) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [z.property, one_pow]⟩
  map_one' := rfl
  map_mul' := by intros; rfl

def genuineCharacter : rootsOfUnity 3 F →* ℂˣ :=
  (Units.map (starRingEnd ℂ).toMonoidHom).comp
    ((coefficientEmbedding F ζ hζ).comp (threeToSix F))

@[simp] theorem genuineCharacter_apply (z : rootsOfUnity 3 F) :
    (genuineCharacter F ζ hζ z : ℂ) =
      star (coefficientEmbedding F ζ hζ (threeToSix F z) : ℂ) := rfl

end
end KPLocalCover
end DedekindZetaZeroFree
