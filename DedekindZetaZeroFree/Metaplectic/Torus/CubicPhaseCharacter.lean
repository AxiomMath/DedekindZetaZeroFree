module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations

@[expose] public section

open scoped NumberField Classical NNReal

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TorusFiniteCenterQuotient

noncomputable section

private theorem local_class_cube
    (F : Type) [Field F] [NumberField F]
    (v : KPHilbert.Place F) (x : KPGlobalCubicIdelePairing.LocalD F v) :
    x ^ 3 = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (CubicCharacters.cubes (KPHilbert.Completion F v)ˣ) x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩

private theorem adjustment_cube
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (v : KPHilbert.Place F) (x : (P.localData v).L) :
    T.chi v x ^ 3 = 1 := by
  have hx : x ^ 3 = 1 := by
    apply Subtype.ext
    exact local_class_cube F v x.val
  rw [← map_pow, hx, map_one]

private theorem local_normal
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : KPHilbert.Place F)
    (b : KPGlobalProductPolarizationCharacter.LocalE F ζ hζ v) :
    ∃ ε : rootsOfUnity 3 F, ∃ y : (KPHilbert.Completion F v)ˣ,
      b.val = KPPGLLocalCover.centralInjection F ζ hζ v ε * KPPGLLocalCover.A F ζ hζ v y := by
  obtain ⟨y, hy⟩ := b.property
  have ha : KPPGLLocalCover.projection F ζ hζ v (KPPGLLocalCover.A F ζ hζ v y) =
      KPPGLLocalCover.baseQuotient F v (KPGlobalProductPolarizationCharacter.diagonalHom F v y) := by
    rfl
  have hk : b.val / KPPGLLocalCover.A F ζ hζ v y ∈
      (KPPGLLocalCover.projection F ζ hζ v).ker := by
    rw [MonoidHom.mem_ker, map_div, ha]
    change KPPGLLocalCover.projection F ζ hζ v b.val /
      KPPGLLocalCover.baseQuotient F v (KPGlobalProductPolarizationCharacter.diagonalHom F v y) = 1
    change KPPGLLocalCover.baseQuotient F v (KPGlobalProductPolarizationCharacter.diagonalHom F v y) =
      KPPGLLocalCover.projection F ζ hζ v b.val at hy
    rw [hy]
    exact div_self' _
  rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection] at hk
  obtain ⟨ε, hε⟩ := hk
  refine ⟨ε, y, ?_⟩
  rw [hε, div_mul_cancel]

private theorem local_A_cube
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) :
    KPPGLLocalCover.A F ζ hζ v y ^ 3 = KPPGLLocalCover.A F ζ hζ v (y ^ 3) := by
  have hB := KPHilbert.B3_laws F ζ hζ v
  have hyy : KPHilbert.B3 F ζ hζ v y y = 1 := (hB.2.2.2.2.2 y).1
  have h2y : KPHilbert.B3 F ζ hζ v (y * y) y = 1 := by rw [hB.1, hyy, one_mul]
  change (KPPGLLocalCover.coverQuotient F ζ hζ v (KPStandardLocalRootLifts.A F ζ hζ v y)) ^ 3 = _
  rw [← map_pow]
  have hr : KPStandardLocalRootLifts.A F ζ hζ v y ^ 3 = KPStandardLocalRootLifts.A F ζ hζ v (y ^ 3) := by
    rw [pow_succ, pow_two, KPStandardLocalRootLifts.A_mul, hyy, one_pow, map_one, one_mul,
      KPStandardLocalRootLifts.A_mul, h2y, one_pow, map_one, one_mul]
    rw [pow_succ, pow_two]
  rw [hr]
  rfl

private theorem native_cube_positive
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (v : KPHilbert.Place F)
    (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ v (P.localData v).L) :
    ∃ u : (ℝ≥0)ˣ, (P.localData v).lambda b ^ 3 = KPGlobalCenterRationalCharacter.positiveComplex u := by
  obtain ⟨ε, y, hy⟩ := local_normal F ζ hζ v b.val
  have he : (KPPGLLocalCover.centralInjection F ζ hζ v ε) ^ 3 = 1 := by
    rw [← map_pow]
    have hε : ε ^ 3 = 1 := by apply Subtype.ext; exact ε.property
    rw [hε, map_one]
  have hc : Commute (KPPGLLocalCover.centralInjection F ζ hζ v ε) (KPPGLLocalCover.A F ζ hζ v y) := by
    have hr : Commute (KPLocalCover.centralInjection F ζ hζ v ε) (KPStandardLocalRootLifts.A F ζ hζ v y) :=
      (Subgroup.mem_center_iff.mp
        (KPLocalCover.centralInjection_range_le_center F ζ hζ v (show
          KPLocalCover.centralInjection F ζ hζ v ε ∈ (KPLocalCover.centralInjection F ζ hζ v).range from ⟨ε, rfl⟩))
        (KPStandardLocalRootLifts.A F ζ hζ v y)).symm
    exact hr.map (KPPGLLocalCover.coverQuotient F ζ hζ v)
  have hp : b.val.val ^ 3 = KPPGLLocalCover.A F ζ hζ v (y ^ 3) := by
    rw [hy, hc.mul_pow, he, one_mul, local_A_cube]
  let z : KPGlobalProductPolarizationCharacter.localCenter F ζ hζ v :=
    ⟨b.val ^ 3, by
      change KPGlobalProductPolarizationCharacter.localProjection F ζ hζ v (b.val ^ 3) = 1
      rw [map_pow]; exact local_class_cube F v _⟩
  have hz := (P.localData v).extends_center (b ^ 3) z rfl
  have hf := KPGlobalProductPolarizationCharacter.localOmega_raw_formula F ζ hζ v z
    (KPStandardLocalRootLifts.A F ζ hζ v (y ^ 3)) hp.symm
  have hv := ProductPolarizationCharacterDescent.raw_value_on_cube_normal_word F ζ hζ v
    1 (y ^ 3) (by
      change QuotientGroup.mk' _ (y ^ 3) = 1
      exact (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩)
    (KPStandardLocalRootLifts.A F ζ hζ v (y ^ 3)) (by rw [map_one, one_mul]; rfl)
  rw [map_pow, hf, hv, map_one, one_mul] at hz
  exact ⟨_, hz⟩

def normUnit : ℂˣ →* (ℝ≥0)ˣ := Units.map nnnormHom.toMonoidHom

private theorem normUnit_positive (u : (ℝ≥0)ˣ) :
    normUnit (KPGlobalCenterRationalCharacter.positiveComplex u) = u := by
  apply Units.ext
  change ‖((KPGlobalCenterRationalCharacter.positiveComplex u : ℂˣ) : ℂ)‖₊ = (u : ℝ≥0)
  apply NNReal.coe_injective
  change ‖(((u : ℝ≥0) : ℝ) : ℂ)‖ = ((u : ℝ≥0) : ℝ)
  exact Complex.norm_of_nonneg (NNReal.coe_nonneg _)

private theorem normalized_cube (a : ℂˣ)
    (ha : ∃ u : (ℝ≥0)ˣ, a ^ 3 = KPGlobalCenterRationalCharacter.positiveComplex u) :
    (a / KPGlobalCenterRationalCharacter.positiveComplex (normUnit a)) ^ 3 = 1 := by
  obtain ⟨u, hu⟩ := ha
  have hn := congrArg normUnit hu
  rw [map_pow, normUnit_positive] at hn
  rw [div_pow, ← map_pow, hu, hn, div_self']

private theorem adjusted_normalized_cube
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (v : KPHilbert.Place F)
    (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ v (P.localData v).L) :
    (KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ P T v b /
      KPGlobalCenterRationalCharacter.positiveComplex (normUnit
        (KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ P T v b))) ^ 3 = 1 := by
  apply normalized_cube
  obtain ⟨u, hu⟩ := native_cube_positive F ζ hζ P v b
  refine ⟨u, ?_⟩
  rw [KPGlobalProductPolarizationCharacter.adjustedLocalValue, mul_pow, adjustment_cube, mul_one]
  exact hu

def normalizedHom : ℂˣ →* ℂˣ where
  toFun a := a / KPGlobalCenterRationalCharacter.positiveComplex (normUnit a)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul]; exact mul_div_mul_comm _ _ _ _

private theorem product_normalized_cube
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (b : KPGlobalProductPolarizationCharacter.B F ζ hζ P) :
    normalizedHom (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b) ^ 3 = 1 := by
  obtain ⟨x, hx⟩ := KPGlobalProductPolarizationCharacter.B_has_raw_lift F ζ hζ P b
  rw [KPGlobalProductPolarizationCharacter.lambdaB_raw_formula F ζ hζ P T b x hx,
    normalizedHom.map_finprod (KPGlobalProductPolarizationCharacter.rawProduct_finiteSupport F ζ hζ P T x)]
  let pow3 : ℂˣ →* ℂˣ := powMonoidHom 3
  change pow3 (∏ᶠ v, normalizedHom
    (KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ P T v
      (KPGlobalProductPolarizationCharacter.rawCoordinate F ζ hζ P x v))) = 1
  have hm := pow3.map_finprod ((KPGlobalProductPolarizationCharacter.rawProduct_finiteSupport F ζ hζ P T x).comp (normalizedHom.map_one))
  simp only [Function.comp_apply] at hm
  rw [hm]
  have he : (fun v => pow3 (normalizedHom
      (KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ P T v
        (KPGlobalProductPolarizationCharacter.rawCoordinate F ζ hζ P x v)))) = fun _ => 1 := by
    funext v
    exact adjusted_normalized_cube F ζ hζ P T v _
  rw [he, finprod_one]

theorem phaseCharacter_cube
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (k : KPGlobalTorusFiniteStages.phaseGroup F ζ hζ C L) :
    KPGlobalTorusFiniteStages.phaseCharacter F ζ hζ C L k ^ 3 = 1 := by
  let b : KPGlobalTorusFiniteStages.B F ζ hζ C :=
    ⟨k.val, KPGlobalTorusFiniteStages.phase_inside_product F ζ hζ C L k.property⟩
  have hn : normUnit (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b) =
      KPGlobalCenterRationalCharacter.nu F ζ hζ b.val := by
    apply Units.ext
    apply NNReal.coe_injective
    exact KPGlobalProductPolarizationCharacter.lambdaB_norm F ζ hζ C C.adjustment b
  have hc := product_normalized_cube F ζ hζ C C.adjustment b
  change (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b /
    KPGlobalCenterRationalCharacter.positiveComplex
      (normUnit (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b))) ^ 3 = 1 at hc
  rw [hn] at hc
  exact hc

end

end DedekindZetaZeroFree.TorusFiniteCenterQuotient
