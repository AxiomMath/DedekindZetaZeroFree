module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.JetMultiplierContinuity
public import DedekindZetaZeroFree.Metaplectic.Torus.ClosednessAndNormChartFormula

@[expose] public section

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev E := KPGlobalTorusFiniteStages.E F ζ hζ
abbrev A := KPGlobalTorusFiniteStages.A F
abbrev R := KPGlobalTorusFiniteStages.R F ζ hζ
abbrev ModelData := KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ
abbrev M (C : ModelData F ζ hζ) := KPGlobalTorusFiniteStages.M F ζ hζ C
abbrev B (C : ModelData F ζ hζ) := KPGlobalTorusFiniteStages.B F ζ hζ C
abbrev J (C : ModelData F ζ hζ) := KPGlobalTorusFiniteStages.J F ζ hζ C
abbrev pD := KPGlobalTorusFiniteStages.pD F ζ hζ

abbrev PeriodizationIndex (C : ModelData F ζ hζ) :=
  A F ⧸ (J F ζ hζ C).comap (A F).subtype

abbrev CompactIndex (C : ModelData F ζ hζ) :=
  M F ζ hζ C ⧸ (J F ζ hζ C).comap (M F ζ hζ C).subtype

def intersectionInB (C : ModelData F ζ hζ) : Subgroup (B F ζ hζ C) :=
  (R F ζ hζ).comap (B F ζ hζ C).subtype

instance intersectionInB_normal (C : ModelData F ζ hζ) :
    (intersectionInB F ζ hζ C).Normal := by
  constructor
  intro n hn g
  have hc := (KPGlobalProductPolarizationCharacter.B_maximal_abelian F ζ hζ C).1
    g.val g.property n.val n.property
  have he : g * n * g⁻¹ = n := by
    apply Subtype.ext
    change g.val * n.val * g.val⁻¹ = n.val
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  rwa [he]

def averagingClass (C : ModelData F ζ hζ) (b : B F ζ hζ C) :
    CompactIndex F ζ hζ C :=
  QuotientGroup.mk (⟨pD F ζ hζ b.val, b.property⟩ : M F ζ hζ C)

private lemma diag_inverse (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F)
    (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit⁻¹.val = A⁻¹ 0 0 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F) => B 0 0) A.inv_mul
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h10, mul_zero, add_zero, if_pos rfl] at h
  have hu := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit_spec
  change A⁻¹ 0 0 * A 0 0 = 1 at h
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit
  have hu' : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 0 0 := hu
  calc
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * 1 := (mul_one _).symm
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * (A⁻¹ 0 0 * A 0 0) := by rw [h]
    _ = A⁻¹ 0 0 := by rw [← hu']; simp [← mul_assoc, mul_comm]
private lemma diag_inverse11 (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F)
    (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit⁻¹.val = A⁻¹ 1 1 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F) => B 1 1) A.inv_mul
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h01, mul_zero, zero_add, if_pos rfl] at h
  have hu := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit_spec
  change A⁻¹ 1 1 * A 1 1 = 1 at h
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit
  have hu' : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 1 1 := hu
  calc
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * 1 := (mul_one _).symm
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * (A⁻¹ 1 1 * A 1 1) := by rw [h]
    _ = A⁻¹ 1 1 := by rw [← hu']; simp [← mul_assoc, mul_comm]
private lemma preimage_diag (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A ∈
      KPGlobalTorusFunctionData.ordinaryTorus F) : A 1 0 = 0 ∧ A 0 1 = 0 := by
  obtain ⟨B, hB, h10, h01⟩ := hA
  rw [QuotientGroup.mk'_eq_mk'] at hB
  obtain ⟨z, hz, he⟩ := hB
  obtain ⟨u, rfl⟩ := hz
  rw [← he]
  simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h01, h10]
private lemma ratio_continuous : Continuous (KPGlobalTorusFunctionData.torusRatio F) := by
  let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  let S := (KPGlobalTorusFunctionData.ordinaryTorus F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F))
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
  let u (A : q ⁻¹' S) := (KPGlobalTorusFunctionData.diagonal_entries_units F A.val
    (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2).1.unit
  let w (A : q ⁻¹' S) := (KPGlobalTorusFunctionData.diagonal_entries_units F A.val
    (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2).2.unit
  have hu : Continuous u := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : q ⁻¹' S => (u A).val)
      have he : (fun A : q ⁻¹' S => (u A).val) = fun A => A.val 0 0 := by
        funext A; exact IsUnit.unit_spec _
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A 0 0) from (continuous_apply 0).comp ((continuous_apply 0).comp (Units.continuous_val : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A.val)))).comp continuous_subtype_val
    · have he : (fun A : q ⁻¹' S => (u A)⁻¹.val) = fun A => A.val⁻¹ 0 0 := by
        funext A; exact diag_inverse F A.val (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
      change Continuous (fun A : q ⁻¹' S => (u A)⁻¹.val)
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A⁻¹ 0 0) from (continuous_apply 0).comp ((continuous_apply 0).comp (Units.continuous_coe_inv : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => (A⁻¹ : KPGlobalTorusFunctionData.AdelicMatrixGroup F).val)))).comp continuous_subtype_val
  have hw : Continuous w := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : q ⁻¹' S => (w A).val)
      have he : (fun A : q ⁻¹' S => (w A).val) = fun A => A.val 1 1 := by
        funext A; exact IsUnit.unit_spec _
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A 1 1) from (continuous_apply 1).comp ((continuous_apply 1).comp (Units.continuous_val : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A.val)))).comp continuous_subtype_val
    · have he : (fun A : q ⁻¹' S => (w A)⁻¹.val) = fun A => A.val⁻¹ 1 1 := by
        funext A; exact diag_inverse11 F A.val (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
      change Continuous (fun A : q ⁻¹' S => (w A)⁻¹.val)
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A⁻¹ 1 1) from (continuous_apply 1).comp ((continuous_apply 1).comp (Units.continuous_coe_inv : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => (A⁻¹ : KPGlobalTorusFunctionData.AdelicMatrixGroup F).val)))).comp continuous_subtype_val
  have he : (KPGlobalTorusFunctionData.torusRatio F) ∘ S.restrictPreimage q =
      fun A => u A * (w A)⁻¹ := by
    funext A
    apply Units.ext
    exact KPGlobalTorusFunctionData.ratio_formula F _ A.val rfl
      (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
  rw [he]
  exact hu.mul hw.inv

private lemma pD_continuous :
    Continuous (KPGlobalProductPolarizationCharacter.pD F ζ hζ) := by
  apply QuotientGroup.continuous_mk.comp
  apply (ratio_continuous F).comp
  exact ((KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
    continuous_subtype_val).subtype_mk (fun t => t.property)

instance compactIndex_compact (C : ModelData F ζ hζ) :
    CompactSpace (CompactIndex F ζ hζ C) := by
  letI : CompactSpace (M F ζ hζ C) := isCompact_iff_compactSpace.mp
    (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ C).1
  infer_instance

instance compactIndex_t2 (C : ModelData F ζ hζ) :
    T2Space (CompactIndex F ζ hζ C) := by
  letI := KPGlobalCubicIdelePairing.hausdorff F
  letI := KPGlobalProductPolarizationCharacter.J_finite F ζ hζ C
  have hj : Set.Finite (J F ζ hζ C : Set (KPGlobalCubicIdelePairing.D F)) := by
    simpa using (Set.finite_range (fun j : J F ζ hζ C => j.val))
  haveI : IsClosed (((J F ζ hζ C).comap (M F ζ hζ C).subtype) : Set (M F ζ hζ C)) :=
    hj.isClosed.preimage continuous_subtype_val
  infer_instance

instance compactIndex_topologicalGroup (C : ModelData F ζ hζ) :
    IsTopologicalGroup (CompactIndex F ζ hζ C) := by
  infer_instance

instance compactIndex_measurable (C : ModelData F ζ hζ) :
    MeasurableSpace (CompactIndex F ζ hζ C) := borel _

instance compactIndex_borel (C : ModelData F ζ hζ) :
    BorelSpace (CompactIndex F ζ hζ C) := ⟨rfl⟩

def probabilityHaar (C : ModelData F ζ hζ) : Measure (CompactIndex F ζ hζ C) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

theorem probabilityHaar_mass (C : ModelData F ζ hζ) :
    probabilityHaar F ζ hζ C Set.univ = 1 := by
  exact Measure.haarMeasure_self

instance probabilityHaar_isHaar (C : ModelData F ζ hζ) :
    (probabilityHaar F ζ hζ C).IsHaarMeasure := by
  unfold probabilityHaar
  infer_instance

instance probabilityHaar_isProbability (C : ModelData F ζ hζ) :
    IsProbabilityMeasure (probabilityHaar F ζ hζ C) := by
  exact ⟨probabilityHaar_mass F ζ hζ C⟩

def rationalModel : KPGlobalTorusFunctionData.Polarization F ζ hζ where
  H := R F ζ hζ
  closed := KPGlobalCenterRationalCharacter.R_closed F ζ hζ
  abelian := by
    intro x y
    apply Subtype.ext
    exact ((KPGlobalCenterRationalCharacter.R_maximal_abelian F ζ hζ).1
      x.val x.property y.val y.property).eq
  contains_center := le_sup_right
  character := KPGlobalCenterRationalCharacter.lambdaR F ζ hζ

def productModel (C : ModelData F ζ hζ) : KPGlobalTorusFunctionData.Polarization F ζ hζ where
  H := B F ζ hζ C
  closed := KPGlobalProductPolarizationCharacter.B_closed F ζ hζ C
  abelian := by
    intro x y
    apply Subtype.ext
    exact ((KPGlobalProductPolarizationCharacter.B_maximal_abelian F ζ hζ C).1
      x.val x.property y.val y.property).eq
  contains_center := KPGlobalProductPolarizationCharacter.center_le_B F ζ hζ C
  character := KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment

abbrev RationalSmooth := KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ (rationalModel F ζ hζ)
abbrev ProductSmooth (C : ModelData F ζ hζ) :=
  KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ (productModel F ζ hζ C)
abbrev RationalUnitary := KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ
  (KPGlobalTorusFiniteStages.rationalModel F ζ hζ)
abbrev ProductUnitary (C : ModelData F ζ hζ) :=
  KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ (KPGlobalTorusFiniteStages.productModel F ζ hζ C)

local instance modelTopology (P : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    TopologicalSpace (KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

def rationalClass (r : R F ζ hζ) : A F :=
  ⟨pD F ζ hζ r.val, by
    have hr : r.val ∈ KPGlobalCenterRationalCharacter.R F ζ hζ := r.property
    rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ] at hr
    exact hr⟩

def periodizationClass (C : ModelData F ζ hζ) (r : R F ζ hζ) :
    PeriodizationIndex F ζ hζ C := QuotientGroup.mk (rationalClass F ζ hζ r)

structure PeriodizationRepresentatives (C : ModelData F ζ hζ) where
  lift : PeriodizationIndex F ζ hζ C → R F ζ hζ
  projects : ∀ a, periodizationClass F ζ hζ C (lift a) = a

 theorem rationalLift_mem (y : Fˣ) :
    KPGlobalTorusFunctionData.s F ζ hζ y ∈ R F ζ hζ := by
  exact Subgroup.mem_sup_left ⟨y, rfl⟩

def rationalLift (y : Fˣ) : R F ζ hζ :=
  ⟨KPGlobalTorusFunctionData.s F ζ hζ y, rationalLift_mem F ζ hζ y⟩

private theorem rationalLift_projection (y : Fˣ) : KPGlobalTorusFunctionData.p F ζ hζ (rationalLift F ζ hζ y).val = IdeleGroup.unitEmbedding (𝓞 F) F y := by
  apply Units.val_injective
  let t : KPGlobalTorusFunctionData.ordinaryTorus F :=
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (rationalLift F ζ hζ y).val.val,
      (rationalLift F ζ hζ y).val.property⟩
  let a := KPAdelicCoverRestrictedProduct.rationalBase F (KPGlobalTorusFunctionData.rationalDiagonal F y)
  have ha : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) a = t.val := by
    change QuotientGroup.mk' _ a = QuotientGroup.lift _ _ _ (QuotientGroup.mk _)
    simp only [QuotientGroup.lift_mk, MonoidHom.comp_apply]
    exact congrArg (QuotientGroup.mk' _) (KPAdelicCoverRestrictedProduct.projection_rationalSection F ζ hζ _).symm
  have h10 : a 1 0 = 0 := by simp [a, KPAdelicCoverRestrictedProduct.rationalBase, KPGlobalTorusFunctionData.rationalDiagonal, KubotaRankTwo.d]
  have h01 : a 0 1 = 0 := by simp [a, KPAdelicCoverRestrictedProduct.rationalBase, KPGlobalTorusFunctionData.rationalDiagonal, KubotaRankTwo.d]
  change (KPGlobalTorusFunctionData.torusRatio F t : KPGlobalTorusFunctionData.Adeles F) = _
  have h11 : (KPGlobalTorusFunctionData.diagonal_entries_units F a h10 h01).2.unit = 1 := by
    apply Units.val_injective
    rw [IsUnit.unit_spec]
    simp [a, KPAdelicCoverRestrictedProduct.rationalBase, KPGlobalTorusFunctionData.rationalDiagonal, KubotaRankTwo.d]
  rw [KPGlobalTorusFunctionData.ratio_formula F t a ha h10 h01, h11, inv_one, Units.val_one, mul_one, IsUnit.unit_spec]
  rfl

 theorem rational_representatives_exist (C : ModelData F ζ hζ) :
    ∃ s : PeriodizationRepresentatives F ζ hζ C,
      ∀ a, ∃ y : Fˣ, s.lift a = rationalLift F ζ hζ y := by
  have hs : ∀ a : PeriodizationIndex F ζ hζ C, ∃ y : Fˣ,
      periodizationClass F ζ hζ C (rationalLift F ζ hζ y) = a := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, hy⟩ := x.property
    refine ⟨y, ?_⟩
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    change pD F ζ hζ (rationalLift F ζ hζ y).val = x.val
    change QuotientGroup.mk' _ (KPGlobalTorusFunctionData.p F ζ hζ _) = _
    rw [rationalLift_projection]
    exact hy
  refine ⟨⟨fun a => rationalLift F ζ hζ (Classical.choose (hs a)),
    fun a => Classical.choose_spec (hs a)⟩, ?_⟩
  intro a
  exact ⟨Classical.choose (hs a), rfl⟩

 theorem rational_representative_norm (y : Fˣ) :
      KPGlobalCenterRationalCharacter.nu F ζ hζ (rationalLift F ζ hζ y).val = 1 := by
  have hc := KPGlobalCenterRationalCharacter.lambdaR_rational F ζ hζ y
    (rationalLift F ζ hζ y) rfl
  have hn := KPGlobalCenterRationalCharacter.lambdaR_norm F ζ hζ (rationalLift F ζ hζ y)
  rw [hc, Units.val_one, norm_one] at hn
  exact Units.val_injective (NNReal.coe_injective (by simpa using hn.symm))

 theorem rational_representative_character (y : Fˣ) :
    KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (rationalLift F ζ hζ y) = 1 ∧
      KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (rationalLift F ζ hζ y) = 1 := by
  have hc := KPGlobalCenterRationalCharacter.lambdaR_rational F ζ hζ y
    (rationalLift F ζ hζ y) rfl
  refine ⟨hc, ?_⟩
  change KPGlobalTorusFiniteStages.rationalUnitValue F ζ hζ (rationalLift F ζ hζ y) = 1
  simp [KPGlobalTorusFiniteStages.rationalUnitValue, hc, rational_representative_norm]

def periodizationTerm (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductSmooth F ζ hζ C)
    (g : E F ζ hζ) (a : PeriodizationIndex F ζ hζ C) : ℂ :=
  ((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (s.lift a))⁻¹ : ℂˣ) *
    f.val.val ((s.lift a).val * g)

 theorem periodizationTerm_independent (C : ModelData F ζ hζ)
    (s t : PeriodizationRepresentatives F ζ hζ C) (f : ProductSmooth F ζ hζ C)
    (g : E F ζ hζ) (a : PeriodizationIndex F ζ hζ C) :
    periodizationTerm F ζ hζ C s f g a = periodizationTerm F ζ hζ C t f g a := by
  let u := s.lift a
  let v := t.lift a
  have he : periodizationClass F ζ hζ C u = periodizationClass F ζ hζ C v :=
    (s.projects a).trans (t.projects a).symm
  have hdj : pD F ζ hζ (u / v).val ∈ J F ζ hζ C := by
    have hx := QuotientGroup.eq_iff_div_mem.mp he
    change pD F ζ hζ u.val / pD F ζ hζ v.val ∈ J F ζ hζ C at hx
    simpa only [Subgroup.coe_div, map_div] using hx
  let b : B F ζ hζ C := ⟨(u / v).val, hdj.2⟩
  have hu : u = (u / v) * v := by simp
  have hchar := C.agrees b (u / v) rfl
  have hcov := f.val.property b (v.val * g)
  change f.val.val (b.val * (v.val * g)) =
    (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b : ℂ) * f.val.val (v.val * g) at hcov
  change (((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ u)⁻¹ : ℂˣ) : ℂ) * f.val.val (u.val * g) =
    (((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ v)⁻¹ : ℂˣ) : ℂ) * f.val.val (v.val * g)
  rw [hu, map_mul]
  simp only [Subgroup.coe_mul, mul_assoc]
  rw [hcov, hchar]
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have hn : (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (u / v) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

 theorem finitePart_normal : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
  unfold KPGlobalTorusFunctionData.finitePart
  apply Subgroup.Normal.map (Subgroup.normal_iInf_normal fun w => inferInstance)
  change Function.Surjective (fun x => KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x))
  exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

 noncomputable def finiteConj (a : E F ζ hζ) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  refine ⟨(MulAut.conjNormal a.val).toEquiv, ?_, ?_⟩
  · apply Continuous.subtype_mk
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => a.val * x.val * a.val⁻¹)
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  · apply Continuous.subtype_mk
    have he : (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a.val).symm = MulAut.conjNormal a.val⁻¹ := by
      change (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a.val)⁻¹ = _
      rw [map_inv]
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => ((MulAut.conjNormal a.val).symm x).val)
    rw [he]
    simp only [MulAut.conjNormal_apply, inv_inv]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

 noncomputable def conjLevel (a : E F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.FiniteLevel F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  exact ⟨J.toOpenSubgroup.comap (MulAut.conjNormal a.val⁻¹).toMonoidHom (by
      change Continuous (finiteConj F ζ hζ a⁻¹)
      exact (finiteConj F ζ hζ a⁻¹).continuous),
    (finiteConj F ζ hζ a⁻¹).isCompact_preimage.mpr J.isCompact⟩

private theorem translate_level (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (a : E F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P)
    (hf : f ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P J) :
    KPGlobalTorusFunctionData.rightTranslation P.H P.character.toMonoidHom a f ∈
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P (conjLevel F ζ hζ a J) := by
  constructor
  · intro g
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => f.val ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * g) * a)) _
    simpa only [mul_assoc] using hf.1 (g * a)
  · intro j
    apply Subtype.ext
    funext g
    have hj : a.val⁻¹ * j.val.val * a.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
      obtain ⟨k, hk, he⟩ := j.property
      have hk' : a.val⁻¹ * k.val * a.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
        letI := finitePart_normal F ζ hζ
        apply Subgroup.mem_map.mpr
        exact ⟨MulAut.conjNormal a.val⁻¹ k, hk, by simp only [Subgroup.subtype_apply, MulAut.conjNormal_apply, inv_inv]⟩
      change k.val = j.val.val at he
      rw [← he]
      exact hk'
    let t : E F ζ hζ := a⁻¹ * j.val * a
    have ht : t ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype := hj
    have hh := congrArg (fun z : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P => z.val (g * a))
      (hf.2 ⟨t, ht⟩)
    change f.val ((g * j.val) * a) = f.val (g * a)
    change f.val ((g * a) * t) = f.val (g * a) at hh
    have he : (g * a) * t = (g * j.val) * a := by dsimp [t]; group
    rwa [he] at hh

 theorem translate_union (P : KPGlobalTorusFunctionData.Polarization F ζ hζ) (a : E F ζ hζ)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ P)
    (hf : f ∈ KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P) :
    KPGlobalTorusFunctionData.rightTranslation P.H P.character.toMonoidHom a f ∈
      KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P := by
  have hle : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P ≤
      (KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P).comap
        (KPGlobalTorusFunctionData.rightTranslation P.H P.character.toMonoidHom a) := by
    apply iSup_le
    intro J x hx
    exact Submodule.mem_iSup_of_mem (conjLevel F ζ hζ a J) (translate_level F ζ hζ P a J x hx)
  exact hle hf

def rightAction (P : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    Representation ℂ (E F ζ hζ) (KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P) where
  toFun a := (KPGlobalTorusFunctionData.rightTranslation P.H P.character.toMonoidHom a).restrict
    (translate_union F ζ hζ P a)
  map_one' := by
    ext f g
    change f.val.val (g * 1) = f.val.val g
    rw [mul_one]
  map_mul' a b := by
    ext f g
    change f.val.val (g * (a * b)) = f.val.val ((g * a) * b)
    rw [mul_assoc]

 theorem rightAction_formula (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (a g : E F ζ hζ) (f : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P) :
    (rightAction F ζ hζ P a f).val.val g = f.val.val (g * a) := by rfl

namespace ScalarUntwistHelpers
variable {T : Type*} [Group T] (H : Subgroup T) (χ ψ : H →* ℂˣ) (η : T →* ℂˣ)
variable (hψ : ∀ h : H, ψ h = χ h * η h.val)
 def scalarMap : KPGlobalTorusFunctionData.ScalarFunctions H χ →ₗ[ℂ] KPGlobalTorusFunctionData.ScalarFunctions H ψ where
  toFun f := ⟨fun g => (η g : ℂ) * f.val g, by
    intro h g
    dsimp only
    rw [map_mul, Units.val_mul, f.property h g, hψ, Units.val_mul]
    ring⟩
  map_add' f g := by ext t; simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c f := by ext t; simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

 def scalarEquiv : KPGlobalTorusFunctionData.ScalarFunctions H χ ≃ₗ[ℂ] KPGlobalTorusFunctionData.ScalarFunctions H ψ := by
  let ηi : T →* ℂˣ := (invMonoidHom : ℂˣ →* ℂˣ).comp η
  have hi : ∀ h : H, χ h = ψ h * ηi h.val := by
    intro h; rw [hψ]; dsimp [ηi]; simp [mul_assoc]
  refine LinearEquiv.ofLinear (scalarMap H χ ψ η hψ) (scalarMap H ψ χ ηi hi) ?_ ?_
  · ext f t
    change (η t : ℂ) * ((ηi t : ℂ) * f.val t) = f.val t
    simp [ηi, Units.val_inv_eq_inv_val, Units.ne_zero]
  · ext f t
    change (ηi t : ℂ) * ((η t : ℂ) * f.val t) = f.val t
    simp [ηi, Units.val_inv_eq_inv_val, Units.ne_zero]
end ScalarUntwistHelpers

 def normInverse : E F ζ hζ →* ℂˣ :=
  (invMonoidHom : ℂˣ →* ℂˣ).comp
    ((KPGlobalCenterRationalCharacter.positiveComplex).comp
      (KPGlobalCenterRationalCharacter.nu F ζ hζ))

def scalarUntwistRational :
    KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (rationalModel F ζ hζ) ≃ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) :=
  ScalarUntwistHelpers.scalarEquiv (R F ζ hζ) (rationalModel F ζ hζ).character.toMonoidHom
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ).character.toMonoidHom
    (normInverse F ζ hζ) (by intro h; rfl)

def scalarUntwistProduct (C : ModelData F ζ hζ) :
    KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (productModel F ζ hζ C) ≃ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (KPGlobalTorusFiniteStages.productModel F ζ hζ C) :=
  ScalarUntwistHelpers.scalarEquiv (B F ζ hζ C) (productModel F ζ hζ C).character.toMonoidHom
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C).character.toMonoidHom
    (normInverse F ζ hζ) (by intro h; rfl)
 theorem scalarUntwistRational_formula
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (rationalModel F ζ hζ)) (g : E F ζ hζ) :
    (scalarUntwistRational F ζ hζ f).val g =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ)⁻¹ * f.val g := by
  change ((normInverse F ζ hζ g : ℂˣ) : ℂ) * f.val g = _
  simp [normInverse, KPGlobalCenterRationalCharacter.positiveComplex]
 theorem scalarUntwistProduct_formula (C : ModelData F ζ hζ)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (productModel F ζ hζ C)) (g : E F ζ hζ) :
    (scalarUntwistProduct F ζ hζ C f).val g =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ)⁻¹ * f.val g := by
  change ((normInverse F ζ hζ g : ℂˣ) : ℂ) * f.val g = _
  simp [normInverse, KPGlobalCenterRationalCharacter.positiveComplex]
private theorem nu_compact_subgroup (H : Subgroup (E F ζ hζ))
    (hc : IsCompact (H : Set (E F ζ hζ))) (t : H) :
    KPGlobalCenterRationalCharacter.nu F ζ hζ t.val = 1 := by
  let f (a : E F ζ hζ) : ℝ :=
    (((KPGlobalCenterRationalCharacter.nu F ζ hζ a : ℝ≥0) : ℝ))
  have hp (a : E F ζ hζ) : 0 < f a := KPGlobalCenterRationalCharacter.nu_positive F ζ hζ a
  have hf : Continuous f := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))
  obtain ⟨k, hk, hmax⟩ := hc.exists_isMaxOn ⟨1, H.one_mem⟩ hf.continuousOn
  have hmul (a b : E F ζ hζ) : f (a * b) = f a * f b := by
    simp [f, map_mul, Units.val_mul, NNReal.coe_mul]
  have ht : f t.val ≤ 1 := by
    have h : f (k * t.val) ≤ f k := hmax (H.mul_mem hk t.property)
    rw [hmul] at h
    nlinarith [hp k]
  have hi : 1 ≤ f t.val := by
    have h : f (k * t.val⁻¹) ≤ f k := hmax (H.mul_mem hk (H.inv_mem t.property))
    rw [hmul] at h
    have hprod : f t.val * f t.val⁻¹ = 1 := by rw [← hmul]; simp [f]
    nlinarith [hp k, hp t.val, hp t.val⁻¹]
  apply Units.ext
  apply NNReal.coe_injective
  exact le_antisymm ht hi

theorem torus_closed : IsClosed ((KPGlobalTorusFunctionData.torus F ζ hζ) :
    Set (KPGlobalTorusFunctionData.G F ζ hζ)) := by
  have ho : IsClosed ((KPGlobalTorusFunctionData.ordinaryTorus F) :
      Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F)) := by
    let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
    apply hq.isQuotientMap.isClosed_preimage.mp
    have he : q ⁻¹' (KPGlobalTorusFunctionData.ordinaryTorus F : Set _) =
        {A : KPGlobalTorusFunctionData.AdelicMatrixGroup F | A 1 0 = 0 ∧ A 0 1 = 0} := by
      ext A
      constructor
      · intro hA
        obtain ⟨B, hB, h10, h01⟩ := hA
        rw [QuotientGroup.mk'_eq_mk'] at hB
        obtain ⟨z, hz, he⟩ := hB
        obtain ⟨u, rfl⟩ := hz
        rw [← he]
        simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h01, h10]
      · intro hA; exact ⟨A, rfl, hA⟩
    rw [he]
    have hc (i j : Fin 2) : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp
        (Units.continuous_val : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A.val)))
    exact (isClosed_eq (hc 1 0) continuous_const).inter (isClosed_eq (hc 0 1) continuous_const)
  exact ho.preimage (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous

theorem nu_level_trivial (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (j : E F ζ hζ) (hj : j ∈ ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)) :
    KPGlobalCenterRationalCharacter.nu F ζ hζ j = 1 := by
  let H := (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
    (KPGlobalTorusFunctionData.torus F ζ hζ).subtype
  have hc : IsCompact (H : Set (E F ζ hζ)) :=
    (torus_closed F ζ hζ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (J.isCompact.image continuous_subtype_val)
  exact nu_compact_subgroup F ζ hζ H hc ⟨j, hj⟩

namespace UntwistSmoothHelpers
noncomputable section
open KPGlobalTorusFunctionData
variable {T V ι : Type*} [Group T] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (H : Subgroup T) (χ ψ : H →* ℂˣ) (chart : V → T) (U : Set V)
  (hU : IsOpen U) (levels : ι → Subgroup T)
variable (e : ScalarFunctions H χ ≃ₗ[ℂ] ScalarFunctions H ψ)
  (a : T → ℂ) (ha : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => a (chart z * g)) U)
  (he : ∀ f t, (e f).val t = a t * f.val t)
  (hl : ∀ i, ∀ j : levels i, a j.val = 1)
  (hm : ∀ t u, a (t * u) = a t * a u)

include e a ha he hl hm
 theorem mem_level (i : ι) (f : ScalarFunctions H χ)
    (hf : f ∈ SmoothLevel H χ chart U (levels i)) :
    e f ∈ SmoothLevel H ψ chart U (levels i) := by
  constructor
  · intro g
    simpa only [he] using (ha g).mul (hf.1 g)
  · intro j
    apply Subtype.ext
    funext t
    change (e f).val (t * j.val) = (e f).val t
    rw [he, he, hm, hl i j, mul_one,
      rightLevel_covariance _ _ _ ⟨f, hf.2⟩ t j.val j.property]

 theorem mem_union (f : ScalarFunctions H χ)
    (hf : f ∈ SmoothUnion H χ chart U levels) :
    e f ∈ SmoothUnion H ψ chart U levels := by
  refine Submodule.iSup_induction
    (p := fun i => SmoothLevel H χ chart U (levels i))
    (motive := fun f => e f ∈ SmoothUnion H ψ chart U levels) hf ?_ ?_ ?_
  · intro i f hf
    exact (le_iSup (fun i => SmoothLevel H ψ chart U (levels i)) i)
      (mem_level H χ ψ chart U levels e a ha he hl hm i f hf)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro f g hf hg
    rw [map_add]; exact Submodule.add_mem _ hf hg

 def unionMap : SmoothUnion H χ chart U levels →ₗ[ℂ]
    SmoothUnion H ψ chart U levels where
  toFun f := ⟨e f.val, mem_union H χ ψ chart U levels e a ha he hl hm f.val f.property⟩
  map_add' f g := by apply Subtype.ext; exact e.map_add f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smul c f.val

 def stageMap (i : ι) : SmoothLevel H χ chart U (levels i) →ₗ[ℂ]
    SmoothLevel H ψ chart U (levels i) where
  toFun f := ⟨e f.val, mem_level H χ ψ chart U levels e a ha he hl hm i f.val f.property⟩
  map_add' f g := by apply Subtype.ext; exact e.map_add f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smul c f.val

 theorem unionMap_continuous :
    @Continuous _ _ (finalLocallyConvexTopology H χ chart U hU levels)
      (finalLocallyConvexTopology H ψ chart U hU levels)
      (unionMap H χ ψ chart U levels e a ha he hl hm) := by
  letI := finalLocallyConvexTopology H χ chart U hU levels
  letI := finalLocallyConvexTopology H ψ chart U hU levels
  let p := fun q : finalSeminorms H χ chart U hU levels => q.val
  let q := fun q : finalSeminorms H ψ chart U hU levels => q.val
  have hp : WithSeminorms p := ⟨rfl⟩
  have hq : WithSeminorms q := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  let A := unionMap H χ ψ chart U levels e a ha he hl hm
  apply WithSeminorms.continuous_of_continuous_comp
    (E := SmoothUnion H χ chart U levels) (F := SmoothUnion H ψ chart U levels)
    (𝕝 := ℂ) (𝕝₂ := ℂ)
    (τ₁₂ := RingHom.id ℂ) hq A
  intro r
  let u : finalSeminorms H χ chart U hU levels := ⟨r.val.comp A, fun i => by
    letI := smoothLevelTopology H χ chart U hU (levels i)
    letI := smoothLevelTopology H ψ chart U hU (levels i)
    have hs := KPGlobalTorusBorelNormTwistTransport.JetMultiplierRaw.linearMap_continuous
      H χ chart U hU (levels i) ψ
      (stageMap H χ ψ chart U levels e a ha he hl hm i) a ha (fun f t => he f.val t)
    exact (r.property i).comp hs⟩
  exact hp.continuous_seminorm u

omit e a ha he hl hm
 def smoothEquiv
    (e : ScalarFunctions H χ ≃ₗ[ℂ] ScalarFunctions H ψ)
    (a b : T → ℂ)
    (ha : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => a (chart z * g)) U)
    (hb : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => b (chart z * g)) U)
    (he : ∀ f t, (e f).val t = a t * f.val t)
    (hei : ∀ f t, (e.symm f).val t = b t * f.val t)
    (hl : ∀ i, ∀ j : levels i, a j.val = 1)
    (hli : ∀ i, ∀ j : levels i, b j.val = 1)
    (hm : ∀ t u, a (t * u) = a t * a u)
    (hmi : ∀ t u, b (t * u) = b t * b u) :
    letI := finalLocallyConvexTopology H χ chart U hU levels
    letI := finalLocallyConvexTopology H ψ chart U hU levels
    SmoothUnion H χ chart U levels ≃L[ℂ] SmoothUnion H ψ chart U levels := by
  letI := finalLocallyConvexTopology H χ chart U hU levels
  letI := finalLocallyConvexTopology H ψ chart U hU levels
  let L : SmoothUnion H χ chart U levels ≃ₗ[ℂ] SmoothUnion H ψ chart U levels :=
    LinearEquiv.ofLinear (unionMap H χ ψ chart U levels e a ha he hl hm)
      (unionMap H ψ χ chart U levels e.symm b hb hei hli hmi)
      (by ext f t; exact congrArg (fun f : ScalarFunctions H ψ => f.val t) (e.apply_symm_apply f.val))
      (by ext f t; exact congrArg (fun f : ScalarFunctions H χ => f.val t) (e.symm_apply_apply f.val))
  exact { L with
    continuous_toFun := unionMap_continuous H χ ψ chart U hU levels e a ha he hl hm
    continuous_invFun := unionMap_continuous H ψ χ chart U hU levels e.symm b hb hei hli hmi }

end
end UntwistSmoothHelpers

open KPGlobalTorusFunctionData
 theorem norm_smooth (g : E F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z =>
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ (torusArchChart F ζ hζ z * g) : ℝ≥0) : ℂ))
      (torusArchDomain F) := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fun z =>
      ((delta F ζ hζ (torusArchChart F ζ hζ z) : ℝ≥0) : ℝ)) (torusArchDomain F) := by
    have hp : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : TorusArch F => ∏ w : NumberField.InfinitePlace F, ‖z w‖ ^ 2) :=
      contDiff_prod (fun w _ => (contDiff_apply ℝ ℂ w).norm_sq ℝ)
    exact hp.contDiffOn.congr (fun z hz =>
      KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ z hz)
  have ht : ContDiffOn ℝ (⊤ : ℕ∞) (fun z =>
      ((delta F ζ hζ (torusArchChart F ζ hζ z * g) : ℝ≥0) : ℝ)) (torusArchDomain F) := by
    simpa only [map_mul, Units.val_mul, NNReal.coe_mul] using hd.mul contDiffOn_const
  have hn := ht.rpow_const_of_ne (p := (1 / 6 : ℝ)) (fun z _ => by
    exact_mod_cast Units.ne_zero (delta F ζ hζ (torusArchChart F ζ hζ z * g)))
  have hcn := Complex.ofRealCLM.contDiff.comp_contDiffOn hn
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun z =>
    (↑(((delta F ζ hζ (torusArchChart F ζ hζ z * g) : ℝ≥0) : ℝ) ^ (1 / 6 : ℝ)) : ℂ))
    (torusArchDomain F) at hcn
  convert hcn using 1
  funext z
  congr 1

 def normEquiv (H : Subgroup (E F ζ hζ)) (χ ψ : H →* ℂˣ)
    (e : ScalarFunctions H χ ≃ₗ[ℂ] ScalarFunctions H ψ)
    (he : ∀ f t, (e f).val t =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ t : ℝ≥0) : ℂ)⁻¹ * f.val t) :
    let levels := fun J : FiniteLevel F ζ hζ =>
      (globalLevel F ζ hζ J).comap (torus F ζ hζ).subtype
    letI := finalLocallyConvexTopology H χ (torusArchChart F ζ hζ)
      (torusArchDomain F) (torusArchDomain_open F) levels
    letI := finalLocallyConvexTopology H ψ (torusArchChart F ζ hζ)
      (torusArchDomain F) (torusArchDomain_open F) levels
    SmoothUnion H χ (torusArchChart F ζ hζ) (torusArchDomain F) levels ≃L[ℂ]
      SmoothUnion H ψ (torusArchChart F ζ hζ) (torusArchDomain F) levels := by
  let b (t : E F ζ hζ) := ((KPGlobalCenterRationalCharacter.nu F ζ hζ t : ℝ≥0) : ℂ)
  have hn (t : E F ζ hζ) : b t ≠ 0 := by
    dsimp [b]
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ t)
  have hm (t u : E F ζ hζ) : b (t * u) = b t * b u := by
    simp only [b, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
  apply UntwistSmoothHelpers.smoothEquiv H χ ψ
    (torusArchChart F ζ hζ) (torusArchDomain F) (torusArchDomain_open F)
    (fun J : FiniteLevel F ζ hζ => (globalLevel F ζ hζ J).comap (torus F ζ hζ).subtype)
    e (fun t => (b t)⁻¹) b
  · intro g
    exact (norm_smooth F ζ hζ g).inv (fun z _ => hn _)
  · exact norm_smooth F ζ hζ
  · exact he
  · intro f t
    have ht := he (e.symm f) t
    rw [e.apply_symm_apply] at ht
    change f.val t = (b t)⁻¹ * (e.symm f).val t at ht
    rw [ht]
    simp [hn t]
  · intro J j
    simp only [b, nu_level_trivial F ζ hζ J j.val j.property, Units.val_one,
      NNReal.coe_one, inv_one, Complex.ofReal_one]
  · intro J j
    simp only [b, nu_level_trivial F ζ hζ J j.val j.property, Units.val_one,
      NNReal.coe_one, Complex.ofReal_one]
  · intro t u
    rw [hm, mul_inv_rev, mul_comm]
  · exact hm

def untwistRational : RationalSmooth F ζ hζ ≃L[ℂ] RationalUnitary F ζ hζ :=
  normEquiv F ζ hζ (R F ζ hζ) (rationalModel F ζ hζ).character.toMonoidHom
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ).character.toMonoidHom
    (scalarUntwistRational F ζ hζ) (scalarUntwistRational_formula F ζ hζ)

def untwistProduct (C : ModelData F ζ hζ) :
    ProductSmooth F ζ hζ C ≃L[ℂ] ProductUnitary F ζ hζ C :=
  normEquiv F ζ hζ (B F ζ hζ C) (productModel F ζ hζ C).character.toMonoidHom
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C).character.toMonoidHom
    (scalarUntwistProduct F ζ hζ C) (scalarUntwistProduct_formula F ζ hζ C)

 theorem untwistRational_formula (h : RationalSmooth F ζ hζ) (g : E F ζ hζ) :
    (untwistRational F ζ hζ h).val.val g =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ)⁻¹ * h.val.val g := by
  exact scalarUntwistRational_formula F ζ hζ h.val g

 theorem untwistProduct_formula (C : ModelData F ζ hζ)
    (f : ProductSmooth F ζ hζ C) (g : E F ζ hζ) :
    (untwistProduct F ζ hζ C f).val.val g =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ)⁻¹ * f.val.val g := by
  exact scalarUntwistProduct_formula F ζ hζ C f.val g

 theorem retwistRational_formula (h : RationalUnitary F ζ hζ) (g : E F ζ hζ) :
    ((untwistRational F ζ hζ).symm h).val.val g =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) * h.val.val g := by
  have ht := untwistRational_formula F ζ hζ ((untwistRational F ζ hζ).symm h) g
  rw [ContinuousLinearEquiv.apply_symm_apply] at ht
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
  rw [ht]
  field_simp

 theorem retwistProduct_formula (C : ModelData F ζ hζ)
    (f : ProductUnitary F ζ hζ C) (g : E F ζ hζ) :
    ((untwistProduct F ζ hζ C).symm f).val.val g =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) * f.val.val g := by
  have ht := untwistProduct_formula F ζ hζ C ((untwistProduct F ζ hζ C).symm f) g
  rw [ContinuousLinearEquiv.apply_symm_apply] at ht
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
  rw [ht]
  field_simp

theorem nu_complex_mul (a b : E F ζ hζ) :
    ((KPGlobalCenterRationalCharacter.nu F ζ hζ (a * b) : ℝ≥0) : ℂ) =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ a : ℝ≥0) : ℂ) *
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ b : ℝ≥0) : ℂ) := by
  simp [map_mul, Units.val_mul, NNReal.coe_mul]

theorem rational_unit_inverse (r : R F ζ hζ) :
    (((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ r)⁻¹ : ℂˣ) : ℂ) =
      (((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r)⁻¹ : ℂˣ) : ℂ) *
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ r.val : ℝ≥0) : ℂ) := by
  change (((KPGlobalTorusFiniteStages.rationalUnitValue F ζ hζ r)⁻¹ : ℂˣ) : ℂ) = _
  simp [KPGlobalTorusFiniteStages.rationalUnitValue,
    KPGlobalCenterRationalCharacter.positiveComplex, div_eq_mul_inv]
  <;> ring

private theorem mul_div_div_cancel {G : Type*} [CommGroup G] (a b c : G) :
    a * b / (b / c) = a * c := by
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    a * b * (c * b⁻¹) = a * c * (b * b⁻¹) := by ac_rfl
    _ = a * c := by rw [mul_inv_cancel, mul_one]

set_option maxHeartbeats 800000 in

 theorem periodization_stage_locally_finite (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (s : PeriodizationRepresentatives F ζ hζ C) (g : E F ζ hζ) :
    ∃ U : Set (E F ζ hζ), U ∈ nhds g ∧
      ∃ S : Finset (PeriodizationIndex F ζ hζ C),
        ∀ (f : ProductSmooth F ζ hζ C),
          (untwistProduct F ζ hζ C f).val ∈
            KPGlobalTorusFiniteStages.Stage F ζ hζ C L (KPGlobalTorusFiniteStages.productModel F ζ hζ C) →
          ∀ g' ∈ U, ∀ a ∉ S, periodizationTerm F ζ hζ C s f g' a = 0 := by
  letI := KPGlobalCubicIdelePairing.hausdorff F
  letI := KPGlobalPrincipalCubicLagrangian.principal_discrete F ζ hζ
  let H := KPGlobalTorusFiniteStages.annihilator F ζ hζ L.K
  have hH := KPGlobalTorusFiniteStages.annihilator_compact_open F ζ hζ C L
  let T : Set (A F) := {a | a.val * pD F ζ hζ g ∈ H}
  have ht : IsCompact T := by
    have hc : IsCompact {d : KPGlobalCubicIdelePairing.D F | d * pD F ζ hζ g ∈ H} := by
      have he : {d : KPGlobalCubicIdelePairing.D F | d * pD F ζ hζ g ∈ H} =
          (fun d => d * (pD F ζ hζ g)⁻¹) '' (H : Set (KPGlobalCubicIdelePairing.D F)) := by
        ext d
        constructor
        · intro hd; exact ⟨d * pD F ζ hζ g, hd, by simp⟩
        · rintro ⟨d', hd', rfl⟩; simpa using hd'
      rw [he]
      exact hH.1.image (continuous_id.mul continuous_const)
    exact (Subgroup.isClosed_of_discrete (U := A F)).isClosedEmbedding_subtypeVal.isCompact_preimage hc
  let S : Finset (PeriodizationIndex F ζ hζ C) :=
    ht.finite_of_discrete.toFinset.image QuotientGroup.mk
  let U : Set (E F ζ hζ) := {g' | pD F ζ hζ g' / pD F ζ hζ g ∈ H}
  have hU : U ∈ nhds g := by
    have ho : IsOpen U := by
      change IsOpen ((fun g' => pD F ζ hζ g' * (pD F ζ hζ g)⁻¹) ⁻¹' (H : Set _))
      exact hH.2.preimage ((pD_continuous F ζ hζ).mul continuous_const)
    apply ho.mem_nhds
    change pD F ζ hζ g / pD F ζ hζ g ∈ H
    simp
  refine ⟨U, hU, S, ?_⟩
  intro f hf g' hg' a ha
  have hn : (s.lift a).val * g' ∉
      KPGlobalTorusFiniteStages.saturatedDomain F ζ hζ C L
        (KPGlobalTorusFiniteStages.productModel F ζ hζ C) := by
    rintro ⟨b, x, hx⟩
    have hbg : pD F ζ hζ ((s.lift a).val * g') ∈ H := by
      rw [hx, map_mul]
      exact H.mul_mem (KPGlobalTorusFiniteStages.product_inside_annihilator F ζ hζ C L b.property) x.property
    have hproj : pD F ζ hζ (s.lift a).val * pD F ζ hζ g ∈ H := by
      have hh := H.div_mem hbg hg'
      have he : pD F ζ hζ ((s.lift a).val * g') / (pD F ζ hζ g' / pD F ζ hζ g) =
          pD F ζ hζ (s.lift a).val * pD F ζ hζ g := by
        rw [map_mul]
        exact mul_div_div_cancel _ _ _
      rwa [he] at hh
    have hmem : a ∈ S := by
      apply Finset.mem_image.mpr
      refine ⟨rationalClass F ζ hζ (s.lift a), ?_, s.projects a⟩
      exact ht.finite_of_discrete.mem_toFinset.mpr hproj
    exact ha hmem
  have hz := hf.1 ((s.lift a).val * g') hn
  have hr := retwistProduct_formula F ζ hζ C (untwistProduct F ζ hζ C f)
    ((s.lift a).val * g')
  rw [ContinuousLinearEquiv.symm_apply_apply, hz, mul_zero] at hr
  simp only [periodizationTerm, hr, mul_zero]

 theorem periodization_locally_finite (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductSmooth F ζ hζ C)
    (g : E F ζ hζ) :
    ∃ U : Set (E F ζ hζ), U ∈ nhds g ∧
      ∃ S : Finset (PeriodizationIndex F ζ hζ C),
        ∀ g' ∈ U, ∀ a ∉ S, periodizationTerm F ζ hζ C s f g' a = 0 := by
  obtain ⟨L, hL⟩ := KPGlobalTorusFiniteStages.smooth_vector_in_stage F ζ hζ C
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C) (Or.inr rfl)
    (untwistProduct F ζ hζ C f)
  obtain ⟨U, hU, S, hS⟩ := periodization_stage_locally_finite F ζ hζ C L s g
  exact ⟨U, hU, S, hS f hL⟩

 theorem rawPeriodization_summable (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductSmooth F ζ hζ C)
    (g : E F ζ hζ) : Summable (periodizationTerm F ζ hζ C s f g) := by
  obtain ⟨U, hU, S, hS⟩ := periodization_locally_finite F ζ hζ C s f g
  apply summable_of_hasFiniteSupport
  apply S.finite_toSet.subset
  intro a ha
  by_contra hn
  exact ha (hS g (mem_of_mem_nhds hU) a hn)

private theorem rawPeriodization_class_mul (C : ModelData F ζ hζ)
    (r r' : R F ζ hζ) :
    periodizationClass F ζ hζ C (r * r') =
      periodizationClass F ζ hζ C r * periodizationClass F ζ hζ C r' := by
  simp only [periodizationClass, rationalClass, Subgroup.coe_mul, map_mul]
  rfl

private theorem rawPeriodization_weight_descends (C : ModelData F ζ hζ)
    (f : ProductSmooth F ζ hζ C) (g : E F ζ hζ) (u v : R F ζ hζ)
    (he : periodizationClass F ζ hζ C u = periodizationClass F ζ hζ C v) :
    (((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ u)⁻¹ : ℂˣ) : ℂ) * f.val.val (u.val * g) =
      (((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ v)⁻¹ : ℂˣ) : ℂ) * f.val.val (v.val * g) := by
  have hdj : pD F ζ hζ (u / v).val ∈ J F ζ hζ C := by
    have hx := QuotientGroup.eq_iff_div_mem.mp he
    change pD F ζ hζ u.val / pD F ζ hζ v.val ∈ J F ζ hζ C at hx
    simpa only [Subgroup.coe_div, map_div] using hx
  let b : B F ζ hζ C := ⟨(u / v).val, hdj.2⟩
  have hu : u = (u / v) * v := by simp
  have hchar := C.agrees b (u / v) rfl
  have hcov := f.val.property b (v.val * g)
  change f.val.val (b.val * (v.val * g)) =
    (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b : ℂ) * f.val.val (v.val * g) at hcov
  rw [hu, map_mul]
  simp only [Subgroup.coe_mul, mul_assoc]
  rw [hcov, hchar]
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have hn : (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (u / v) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

private theorem rawPeriodization_translate_term (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductSmooth F ζ hζ C)
    (r : R F ζ hζ) (g : E F ζ hζ) (x : PeriodizationIndex F ζ hζ C) :
    periodizationTerm F ζ hζ C s f (r.val * g) x =
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
        periodizationTerm F ζ hζ C s f g (periodizationClass F ζ hζ C r * x) := by
  have he : periodizationClass F ζ hζ C (r * s.lift x) =
      periodizationClass F ζ hζ C (s.lift (periodizationClass F ζ hζ C r * x)) := by
    rw [rawPeriodization_class_mul, s.projects, s.projects]
  have hd := rawPeriodization_weight_descends F ζ hζ C f g
    (r * s.lift x) (s.lift (periodizationClass F ζ hζ C r * x)) he
  unfold periodizationTerm
  rw [← hd]
  have hc : (s.lift x).val * r.val = r.val * (s.lift x).val :=
    ((KPGlobalCenterRationalCharacter.R_maximal_abelian F ζ hζ).1
      (s.lift x).val (s.lift x).property r.val r.property).eq
  simp only [map_mul, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [← mul_assoc, hc, mul_assoc]
  have hn : (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

 theorem rawPeriodization_left_covariant (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductSmooth F ζ hζ C)
    (r : R F ζ hζ) (g : E F ζ hζ) :
    (∑' x, periodizationTerm F ζ hζ C s f (r.val * g) x) =
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
        ∑' x, periodizationTerm F ζ hζ C s f g x := by
  simp_rw [rawPeriodization_translate_term F ζ hζ C s f r g]
  rw [tsum_mul_left]
  exact congrArg (fun z : ℂ => (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * z)
    ((Equiv.mulLeft (periodizationClass F ζ hζ C r)).tsum_eq
      (periodizationTerm F ζ hζ C s f g))

 def rawPeriodization (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) :
    ProductSmooth F ζ hζ C →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (rationalModel F ζ hζ) where
  toFun f := ⟨fun g => ∑' x, periodizationTerm F ζ hζ C s f g x,
    rawPeriodization_left_covariant F ζ hζ C s f⟩
  map_add' f k := by
    apply Subtype.ext
    funext g
    change (∑' x, periodizationTerm F ζ hζ C s (f + k) g x) = _
    have he : periodizationTerm F ζ hζ C s (f + k) g =
        fun x => periodizationTerm F ζ hζ C s f g x + periodizationTerm F ζ hζ C s k g x := by
      funext x
      simp only [periodizationTerm, Submodule.coe_add, Pi.add_apply, mul_add]
    rw [he, (rawPeriodization_summable F ζ hζ C s f g).tsum_add
      (rawPeriodization_summable F ζ hζ C s k g)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext g
    change (∑' x, periodizationTerm F ζ hζ C s (c • f) g x) = _
    have he : periodizationTerm F ζ hζ C s (c • f) g =
        fun x => c * periodizationTerm F ζ hζ C s f g x := by
      funext x
      simp only [periodizationTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, tsum_mul_left]
    rfl

 def rawUnitaryPeriodization (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) :
    ProductUnitary F ζ hζ C →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) :=
  (scalarUntwistRational F ζ hζ).toLinearMap.comp
    ((rawPeriodization F ζ hζ C s).comp (untwistProduct F ζ hζ C).symm.toLinearMap)

private theorem rawUnitaryPeriodization_formula (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C)
    (f : ProductUnitary F ζ hζ C) (g : E F ζ hζ) :
    (rawUnitaryPeriodization F ζ hζ C s f).val g =
      ∑' a, (((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) *
        f.val.val ((s.lift a).val * g) := by
  change (scalarUntwistRational F ζ hζ
    (rawPeriodization F ζ hζ C s ((untwistProduct F ζ hζ C).symm f))).val g = _
  rw [scalarUntwistRational_formula]
  change _ * (∑' a, periodizationTerm F ζ hζ C s ((untwistProduct F ζ hζ C).symm f) g a) = _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [periodizationTerm, retwistProduct_formula, rational_unit_inverse, nu_complex_mul]
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
  field_simp
  <;> ring

private theorem rawUnitaryPeriodization_stage (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductUnitary F ζ hζ C)
    (hf : f.val ∈ KPGlobalTorusFiniteStages.Stage F ζ hζ C L
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C)) :
    rawUnitaryPeriodization F ζ hζ C s f ∈ KPGlobalTorusFiniteStages.Stage F ζ hζ C L
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) := by
  constructor
  · intro g hg
    rw [rawUnitaryPeriodization_formula]
    suffices hh : ∀ a, (((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) *
        f.val.val ((s.lift a).val * g) = 0 by simp only [hh, tsum_zero]
    intro a
    have hn : (s.lift a).val * g ∉ KPGlobalTorusFiniteStages.saturatedDomain F ζ hζ C L
        (KPGlobalTorusFiniteStages.productModel F ζ hζ C) := by
      rintro ⟨b, x, he⟩
      have hb : b.val ∈ KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L :=
        KPGlobalTorusFiniteStages.product_inside_annihilator F ζ hζ C L b.property
      apply hg
      refine ⟨(s.lift a)⁻¹, ⟨b.val * x.val,
        (KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L).mul_mem hb x.property⟩, ?_⟩
      have hh := congrArg (fun t : E F ζ hζ => (s.lift a).val⁻¹ * t) he
      change g = (s.lift a).val⁻¹ * (b.val * x.val)
      simpa only [inv_mul_cancel_left] using hh
    rw [hf.1 _ hn, mul_zero]
  · intro k x
    rw [rawUnitaryPeriodization_formula, rawUnitaryPeriodization_formula, ← tsum_mul_left]
    apply tsum_congr
    intro a
    have hall := KPGlobalTorusTensorFibers.scalar_phase_global_covariance
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C).H
      (KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L)
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C).character.toMonoidHom
      f.val hf.1 k.val (KPGlobalTorusFiniteStages.phase_inside_domain F ζ hζ C L k.property)
      (KPGlobalTorusFiniteStages.phaseCharacter F ζ hζ C L k : ℂ)
      (fun y => hf.2 k y) ((s.lift a).val * x.val)
    rw [← mul_assoc, hall]
    ring

 theorem rawUnitaryPeriodization_smooth (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductUnitary F ζ hζ C) :
    rawUnitaryPeriodization F ζ hζ C s f ∈ RationalUnitary F ζ hζ := by
  obtain ⟨L, hL⟩ := KPGlobalTorusFiniteStages.smooth_vector_in_stage F ζ hζ C
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C) (Or.inr rfl) f
  obtain ⟨U, hU⟩ := KPGlobalTorusFiniteStages.stage_in_smooth_level F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) (Or.inl rfl)
  exact Submodule.mem_iSup_of_mem U (hU (rawUnitaryPeriodization_stage F ζ hζ C L s f hL))

 def smoothUnitaryPeriodization (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) :
    ProductUnitary F ζ hζ C →ₗ[ℂ] RationalUnitary F ζ hζ :=
  (rawUnitaryPeriodization F ζ hζ C s).codRestrict _ (rawUnitaryPeriodization_smooth F ζ hζ C s)

def smoothPeriodization (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) :
    ProductSmooth F ζ hζ C →ₗ[ℂ] RationalSmooth F ζ hζ :=
  (untwistRational F ζ hζ).symm.toLinearMap.comp
    ((smoothUnitaryPeriodization F ζ hζ C s).comp (untwistProduct F ζ hζ C).toLinearMap)

theorem smoothPeriodization_formula (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductSmooth F ζ hζ C) (g : E F ζ hζ) :
    (smoothPeriodization F ζ hζ C s f).val.val g = ∑' a, periodizationTerm F ζ hζ C s f g a := by
  change ((untwistRational F ζ hζ).symm
    (smoothUnitaryPeriodization F ζ hζ C s (untwistProduct F ζ hζ C f))).val.val g = _
  rw [retwistRational_formula]
  change _ * (rawUnitaryPeriodization F ζ hζ C s (untwistProduct F ζ hζ C f)).val g = _
  change _ * (scalarUntwistRational F ζ hζ
    (rawPeriodization F ζ hζ C s ((untwistProduct F ζ hζ C).symm (untwistProduct F ζ hζ C f)))).val g = _
  rw [ContinuousLinearEquiv.symm_apply_apply, scalarUntwistRational_formula]
  change _ * (_ * (∑' a, periodizationTerm F ζ hζ C s f g a)) = _
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

 abbrev periodizationLevelJets (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :=
  fun i : E F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (KPGlobalTorusFunctionData.torusArchDomain F) =>
    KPGlobalTorusFunctionData.jetSeminorm Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) i.1 i.2.1 i.2.2

private theorem periodization_level_separating (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) (hf : f ≠ 0) :
    ∃ i, periodizationLevelJets F ζ hζ Q U i f ≠ 0 := by
  have hn : ∃ g : E F ζ hζ, f.val.val g ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hf
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hh g
  obtain ⟨g, hg⟩ := hn
  let z : KPGlobalTorusFunctionData.TorusArch F := fun _ => 1
  have hz : z ∈ KPGlobalTorusFunctionData.torusArchDomain F := by
    intro w
    exact one_ne_zero
  let K : KPGlobalTorusFunctionData.JetCompact (KPGlobalTorusFunctionData.torusArchDomain F) :=
    ⟨{z}, isCompact_singleton, Set.singleton_subset_iff.mpr hz⟩
  refine ⟨((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z)⁻¹ * g, 0, K), ?_⟩
  change KPGlobalTorusFunctionData.jetBound Q.H Q.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
    (KPGlobalTorusFunctionData.torusArchDomain F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
    ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z)⁻¹ * g) 0 K f ≠ 0
  simpa only [KPGlobalTorusFunctionData.jetBound, K, Set.image_singleton, csSup_singleton,
    norm_iteratedFDerivWithin_zero, mul_inv_cancel_left, norm_ne_zero_iff] using hg

set_option maxHeartbeats 1000000 in
private theorem periodization_stage_t2 (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hU : KPGlobalTorusFiniteStages.Stage F ζ hζ C L Q ≤
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) :
    @T2Space (KPGlobalTorusFiniteStages.Stage F ζ hζ C L Q)
      (KPGlobalTorusFiniteStages.stageTopology F ζ hζ C L Q U hU) := by
  letI := KPGlobalTorusFiniteStages.stageTopology F ζ hζ C L Q U hU
  letI := KPGlobalTorusFunctionData.smoothLevelTopology Q.H Q.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
    (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  have hp : WithSeminorms (periodizationLevelJets F ζ hζ Q U) := ⟨rfl⟩
  letI : IsTopologicalAddGroup (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) := hp.isTopologicalAddGroup
  letI : T1Space (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) :=
    hp.T1_of_separating (periodization_level_separating F ζ hζ Q U)
  letI : T2Space (KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) :=
    IsTopologicalAddGroup.t2Space_iff_zero_closed.mpr (isClosed_singleton)
  exact T2Space.of_injective_continuous (Submodule.inclusion_injective hU) continuous_induced_dom

set_option maxHeartbeats 1000000 in
private theorem periodization_stage_polynorms (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hU : KPGlobalTorusFiniteStages.Stage F ζ hζ C L Q ≤
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q U) :
    @WithSeminorms ℂ (KPGlobalTorusFiniteStages.Stage F ζ hζ C L Q) _ _ _ _
      (fun i => (periodizationLevelJets F ζ hζ Q U i).comp (σ₁₂ := RingHom.id ℂ) (Submodule.inclusion hU))
      (KPGlobalTorusFiniteStages.stageTopology F ζ hζ C L Q U hU) := by
  letI := KPGlobalTorusFunctionData.smoothLevelTopology Q.H Q.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
    (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  have hp : WithSeminorms (periodizationLevelJets F ζ hζ Q U) := ⟨rfl⟩
  have hh := LinearMap.withSeminorms_induced (E := KPGlobalTorusFiniteStages.Stage F ζ hζ C L Q)
    (σ₁₂ := RingHom.id ℂ) hp (Submodule.inclusion hU)
  exact hh

 abbrev periodizationUnionJets (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :=
  KPGlobalTorusFunctionData.finalSeminorms Q.H Q.character.toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
    (KPGlobalTorusFunctionData.torusArchDomain F)
    (KPGlobalTorusFunctionData.torusArchDomain_open F)
    (fun U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
      (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)

set_option maxHeartbeats 1000000 in
private theorem smoothUnitaryPeriodization_continuous (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) :
    Continuous (smoothUnitaryPeriodization F ζ hζ C s) := by
  let Q := KPGlobalTorusFiniteStages.rationalModel F ζ hζ
  have hq : WithSeminorms (fun q : periodizationUnionJets F ζ hζ Q => q.val) := ⟨rfl⟩
  letI : IsTopologicalAddGroup (RationalUnitary F ζ hζ) := hq.isTopologicalAddGroup
  letI : ContinuousSMul ℂ (RationalUnitary F ζ hζ) := hq.continuousSMul
  letI : ContinuousSMul ℝ (RationalUnitary F ζ hζ) := ⟨by
    have hh := ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd :
      Continuous (fun x : ℝ × RationalUnitary F ζ hζ => (x.1 : ℂ) • x.2))
    convert hh using 1
    funext x
    exact (IsScalarTower.algebraMap_smul ℂ x.1 x.2).symm⟩
  letI : LocallyConvexSpace ℝ (RationalUnitary F ζ hζ) :=
    KPGlobalTorusFunctionData.finalLocallyConvexTopology_locallyConvex Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      (fun U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
        (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  refine (KPGlobalTorusFiniteStages.levelwise_final_topology F ζ hζ C
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C) (Or.inr rfl)
    (V := RationalUnitary F ζ hζ) (T := smoothUnitaryPeriodization F ζ hζ C s)).mpr ?_
  intro L U hU
  letI := KPGlobalTorusFiniteStages.stageTopology F ζ hζ C L
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C) U hU
  have hp := periodization_stage_polynorms F ζ hζ C L
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C) U hU
  letI : IsTopologicalAddGroup (KPGlobalTorusFiniteStages.Stage F ζ hζ C L
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C)) := hp.isTopologicalAddGroup
  letI : ContinuousSMul ℂ (KPGlobalTorusFiniteStages.Stage F ζ hζ C L
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C)) := hp.continuousSMul
  letI := periodization_stage_t2 F ζ hζ C L (KPGlobalTorusFiniteStages.productModel F ζ hζ C) U hU
  letI := KPGlobalTorusFiniteStages.stage_module_finite F ζ hζ C L
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C) (Or.inr rfl)
  exact LinearMap.continuous_of_finiteDimensional (𝕜 := ℂ)
    (E := KPGlobalTorusFiniteStages.Stage F ζ hζ C L (KPGlobalTorusFiniteStages.productModel F ζ hζ C))
    (F' := RationalUnitary F ζ hζ)
    ((smoothUnitaryPeriodization F ζ hζ C s).comp (Submodule.inclusion
      (hU.trans (le_iSup (fun W : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
        KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
          (KPGlobalTorusFiniteStages.productModel F ζ hζ C) W) U))))

theorem smoothPeriodization_continuous (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) : Continuous (smoothPeriodization F ζ hζ C s) :=
  (untwistRational F ζ hζ).symm.continuous.comp
    ((smoothUnitaryPeriodization_continuous F ζ hζ C s).comp (untwistProduct F ζ hζ C).continuous)

end
end DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse

section

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse
noncomputable section
set_option autoImplicit false
attribute [local instance] modelTopology

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev AveragingQuotient (C : ModelData F ζ hζ) :=
  B F ζ hζ C ⧸ intersectionInB F ζ hζ C

 theorem averagingClass_same_coset (C : ModelData F ζ hζ)
    (b b' : B F ζ hζ C)
    (h : (QuotientGroup.mk b : AveragingQuotient F ζ hζ C) = QuotientGroup.mk b') :
    averagingClass F ζ hζ C b = averagingClass F ζ hζ C b' := by
  apply QuotientGroup.eq.mpr
  have hr := QuotientGroup.eq.mp h
  have hi : (b⁻¹ * b').val ∈ R F ζ hζ ⊓ B F ζ hζ C := ⟨hr, (b⁻¹ * b').property⟩
  rw [KPGlobalProductPolarizationCharacter.rational_intersection_preimage F ζ hζ C] at hi
  change (pD F ζ hζ b.val)⁻¹ * pD F ζ hζ b'.val ∈ J F ζ hζ C
  simpa only [Subgroup.mem_comap, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using hi

 theorem compact_quotient_identification (C : ModelData F ζ hζ) :
    ∃ e : AveragingQuotient F ζ hζ C ≃ₜ CompactIndex F ζ hζ C,
      (∀ b, e (QuotientGroup.mk b) = averagingClass F ζ hζ C b) ∧
      (∀ x y, e (x * y) = e x * e y) := by
  let f : B F ζ hζ C →* CompactIndex F ζ hζ C :=
    (QuotientGroup.mk' _).comp
      ((pD F ζ hζ).restrict (fun _ hb => hb))
  have hk : intersectionInB F ζ hζ C = f.ker := by
    ext b
    change b.val ∈ R F ζ hζ ↔ f b = 1
    change b.val ∈ R F ζ hζ ↔
      (QuotientGroup.mk (⟨pD F ζ hζ b.val, b.property⟩ : M F ζ hζ C) : CompactIndex F ζ hζ C) = 1
    rw [QuotientGroup.eq_one_iff]
    change b.val ∈ R F ζ hζ ↔ pD F ζ hζ b.val ∈ J F ζ hζ C
    have hi := KPGlobalProductPolarizationCharacter.rational_intersection_preimage F ζ hζ C
    have he : b.val ∈ R F ζ hζ ⊓ B F ζ hζ C ↔ b.val ∈ R F ζ hζ := by
      simp only [Subgroup.mem_inf, b.property, and_true]
    rw [← he, hi]
    rfl
  let π := KPGlobalTorusFiniteStagesCofinality.finiteTorusClassProjection F ζ hζ
  obtain ⟨hπc, hπo, hπs, _⟩ :=
    KPGlobalTorusFiniteStagesCofinality.finite_torus_projection_and_phase_trivial_class_lifts
      F ζ hζ C C.adjustment
  let X := π ⁻¹' (M F ζ hζ C : Set (KPGlobalCubicIdelePairing.D F))
  let r : X → M F ζ hζ C := (M F ζ hζ C : Set (KPGlobalCubicIdelePairing.D F)).restrictPreimage π
  have hr : IsOpenQuotientMap r :=
    (show IsOpenQuotientMap π from ⟨hπs, hπc, hπo⟩).restrictPreimage _
  let b : X → B F ζ hζ C := fun x => ⟨x.val.val, x.property⟩
  have hbc : Continuous b := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let q : X → CompactIndex F ζ hζ C := fun x => QuotientGroup.mk (r x)
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk.comp hr
  have hfb (x : X) : f (b x) = q x := rfl
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hq.surjective y
    exact ⟨b x, (hfb x).trans hx⟩
  let e := (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (b : B F ζ hζ C) : e (QuotientGroup.mk b) = f b := rfl
  have hfc : Continuous f := QuotientGroup.continuous_mk.comp
    (((pD_continuous F ζ hζ).comp continuous_subtype_val).subtype_mk _)
  have hc : Continuous e := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hfc
  have hi : Continuous e.symm := hq.isQuotientMap.continuous_iff.mpr (by
    have hh : e.symm ∘ q = fun x => QuotientGroup.mk (b x) := by
      funext x
      rw [Function.comp_apply, ← hfb, ← he, e.symm_apply_apply]
    rw [hh]
    exact QuotientGroup.continuous_mk.comp hbc)
  exact ⟨⟨e.toEquiv, hc, hi⟩, he, e.map_mul⟩

structure AveragingRepresentatives (C : ModelData F ζ hζ) where
  lift : CompactIndex F ζ hζ C → B F ζ hζ C
  projects : ∀ x, averagingClass F ζ hζ C (lift x) = x

private theorem torusProjection_surjective : Function.Surjective (KPGlobalTorusFunctionData.p F ζ hζ) := by
  intro y
  let a : KPAdelicCoverRestrictedProduct.AdelicGL2 F :=
    ⟨Matrix.diagonal (fun i : Fin 2 => if i = 0 then (y : KPGlobalTorusFunctionData.Adeles F) else 1),
     Matrix.diagonal (fun i : Fin 2 => if i = 0 then (↑(y⁻¹) : KPGlobalTorusFunctionData.Adeles F) else 1),
     by simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]; funext i; split_ifs <;> simp,
     by simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]; funext i; split_ifs <;> simp⟩
  obtain ⟨b, hb⟩ := KPAdelicCoverRestrictedProduct.projection_surjective F ζ hζ a
  let g := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ b
  have hg : g ∈ E F ζ hζ := by
    refine ⟨a, ?_, ?_, ?_⟩
    · change QuotientGroup.mk' _ a = QuotientGroup.lift _ _ _ (QuotientGroup.mk b)
      simp only [QuotientGroup.lift_mk, MonoidHom.comp_apply, hb]
    · simp [a, Matrix.diagonal_apply]
    · simp [a, Matrix.diagonal_apply]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Units.val_injective
  let t : KPGlobalTorusFunctionData.ordinaryTorus F :=
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g, hg⟩
  have ha : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) a = t.val := by
    change QuotientGroup.mk' _ a = QuotientGroup.lift _ _ _ (QuotientGroup.mk b)
    simp only [QuotientGroup.lift_mk, MonoidHom.comp_apply, hb]
  have h10 : a 1 0 = 0 := by simp [a, Matrix.diagonal_apply]
  have h01 : a 0 1 = 0 := by simp [a, Matrix.diagonal_apply]
  have h11 : (KPGlobalTorusFunctionData.diagonal_entries_units F a h10 h01).2.unit = 1 := by
    apply Units.val_injective
    rw [IsUnit.unit_spec]
    simp [a, Matrix.diagonal_apply]
  change (KPGlobalTorusFunctionData.torusRatio F t : KPGlobalTorusFunctionData.Adeles F) = _
  rw [KPGlobalTorusFunctionData.ratio_formula F t a ha h10 h01, h11, inv_one, Units.val_one, mul_one, IsUnit.unit_spec]
  simp [a, Matrix.diagonal_apply]

 theorem averaging_representatives_exist (C : ModelData F ζ hζ) :
    Nonempty (AveragingRepresentatives F ζ hζ C) := by
  have hp : Function.Surjective (pD F ζ hζ) :=
    (QuotientGroup.mk'_surjective _).comp (torusProjection_surjective F ζ hζ)
  have hs : Function.Surjective (averagingClass F ζ hζ C) := by
    intro x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, hb⟩ := hp m.val
    refine ⟨⟨b, ?_⟩, ?_⟩
    · change pD F ζ hζ b ∈ M F ζ hζ C
      rw [hb]
      exact m.property
    · unfold averagingClass
      apply congrArg QuotientGroup.mk
      exact Subtype.ext hb
  exact ⟨⟨fun x => Classical.choose (hs x), fun x => Classical.choose_spec (hs x)⟩⟩

def averagingIntegrand (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ)
    (g : E F ζ hζ) (x : CompactIndex F ζ hζ C) : ℂ :=
  ((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment (s.lift x))⁻¹ : ℂˣ) *
    h.val.val ((s.lift x).val * g)

 theorem weighted_integrand_descends (C : ModelData F ζ hζ)
    (h : RationalSmooth F ζ hζ) (g : E F ζ hζ) (b b' : B F ζ hζ C)
    (heq : averagingClass F ζ hζ C b = averagingClass F ζ hζ C b') :
    (((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b)⁻¹ : ℂˣ) : ℂ) *
        h.val.val (b.val * g) =
      (((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b')⁻¹ : ℂˣ) : ℂ) *
        h.val.val (b'.val * g)  := by
  let d : B F ζ hζ C := b / b'
  have hdj : pD F ζ hζ d.val ∈ J F ζ hζ C := by
    have hx := QuotientGroup.eq_iff_div_mem.mp heq
    change pD F ζ hζ b.val / pD F ζ hζ b'.val ∈ J F ζ hζ C at hx
    simpa only [d, Subgroup.coe_div, map_div] using hx
  have hdi : d.val ∈ R F ζ hζ ⊓ B F ζ hζ C := by
    rw [KPGlobalProductPolarizationCharacter.rational_intersection_preimage F ζ hζ C]
    exact hdj
  let r : R F ζ hζ := ⟨d.val, hdi.1⟩
  have hb : b = d * b' := by dsimp [d]; simp
  have hchar := C.agrees d r rfl
  have hcov := h.val.property r (b'.val * g)
  change h.val.val (r.val * (b'.val * g)) =
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * h.val.val (b'.val * g) at hcov
  rw [hb, map_mul]
  simp only [Subgroup.coe_mul, mul_assoc]
  rw [hcov, ← hchar]
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have hn : (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment d : ℂ) ≠ 0 :=
    Units.ne_zero _
  field_simp

 theorem averagingIntegrand_independent (C : ModelData F ζ hζ)
    (s t : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ)
    (g : E F ζ hζ) (x : CompactIndex F ζ hζ C) :
    averagingIntegrand F ζ hζ C s h g x = averagingIntegrand F ζ hζ C t h g x := by
  exact weighted_integrand_descends F ζ hζ C h g (s.lift x) (t.lift x)
    ((s.projects x).trans (t.projects x).symm)

namespace ScalarUntwistHelpers
variable {T : Type*} [Group T] (H : Subgroup T) (χ ψ : H →* ℂˣ) (η : T →* ℂˣ)
variable (hψ : ∀ h : H, ψ h = χ h * η h.val)

end ScalarUntwistHelpers

private theorem scalarUntwistRational_rightLevel
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (rationalModel F ζ hζ))
    (hf : f ∈ KPGlobalTorusFunctionData.RightLevel (rationalModel F ζ hζ).H
      (rationalModel F ζ hζ).character.toMonoidHom
        ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)) :
    scalarUntwistRational F ζ hζ f ∈ KPGlobalTorusFunctionData.RightLevel
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ).H
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ).character.toMonoidHom
        ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) := by
  intro j
  apply Subtype.ext
  funext t
  change (scalarUntwistRational F ζ hζ f).val (t * j.val) =
    (scalarUntwistRational F ζ hζ f).val t
  rw [scalarUntwistRational_formula, scalarUntwistRational_formula, map_mul,
    nu_level_trivial F ζ hζ J j.val j.property, mul_one,
    KPGlobalTorusFunctionData.rightLevel_covariance _ _ _ ⟨f, hf⟩ t j.val j.property]

private theorem scalarUntwistProduct_rightLevel (C : ModelData F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (productModel F ζ hζ C))
    (hf : f ∈ KPGlobalTorusFunctionData.RightLevel (productModel F ζ hζ C).H
      (productModel F ζ hζ C).character.toMonoidHom
        ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)) :
    scalarUntwistProduct F ζ hζ C f ∈ KPGlobalTorusFunctionData.RightLevel
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C).H
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C).character.toMonoidHom
        ((KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) := by
  intro j
  apply Subtype.ext
  funext t
  change (scalarUntwistProduct F ζ hζ C f).val (t * j.val) =
    (scalarUntwistProduct F ζ hζ C f).val t
  rw [scalarUntwistProduct_formula, scalarUntwistProduct_formula, map_mul,
    nu_level_trivial F ζ hζ J j.val j.property, mul_one,
    KPGlobalTorusFunctionData.rightLevel_covariance _ _ _ ⟨f, hf⟩ t j.val j.property]

namespace UntwistSmoothHelpers
noncomputable section
open KPGlobalTorusFunctionData
variable {T V ι : Type*} [Group T] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (H : Subgroup T) (χ ψ : H →* ℂˣ) (chart : V → T) (U : Set V)
  (hU : IsOpen U) (levels : ι → Subgroup T)
variable (e : ScalarFunctions H χ ≃ₗ[ℂ] ScalarFunctions H ψ)
  (a : T → ℂ) (ha : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => a (chart z * g)) U)
  (he : ∀ f t, (e f).val t = a t * f.val t)
  (hl : ∀ i, ∀ j : levels i, a j.val = 1)
  (hm : ∀ t u, a (t * u) = a t * a u)

include e a ha he hl hm

omit e a ha he hl hm

end
end UntwistSmoothHelpers

open KPGlobalTorusFunctionData

theorem product_unit_inverse (C : ModelData F ζ hζ) (b : B F ζ hζ C) :
    (((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment b)⁻¹ : ℂˣ) : ℂ) =
      (((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b)⁻¹ : ℂˣ) : ℂ) *
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ b.val : ℝ≥0) : ℂ) := by
  change (((KPGlobalTorusFiniteStages.productUnitValue F ζ hζ C C.adjustment b)⁻¹ : ℂˣ) : ℂ) = _
  simp [KPGlobalTorusFiniteStages.productUnitValue,
    KPGlobalCenterRationalCharacter.positiveComplex, div_eq_mul_inv]
  <;> ring

private theorem stage_weight_locally_constant (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (f : RationalUnitary F ζ hζ)
    (hf : f.val ∈ KPGlobalTorusFiniteStages.Stage F ζ hζ C L
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ)) :
    IsLocallyConstant (fun b : B F ζ hζ C =>
      (((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment b)⁻¹ : ℂˣ) : ℂ) * f.val.val b.val) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro b
  let U : Set (B F ζ hζ C) := {b' | pD F ζ hζ (b⁻¹ * b').val ∈ L.K}
  have ho : IsOpen U := L.open'.preimage
    ((pD_continuous F ζ hζ).comp (continuous_const.mul continuous_subtype_val))
  refine ⟨U, ho, ?_, ?_⟩
  · change pD F ζ hζ (b⁻¹ * b).val ∈ L.K
    simp
  · intro b' hb'
    let k : KPGlobalTorusFiniteStages.phaseGroup F ζ hζ C L := ⟨(b⁻¹ * b').val, hb'⟩
    have hphase : ∀ x : KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L,
        f.val.val (x.val * k.val) =
          (KPGlobalTorusFiniteStages.phaseCharacter F ζ hζ C L k : ℂ) * f.val.val x.val :=
      fun x => hf.2 k x
    have hall := KPGlobalTorusTensorFibers.scalar_phase_global_covariance
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ).H
      (KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L)
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ).character.toMonoidHom
      f.val hf.1 k.val (KPGlobalTorusFiniteStages.phase_inside_domain F ζ hζ C L k.property)
      (KPGlobalTorusFiniteStages.phaseCharacter F ζ hζ C L k : ℂ) hphase b.val
    have hb : b'.val = b.val * k.val := by dsimp [k]; simp
    have hk : (KPGlobalTorusFiniteStages.phaseCharacter F ζ hζ C L k : ℂ) =
        (KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment (b⁻¹ * b') : ℂ) := rfl
    have he : b' = b * (b⁻¹ * b') := by simp
    rw [hb, hall, hk, he, map_mul]
    simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
    have hn : (KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment (b⁻¹ * b') : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    simp only [inv_mul_cancel_left]

 theorem averagingIntegrand_continuous (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ) (g : E F ζ hζ) :
    Continuous (averagingIntegrand F ζ hζ C s h g) := by
  let v := rightAction F ζ hζ (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) g
    (untwistRational F ζ hζ h)
  obtain ⟨L, hL⟩ := KPGlobalTorusFiniteStages.smooth_vector_in_stage F ζ hζ C
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) (Or.inl rfl) v
  obtain ⟨e, he, _⟩ := compact_quotient_identification F ζ hζ C
  have hq : Topology.IsQuotientMap (averagingClass F ζ hζ C) := by
    have hh : e ∘ QuotientGroup.mk = averagingClass F ζ hζ C := funext he
    rw [← hh]
    exact e.isQuotientMap.comp (QuotientGroup.isQuotientMap_mk _)
  apply hq.continuous_iff.mpr
  have hh : averagingIntegrand F ζ hζ C s h g ∘ averagingClass F ζ hζ C =
      fun b : B F ζ hζ C =>
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) *
        ((((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment b)⁻¹ : ℂˣ) : ℂ) * v.val.val b.val) := by
    funext b
    change averagingIntegrand F ζ hζ C s h g (averagingClass F ζ hζ C b) = _
    have hd := weighted_integrand_descends F ζ hζ C h g
      (s.lift (averagingClass F ζ hζ C b)) b (s.projects _)
    change averagingIntegrand F ζ hζ C s h g (averagingClass F ζ hζ C b) =
      (((KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b)⁻¹ : ℂˣ) : ℂ) * h.val.val (b.val * g) at hd
    rw [hd, product_unit_inverse]
    change _ = _ * (_ * (untwistRational F ζ hζ h).val.val (b.val * g))
    rw [untwistRational_formula, nu_complex_mul]
    have hnb : ((KPGlobalCenterRationalCharacter.nu F ζ hζ b.val : ℝ≥0) : ℂ) ≠ 0 := by
      exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ b.val)
    have hng : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
      exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
    field_simp
  rw [hh]
  exact continuous_const.mul (stage_weight_locally_constant F ζ hζ C L v hL).continuous

 theorem averagingIntegrand_integrable (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ)
    (g : E F ζ hζ) :
    Integrable (averagingIntegrand F ζ hζ C s h g) (probabilityHaar F ζ hζ C) := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    (averagingIntegrand_continuous F ζ hζ C s h g).continuousOn.integrableOn_compact
      (μ := probabilityHaar F ζ hζ C) isCompact_univ

private theorem rawAveraging_class_mul (C : ModelData F ζ hζ)
    (b b' : B F ζ hζ C) :
    averagingClass F ζ hζ C (b * b') =
      averagingClass F ζ hζ C b * averagingClass F ζ hζ C b' := by
  simp only [averagingClass, Subgroup.coe_mul, map_mul]
  rfl

private theorem rawAveraging_translate_integrand (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ)
    (b : B F ζ hζ C) (g : E F ζ hζ) (x : CompactIndex F ζ hζ C) :
    averagingIntegrand F ζ hζ C s h (b.val * g) x =
      (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b : ℂ) *
        averagingIntegrand F ζ hζ C s h g (averagingClass F ζ hζ C b * x) := by
  have he : averagingClass F ζ hζ C (b * s.lift x) =
      averagingClass F ζ hζ C (s.lift (averagingClass F ζ hζ C b * x)) := by
    rw [rawAveraging_class_mul, s.projects, s.projects]
  have hd := weighted_integrand_descends F ζ hζ C h g
    (b * s.lift x) (s.lift (averagingClass F ζ hζ C b * x)) he
  change _ = (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b : ℂ) *
    (averagingIntegrand F ζ hζ C s h g (averagingClass F ζ hζ C b * x))
  unfold averagingIntegrand
  rw [← hd]
  have hc : (s.lift x).val * b.val = b.val * (s.lift x).val :=
    ((KPGlobalProductPolarizationCharacter.B_maximal_abelian F ζ hζ C).1
      (s.lift x).val (s.lift x).property b.val b.property).eq
  simp only [averagingIntegrand, map_mul, Subgroup.coe_mul, mul_inv_rev,
    Units.val_mul, Units.val_inv_eq_inv_val]
  rw [← mul_assoc, hc, mul_assoc]
  have hn : (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem rawAveraging_left_covariant (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ)
    (b : B F ζ hζ C) (g : E F ζ hζ) :
    (∫ x, averagingIntegrand F ζ hζ C s h (b.val * g) x ∂probabilityHaar F ζ hζ C) =
      (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b : ℂ) *
        ∫ x, averagingIntegrand F ζ hζ C s h g x ∂probabilityHaar F ζ hζ C := by
  simp_rw [rawAveraging_translate_integrand F ζ hζ C s h b g]
  rw [integral_const_mul, integral_mul_left_eq_self]

def rawAveraging (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) :
    RationalSmooth F ζ hζ →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (productModel F ζ hζ C) where
  toFun h := ⟨fun g => ∫ x, averagingIntegrand F ζ hζ C s h g x ∂probabilityHaar F ζ hζ C,
    rawAveraging_left_covariant F ζ hζ C s h⟩
  map_add' h k := by
    apply Subtype.ext
    funext g
    change (∫ x, averagingIntegrand F ζ hζ C s (h + k) g x ∂probabilityHaar F ζ hζ C) = _
    have he : averagingIntegrand F ζ hζ C s (h + k) g =
        fun x => averagingIntegrand F ζ hζ C s h g x + averagingIntegrand F ζ hζ C s k g x := by
      funext x
      simp only [averagingIntegrand, Submodule.coe_add, Pi.add_apply, mul_add]
    rw [he, integral_add (averagingIntegrand_integrable F ζ hζ C s h g)
      (averagingIntegrand_integrable F ζ hζ C s k g)]
    rfl
  map_smul' c h := by
    apply Subtype.ext
    funext g
    change (∫ x, averagingIntegrand F ζ hζ C s (c • h) g x ∂probabilityHaar F ζ hζ C) = _
    have he : averagingIntegrand F ζ hζ C s (c • h) g =
        fun x => c * averagingIntegrand F ζ hζ C s h g x := by
      funext x
      simp only [averagingIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, integral_const_mul]
    rfl

private theorem rawAveraging_independent (C : ModelData F ζ hζ)
    (s t : AveragingRepresentatives F ζ hζ C) :
    rawAveraging F ζ hζ C s = rawAveraging F ζ hζ C t := by
  apply LinearMap.ext
  intro h
  apply Subtype.ext
  funext g
  apply integral_congr_ae
  filter_upwards [] with x
  exact averagingIntegrand_independent F ζ hζ C s t h g x

private theorem rawPeriodization_independent (C : ModelData F ζ hζ)
    (s t : PeriodizationRepresentatives F ζ hζ C) :
    rawPeriodization F ζ hζ C s = rawPeriodization F ζ hζ C t := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  apply tsum_congr
  intro x
  exact periodizationTerm_independent F ζ hζ C s t f g x

private theorem smoothPeriodization_independent (C : ModelData F ζ hζ)
    (s t : PeriodizationRepresentatives F ζ hζ C) :
    smoothPeriodization F ζ hζ C s = smoothPeriodization F ζ hζ C t := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [smoothPeriodization_formula, smoothPeriodization_formula]
  exact tsum_congr (periodizationTerm_independent F ζ hζ C s t f g)

private theorem smoothPeriodization_intertwines (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (a : E F ζ hζ) (f : ProductSmooth F ζ hζ C) :
    smoothPeriodization F ζ hζ C s (rightAction F ζ hζ (productModel F ζ hζ C) a f) =
      rightAction F ζ hζ (rationalModel F ζ hζ) a (smoothPeriodization F ζ hζ C s f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [smoothPeriodization_formula, rightAction_formula, smoothPeriodization_formula]
  apply tsum_congr
  intro x
  simp only [periodizationTerm, rightAction_formula, mul_assoc]

private theorem rawAveraging_right_level (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hh : h.val ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ (rationalModel F ζ hζ) U) :
    rawAveraging F ζ hζ C s h ∈ KPGlobalTorusFunctionData.RightLevel
      (productModel F ζ hζ C).H (productModel F ζ hζ C).character.toMonoidHom
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) := by
  intro j
  apply Subtype.ext
  funext g
  change (∫ x, averagingIntegrand F ζ hζ C s h (g * j.val) x ∂probabilityHaar F ζ hζ C) = _
  apply integral_congr_ae
  filter_upwards [] with x
  have he := congrArg (fun k : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (rationalModel F ζ hζ) =>
    k.val ((s.lift x).val * g)) (hh.2 j)
  change h.val.val (((s.lift x).val * g) * j.val) = h.val.val ((s.lift x).val * g) at he
  simp only [averagingIntegrand, ← mul_assoc, he]

def rawUnitaryAveraging (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) :
    RationalUnitary F ζ hζ →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (KPGlobalTorusFiniteStages.productModel F ζ hζ C) :=
  (scalarUntwistProduct F ζ hζ C).toLinearMap.comp
    ((rawAveraging F ζ hζ C s).comp (untwistRational F ζ hζ).symm.toLinearMap)

private theorem rawUnitaryAveraging_formula (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalUnitary F ζ hζ) (g : E F ζ hζ) :
    (rawUnitaryAveraging F ζ hζ C s h).val g =
      ∫ x, (((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment (s.lift x))⁻¹ : ℂˣ) : ℂ) *
        h.val.val ((s.lift x).val * g) ∂probabilityHaar F ζ hζ C := by
  change (scalarUntwistProduct F ζ hζ C
    (rawAveraging F ζ hζ C s ((untwistRational F ζ hζ).symm h))).val g = _
  rw [scalarUntwistProduct_formula]
  change _ * (∫ x, averagingIntegrand F ζ hζ C s ((untwistRational F ζ hζ).symm h) g x
    ∂probabilityHaar F ζ hζ C) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [averagingIntegrand, retwistRational_formula, product_unit_inverse, nu_complex_mul]
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
  field_simp

private theorem rawUnitaryAveraging_right_level (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalUnitary F ζ hζ)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hh : h.val ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) U) :
    rawUnitaryAveraging F ζ hζ C s h ∈ KPGlobalTorusFunctionData.RightLevel
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C).H
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C).character.toMonoidHom
      ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) := by
  intro j
  apply Subtype.ext
  funext g
  change (rawUnitaryAveraging F ζ hζ C s h).val (g * j.val) = _
  rw [rawUnitaryAveraging_formula, rawUnitaryAveraging_formula]
  apply integral_congr_ae
  filter_upwards [] with x
  have he := KPGlobalTorusFunctionData.rightLevel_covariance _ _ _ ⟨h.val, hh.2⟩
    ((s.lift x).val * g) j.val j.property
  rw [← mul_assoc, he]

private theorem rawUnitaryAveraging_phase (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalUnitary F ζ hζ)
    (hh : h.val ∈ KPGlobalTorusFiniteStages.Stage F ζ hζ C L
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ))
    (k : KPGlobalTorusFiniteStages.phaseGroup F ζ hζ C L) (g : E F ζ hζ) :
    (rawUnitaryAveraging F ζ hζ C s h).val (g * k.val) =
      (KPGlobalTorusFiniteStages.phaseCharacter F ζ hζ C L k : ℂ) *
        (rawUnitaryAveraging F ζ hζ C s h).val g := by
  rw [rawUnitaryAveraging_formula, rawUnitaryAveraging_formula, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hall := KPGlobalTorusTensorFibers.scalar_phase_global_covariance
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ).H
    (KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L)
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ).character.toMonoidHom
    h.val hh.1 k.val (KPGlobalTorusFiniteStages.phase_inside_domain F ζ hζ C L k.property)
    (KPGlobalTorusFiniteStages.phaseCharacter F ζ hζ C L k : ℂ)
    (fun y => hh.2 k y) ((s.lift x).val * g)
  rw [← mul_assoc, hall]
  ring

theorem rawUnitaryAveraging_smooth (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalUnitary F ζ hζ) :
    rawUnitaryAveraging F ζ hζ C s h ∈ ProductUnitary F ζ hζ C := by
  obtain ⟨L, hL⟩ := KPGlobalTorusFiniteStages.smooth_vector_in_stage F ζ hζ C
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) (Or.inl rfl) h
  obtain ⟨U, hU⟩ := KPGlobalTorusFiniteStages.stage_in_smooth_level F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) (Or.inl rfl)
  apply Submodule.mem_iSup_of_mem U
  refine ⟨?_, rawUnitaryAveraging_right_level F ζ hζ C s h U (hU hL)⟩
  apply KPGlobalTorusTensorFibers.archSmooth_of_chart_character_one F ζ hζ
  apply KPGlobalTorusFiniteStagesCofinality.normalized_arch_chart_character_one F ζ hζ C C.adjustment
  right
  refine ⟨rfl, ?_⟩
  intro r t he
  have ht : r = t := Subtype.ext he
  subst t
  rfl

def smoothUnitaryAveraging (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) :
    RationalUnitary F ζ hζ →ₗ[ℂ] ProductUnitary F ζ hζ C :=
  (rawUnitaryAveraging F ζ hζ C s).codRestrict _ (rawUnitaryAveraging_smooth F ζ hζ C s)

def smoothAveraging (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) :
    RationalSmooth F ζ hζ →ₗ[ℂ] ProductSmooth F ζ hζ C :=
  (untwistProduct F ζ hζ C).symm.toLinearMap.comp
    ((smoothUnitaryAveraging F ζ hζ C s).comp (untwistRational F ζ hζ).toLinearMap)

theorem smoothAveraging_formula (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ) (g : E F ζ hζ) :
    (smoothAveraging F ζ hζ C s h).val.val g =
      ∫ x, averagingIntegrand F ζ hζ C s h g x ∂probabilityHaar F ζ hζ C := by
  unfold smoothAveraging
  change ((untwistProduct F ζ hζ C).symm
    (smoothUnitaryAveraging F ζ hζ C s (untwistRational F ζ hζ h))).val.val g = _
  rw [retwistProduct_formula]
  change _ * (scalarUntwistProduct F ζ hζ C
    (rawAveraging F ζ hζ C s ((untwistRational F ζ hζ).symm (untwistRational F ζ hζ h)))).val g = _
  rw [ContinuousLinearEquiv.symm_apply_apply, scalarUntwistProduct_formula]
  change _ * (_ * (∫ x, averagingIntegrand F ζ hζ C s h g x ∂probabilityHaar F ζ hζ C)) = _
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

set_option maxHeartbeats 1000000 in
private theorem smoothUnitaryAveraging_continuous (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) :
    Continuous (smoothUnitaryAveraging F ζ hζ C s) := by
  let Q := KPGlobalTorusFiniteStages.productModel F ζ hζ C
  have hq : WithSeminorms (fun q : periodizationUnionJets F ζ hζ Q => q.val) := ⟨rfl⟩
  letI : IsTopologicalAddGroup (ProductUnitary F ζ hζ C) := hq.isTopologicalAddGroup
  letI : ContinuousSMul ℂ (ProductUnitary F ζ hζ C) := hq.continuousSMul
  letI : ContinuousSMul ℝ (ProductUnitary F ζ hζ C) := ⟨by
    have hh := ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd :
      Continuous (fun x : ℝ × ProductUnitary F ζ hζ C => (x.1 : ℂ) • x.2))
    convert hh using 1
    funext x
    exact (IsScalarTower.algebraMap_smul ℂ x.1 x.2).symm⟩
  letI : LocallyConvexSpace ℝ (ProductUnitary F ζ hζ C) :=
    KPGlobalTorusFunctionData.finalLocallyConvexTopology_locallyConvex Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusFunctionData.torusArchDomain_open F)
      (fun U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
        (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)
  refine (KPGlobalTorusFiniteStages.levelwise_final_topology F ζ hζ C
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) (Or.inl rfl)
    (V := ProductUnitary F ζ hζ C) (T := smoothUnitaryAveraging F ζ hζ C s)).mpr ?_
  intro L U hU
  letI := KPGlobalTorusFiniteStages.stageTopology F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) U hU
  have hp := periodization_stage_polynorms F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) U hU
  letI : IsTopologicalAddGroup (KPGlobalTorusFiniteStages.Stage F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ)) := hp.isTopologicalAddGroup
  letI : ContinuousSMul ℂ (KPGlobalTorusFiniteStages.Stage F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ)) := hp.continuousSMul
  letI := periodization_stage_t2 F ζ hζ C L (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) U hU
  letI := KPGlobalTorusFiniteStages.stage_module_finite F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) (Or.inl rfl)
  exact LinearMap.continuous_of_finiteDimensional (𝕜 := ℂ)
    (E := KPGlobalTorusFiniteStages.Stage F ζ hζ C L (KPGlobalTorusFiniteStages.rationalModel F ζ hζ))
    (F' := ProductUnitary F ζ hζ C)
    ((smoothUnitaryAveraging F ζ hζ C s).comp (Submodule.inclusion
      (hU.trans (le_iSup (fun W : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
        KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ
          (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) W) U))))

theorem smoothAveraging_continuous (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) : Continuous (smoothAveraging F ζ hζ C s) := by
  unfold smoothAveraging
  exact (untwistProduct F ζ hζ C).symm.continuous.comp
    ((smoothUnitaryAveraging_continuous F ζ hζ C s).comp (untwistRational F ζ hζ).continuous)

end
end DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse

end
