module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicTorusMapsAndCompactRestriction

@[expose] public section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance smoothTopology6 (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

local instance inducedTop6 (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

local instance compactTop6 (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    TopologicalSpace (CompactLevel F ζ hζ P J K) := compactLevelTopology F ζ hζ P J K

 def upperRoot (x : KPGlobalTorusFunctionData.Adeles F) :
    KPAdelicCoverRestrictedProduct.AdelicGL2 F :=
  Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x
private theorem upperRoot_entries (x : KPGlobalTorusFunctionData.Adeles F) (i j : Fin 2) :
    upperRoot F x i j = (!![1, x; 0, 1]) i j := by
  fin_cases i <;> fin_cases j <;> simp [upperRoot, Matrix.transvection]
private theorem adele_ext (a b : KPGlobalTorusFunctionData.Adeles F)
    (h : ∀ v, KPAdelicCoverRestrictedProduct.adeleEval F v a = KPAdelicCoverRestrictedProduct.adeleEval F v b) : a = b := by
  apply Prod.ext
  · funext w
    exact h (Sum.inl w)
  · apply Subtype.ext
    funext q
    exact h (Sum.inr q)
private theorem projected_root (x : KPGlobalTorusFunctionData.Adeles F) :
    KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (KPGlobalTorusFunctionData.N F ζ hζ x) =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) (upperRoot F x) := by
  change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ x)) = _
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply adele_ext F
  intro v
  have h := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ x) v
  have he := congrArg (fun A : KPLocalCover.LocalGL2 F v => A i j) h
  change KPAdelicCoverRestrictedProduct.adeleEval F v
    ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalTorusFunctionData.rootTuple F ζ hζ x)) i j) = _ at he
  rw [he]
  fin_cases i <;> fin_cases j <;>
    simp [KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N,
      KPLocalCover.projection_apply, KPLocalCover.sectionMap, KubotaRankTwo.n,
      upperRoot_entries]
private theorem upper_unit {R : Type*} [CommRing R] (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0) :
    IsUnit (A 0 0) := by
  have h : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) R)) :=
    (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := R) A).isUnit
  have hd : Matrix.det (A : Matrix (Fin 2) (Fin 2) R) = A 0 0 * A 1 1 := by
    simp only [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  exact isUnit_of_mul_isUnit_left (hd ▸ h)
private theorem upper_diagonal {R : Type*} [CommRing R]
    (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0)
    (x : R) (hx : A 0 0 * x = A 0 1) :
    ((A * Matrix.GeneralLinearGroup.transvection (R := R) 0 1 (by decide) (-x) : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
    ((A * Matrix.GeneralLinearGroup.transvection (R := R) 0 1 (by decide) (-x) : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by
  constructor <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, h10, hx]

theorem iwasawaUpperUnits (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) : IsUnit (A 0 0) ∧ IsUnit (A 1 1) := by
  have h : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) (KPGlobalTorusFunctionData.Adeles F))) := (Matrix.GeneralLinearGroup.det A).isUnit
  have hd : Matrix.det (A : Matrix (Fin 2) (Fin 2) (KPGlobalTorusFunctionData.Adeles F)) = A 0 0 * A 1 1 := by simp [Matrix.det_fin_two, h10]
  exact ⟨isUnit_of_mul_isUnit_left (hd ▸ h), isUnit_of_mul_isUnit_right (hd ▸ h)⟩
def iwasawaUpperRatio (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) : KPGlobalTorusFunctionData.Ideles F :=
  (iwasawaUpperUnits F A h10).1.unit * (iwasawaUpperUnits F A h10).2.unit⁻¹
theorem iwasawaUpperRatio_scalar (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : A 1 0 = 0) (hB : B 1 0 = 0)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) : iwasawaUpperRatio F A hA = iwasawaUpperRatio F B hB := by
  obtain ⟨C, hC, he⟩ := (QuotientGroup.mk'_eq_mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).mp he
  obtain ⟨c, rfl⟩ := hC
  have he00 := congrArg (fun M : KPAdelicCoverRestrictedProduct.AdelicGL2 F => M 0 0) he
  have he11 := congrArg (fun M : KPAdelicCoverRestrictedProduct.AdelicGL2 F => M 1 1) he
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at he00 he11
  have hu00 : (iwasawaUpperUnits F A hA).1.unit * c = (iwasawaUpperUnits F B hB).1.unit := by
    apply Units.ext
    simpa only [Units.val_mul, IsUnit.unit_spec] using he00
  have hu11 : (iwasawaUpperUnits F A hA).2.unit * c = (iwasawaUpperUnits F B hB).2.unit := by
    apply Units.ext
    simpa only [Units.val_mul, IsUnit.unit_spec] using he11
  unfold iwasawaUpperRatio
  rw [← hu00, ← hu11]
  group
theorem iwasawaUpperMul_zero (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (hA : A 1 0 = 0) (hB : B 1 0 = 0) : (A * B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB]
theorem iwasawaUpperRatio_mul (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (hA : A 1 0 = 0) (hB : B 1 0 = 0) : iwasawaUpperRatio F (A * B) (iwasawaUpperMul_zero F A B hA hB) = iwasawaUpperRatio F A hA * iwasawaUpperRatio F B hB := by
  have hu00 : (iwasawaUpperUnits F (A * B) (iwasawaUpperMul_zero F A B hA hB)).1.unit = (iwasawaUpperUnits F A hA).1.unit * (iwasawaUpperUnits F B hB).1.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hB]
  have hu11 : (iwasawaUpperUnits F (A * B) (iwasawaUpperMul_zero F A B hA hB)).2.unit = (iwasawaUpperUnits F A hA).2.unit * (iwasawaUpperUnits F B hB).2.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA]
  unfold iwasawaUpperRatio
  rw [hu00, hu11]
  simp only [mul_inv_rev]
  ac_rfl

private theorem upperRoot_zero (x : KPGlobalTorusFunctionData.Adeles F) :
    upperRoot F x 1 0 = 0 := by simp [upperRoot_entries]

private theorem upperRoot_ratio (x : KPGlobalTorusFunctionData.Adeles F) :
    iwasawaUpperRatio F (upperRoot F x) (upperRoot_zero F x) = 1 := by
  have h00 : (iwasawaUpperUnits F (upperRoot F x) (upperRoot_zero F x)).1.unit = 1 := by
    apply Units.ext
    simp [IsUnit.unit_spec, upperRoot_entries]
  have h11 : (iwasawaUpperUnits F (upperRoot F x) (upperRoot_zero F x)).2.unit = 1 := by
    apply Units.ext
    simp [IsUnit.unit_spec, upperRoot_entries]
  simp [iwasawaUpperRatio, h00, h11]

theorem iwasawaUpperRatio_torus (t : E F ζ hζ)
    (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val) :
    iwasawaUpperRatio F A h10 = KPGlobalTorusFunctionData.p F ζ hζ t := by
  apply Units.ext
  change _ = (KPGlobalTorusFunctionData.torusRatio F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ : KPGlobalTorusFunctionData.Adeles F)
  rw [KPGlobalTorusFunctionData.ratio_formula F _ A hA h10 h01]
  rfl

theorem iwasawaUpperRatio_torus_root (t : E F ζ hζ)
    (x : KPGlobalTorusFunctionData.Adeles F)
    (B : KPAdelicCoverRestrictedProduct.AdelicGL2 F) (hB : B 1 0 = 0)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x)) :
    iwasawaUpperRatio F B hB = KPGlobalTorusFunctionData.p F ζ hζ t := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  have hrep : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (A * upperRoot F x) = QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B := by
    rw [map_mul, hA, ← projected_root F ζ hζ x, ← map_mul, ← he]
  rw [← iwasawaUpperRatio_scalar F (A * upperRoot F x) B
    (iwasawaUpperMul_zero F A (upperRoot F x) h10 (upperRoot_zero F x)) hB hrep,
    iwasawaUpperRatio_mul F A (upperRoot F x) h10 (upperRoot_zero F x),
    upperRoot_ratio, mul_one]
  exact iwasawaUpperRatio_torus F ζ hζ t A h10 h01 hA

 theorem actual_borel_factorization (b : KPGlobalTorusFunctionData.borel F ζ hζ) :
    ∃ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F),
      b.val = t.val * KPGlobalTorusFunctionData.N F ζ hζ x := by
  obtain ⟨A, hA, h10⟩ := b.property
  let u := (upper_unit A h10).unit
  let x : KPGlobalTorusFunctionData.Adeles F := ↑u⁻¹ * A 0 1
  have hx : A 0 0 * x = A 0 1 := by
    change A 0 0 * (↑u⁻¹ * A 0 1) = _
    have hu : (u : KPGlobalTorusFunctionData.Adeles F) = A 0 0 := (upper_unit A h10).unit_spec
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have ht : b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x) ∈ E F ζ hζ := by
    change ∃ D : KPAdelicCoverRestrictedProduct.AdelicGL2 F,
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) D =
        KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
          (b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x)) ∧ D 1 0 = 0 ∧ D 0 1 = 0
    refine ⟨A * upperRoot F (-x), ?_, upper_diagonal A h10 x hx⟩
    simp only [map_mul, projected_root, hA]
  refine ⟨⟨b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x), ht⟩, x, ?_⟩
  have hn : KPGlobalTorusFunctionData.N F ζ hζ (-x) * KPGlobalTorusFunctionData.N F ζ hζ x = 1 := by
    rw [← KPGlobalTorusFunctionData.N_add, neg_add_cancel]
    exact (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  change b.val = (b.val * KPGlobalTorusFunctionData.N F ζ hζ (-x)) * KPGlobalTorusFunctionData.N F ζ hζ x
  rw [mul_assoc, hn, mul_one]

 theorem upper_units {R : Type*} [CommRing R]
    (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0) :
    IsUnit (A 0 0) ∧ IsUnit (A 1 1) := by
  have h : IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) R)) :=
    (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := R) A).isUnit
  have hd : Matrix.det (A : Matrix (Fin 2) (Fin 2) R) = A 0 0 * A 1 1 := by
    simp only [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  exact ⟨isUnit_of_mul_isUnit_left (hd ▸ h), isUnit_of_mul_isUnit_right (hd ▸ h)⟩
 def ratio {R : Type*} [CommRing R]
    (A : Matrix.GeneralLinearGroup (Fin 2) R) (h10 : A 1 0 = 0) : Rˣ :=
  (upper_units A h10).1.unit * ((upper_units A h10).2.unit)⁻¹
private theorem upper_product {R : Type*} [CommRing R]
    (A B : Matrix.GeneralLinearGroup (Fin 2) R) (hA : A 1 0 = 0) (hB : B 1 0 = 0) :
    ((A * B : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB]
private theorem ratio_mul {R : Type*} [CommRing R]
    (A B : Matrix.GeneralLinearGroup (Fin 2) R) (hA : A 1 0 = 0) (hB : B 1 0 = 0) :
    ratio (A * B) (upper_product A B hA hB) = ratio A hA * ratio B hB := by
  have h0 : (upper_units (A * B) (upper_product A B hA hB)).1.unit =
      (upper_units A hA).1.unit * (upper_units B hB).1.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hB]
  have h1 : (upper_units (A * B) (upper_product A B hA hB)).2.unit =
      (upper_units A hA).2.unit * (upper_units B hB).2.unit := by
    apply Units.ext
    simp [IsUnit.unit_spec, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA]
  simp only [ratio, h0, h1]
  simp only [mul_inv_rev]; ac_rfl
private theorem ratio_eq (A B : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : A 1 0 = 0) (hB : B 1 0 = 0)
    (h : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) :
    ratio A hA = ratio B hB := by
  have hm := QuotientGroup.eq.mp h
  obtain ⟨z, hz⟩ := hm
  have he : B = A * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) z = A⁻¹ * B at hz
    rw [hz]
    group
  have h0 : (upper_units B hB).1.unit = (upper_units A hA).1.unit * z := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    rw [he]
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar]
  have h1 : (upper_units B hB).2.unit = (upper_units A hA).2.unit * z := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    rw [he]
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar]
  simp only [ratio, h0, h1]
  simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

private theorem root_upper (x : KPGlobalTorusFunctionData.Adeles F) :
    upperRoot F x 1 0 = 0 := by rw [upperRoot_entries]; rfl

 def borelRatio (b : KPGlobalTorusFunctionData.borel F ζ hζ) : KPGlobalTorusFunctionData.Ideles F :=
  ratio (Classical.choose b.property) (Classical.choose_spec b.property).2

private theorem borelRatio_formula (b : KPGlobalTorusFunctionData.borel F ζ hζ)
    (A : KPAdelicCoverRestrictedProduct.AdelicGL2 F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ b.val) (h10 : A 1 0 = 0) :
    borelRatio F ζ hζ b = ratio A h10 := by
  apply ratio_eq F
  exact (Classical.choose_spec b.property).1.trans hA.symm

 theorem borelRatio_mul (b c : KPGlobalTorusFunctionData.borel F ζ hζ) :
    borelRatio F ζ hζ (b * c) = borelRatio F ζ hζ b * borelRatio F ζ hζ c := by
  let A := Classical.choose b.property
  let B := Classical.choose c.property
  have hA := Classical.choose_spec b.property
  have hB := Classical.choose_spec c.property
  rw [borelRatio_formula F ζ hζ (b * c) (A * B) (by
    change _ = KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (b.val * c.val)
    exact (map_mul _ A B).trans ((congrArg₂ (fun a b => a * b) hA.1 hB.1).trans (map_mul _ b.val c.val).symm)) (upper_product A B hA.2 hB.2)]
  exact ratio_mul A B hA.2 hB.2

 theorem borel_torus (t : E F ζ hζ) : t.val ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  exact ⟨A, hA, h10⟩

 theorem borel_root (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ x ∈ KPGlobalTorusFunctionData.borel F ζ hζ :=
  ⟨upperRoot F x, (projected_root F ζ hζ x).symm, root_upper F x⟩

 def borelElement (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.borel F ζ hζ :=
  ⟨t.val * KPGlobalTorusFunctionData.N F ζ hζ x,
    Subgroup.mul_mem _ (borel_torus F ζ hζ t) (borel_root F ζ hζ x)⟩

 theorem borelRatio_torus (t : E F ζ hζ) :
    borelRatio F ζ hζ ⟨t.val, borel_torus F ζ hζ t⟩ = KPGlobalTorusFunctionData.p F ζ hζ t := by
  let A := Classical.choose t.property
  have hA := Classical.choose_spec t.property
  rw [borelRatio_formula F ζ hζ _ A hA.1 hA.2.1]
  apply Units.ext
  have hh := KPGlobalTorusFunctionData.ratio_formula F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ A hA.1 hA.2.1 hA.2.2
  change (ratio A hA.2.1 : KPGlobalTorusFunctionData.Adeles F) =
    ((KPGlobalTorusFunctionData.torusRatio F)
      ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩ : KPGlobalTorusFunctionData.Adeles F)
  rw [hh]
  unfold ratio
  simp only [Units.val_mul]

private theorem borelRatio_root (x : KPGlobalTorusFunctionData.Adeles F) :
    borelRatio F ζ hζ ⟨KPGlobalTorusFunctionData.N F ζ hζ x, borel_root F ζ hζ x⟩ = 1 := by
  rw [borelRatio_formula F ζ hζ _ (upperRoot F x) (projected_root F ζ hζ x).symm (root_upper F x)]
  have h0 : (upper_units (upperRoot F x) (root_upper F x)).1.unit = 1 := by
    apply Units.ext
    simp only [IsUnit.unit_spec, upperRoot_entries, Units.val_one]
    rfl
  have h1 : (upper_units (upperRoot F x) (root_upper F x)).2.unit = 1 := by
    apply Units.ext
    simp only [IsUnit.unit_spec, upperRoot_entries, Units.val_one]
    rfl
  simp only [ratio, h0, h1, inv_one, mul_one]

private theorem borelRatio_element (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    borelRatio F ζ hζ (borelElement F ζ hζ t x) = KPGlobalTorusFunctionData.p F ζ hζ t := by
  change borelRatio F ζ hζ (⟨t.val, borel_torus F ζ hζ t⟩ *
    ⟨KPGlobalTorusFunctionData.N F ζ hζ x, borel_root F ζ hζ x⟩) = _
  rw [borelRatio_mul, borelRatio_torus, borelRatio_root, mul_one]

 def borelRatioHom : KPGlobalTorusFunctionData.borel F ζ hζ →* KPGlobalTorusFunctionData.Ideles F where
  toFun := borelRatio F ζ hζ
  map_one' := by
    have h := borelRatio_torus F ζ hζ 1
    have he : (⟨(1 : E F ζ hζ).val, borel_torus F ζ hζ 1⟩ : KPGlobalTorusFunctionData.borel F ζ hζ) = 1 := Subtype.ext rfl
    rw [he, map_one] at h
    exact h
  map_mul' := borelRatio_mul F ζ hζ

 def borelDelta : KPGlobalTorusFunctionData.borel F ζ hζ →* (ℝ≥0)ˣ :=
  (KPGlobalTorusFunctionData.ideleAbs F).comp (borelRatioHom F ζ hζ)

private theorem borelDelta_element (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) :
    borelDelta F ζ hζ (borelElement F ζ hζ t x) = KPGlobalTorusFunctionData.delta F ζ hζ t := by
  change KPGlobalTorusFunctionData.ideleAbs F (borelRatio F ζ hζ (borelElement F ζ hζ t x)) = _
  rw [borelRatio_element]
  rfl

structure IwasawaData where
  K : Subgroup (G F ζ hζ)
  compact : IsCompact (K : Set (G F ζ hζ))
  decomposition : ∀ g : G F ζ hζ,
    ∃ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (k : K),
      g = (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val
  overlap : ∀ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F),
    t.val * KPGlobalTorusFunctionData.N F ζ hζ x ∈ K →
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1

def iwasawaNorm (D : IwasawaData F ζ hζ) (g : G F ζ hζ) : (ℝ≥0)ˣ :=
  KPGlobalTorusFunctionData.delta F ζ hζ (Classical.choose (D.decomposition g))

 theorem iwasawaNorm_formula (D : IwasawaData F ζ hζ)
    (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (k : D.K) :
    iwasawaNorm F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val) =
      KPGlobalTorusFunctionData.delta F ζ hζ t := by
  let g := (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val
  let u := Classical.choose (D.decomposition g)
  let y := Classical.choose (Classical.choose_spec (D.decomposition g))
  let l := Classical.choose (Classical.choose_spec (Classical.choose_spec (D.decomposition g)))
  have hl : g = (u.val * KPGlobalTorusFunctionData.N F ζ hζ y) * l.val :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (D.decomposition g)))
  let b := borelElement F ζ hζ u y
  let c := borelElement F ζ hζ t x
  have he : (b⁻¹ * c).val = l.val * k.val⁻¹ := by
    have h : c.val * k.val = b.val * l.val := hl
    change b.val⁻¹ * c.val = _
    calc
      b.val⁻¹ * c.val = b.val⁻¹ * ((c.val * k.val) * k.val⁻¹) := by group
      _ = b.val⁻¹ * ((b.val * l.val) * k.val⁻¹) := by rw [h]
      _ = l.val * k.val⁻¹ := by group
  obtain ⟨v, z, hv⟩ := actual_borel_factorization F ζ hζ (b⁻¹ * c)
  have hK : v.val * KPGlobalTorusFunctionData.N F ζ hζ z ∈ D.K := by
    rw [← hv, he]
    exact D.K.mul_mem l.property (D.K.inv_mem k.property)
  have hd : borelDelta F ζ hζ (b⁻¹ * c) = 1 := by
    have hb : b⁻¹ * c = borelElement F ζ hζ v z := Subtype.ext hv
    rw [hb, borelDelta_element]
    exact D.overlap v z hK
  rw [map_mul, map_inv] at hd
  have hb := borelDelta_element F ζ hζ u y
  have hc := borelDelta_element F ζ hζ t x
  change (borelDelta F ζ hζ b)⁻¹ * borelDelta F ζ hζ c = 1 at hd
  rw [hb, hc] at hd
  change KPGlobalTorusFunctionData.delta F ζ hζ u = KPGlobalTorusFunctionData.delta F ζ hζ t
  exact inv_mul_eq_one.mp hd

theorem iwasawaNorm_right_compact (D : IwasawaData F ζ hζ)
    (g : G F ζ hζ) (k : D.K) :
    iwasawaNorm F ζ hζ D (g * k.val) = iwasawaNorm F ζ hζ D g := by
  obtain ⟨t, x, l, rfl⟩ := D.decomposition g
  have he : ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * l.val) * k.val =
      (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * (l * k).val := by
    simp [mul_assoc]
  rw [he, iwasawaNorm_formula, iwasawaNorm_formula]

theorem iwasawaNorm_borel_mul (D : IwasawaData F ζ hζ)
    (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    iwasawaNorm F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.delta F ζ hζ t * iwasawaNorm F ζ hζ D g := by
  obtain ⟨u, y, k, rfl⟩ := D.decomposition g
  let b := borelElement F ζ hζ t x * borelElement F ζ hζ u y
  obtain ⟨v, z, hv⟩ := actual_borel_factorization F ζ hζ b
  have hd : KPGlobalTorusFunctionData.delta F ζ hζ v =
      KPGlobalTorusFunctionData.delta F ζ hζ t * KPGlobalTorusFunctionData.delta F ζ hζ u := by
    have hb : b = borelElement F ζ hζ v z := Subtype.ext hv
    have hm := (borelDelta F ζ hζ).map_mul (borelElement F ζ hζ t x) (borelElement F ζ hζ u y)
    change borelDelta F ζ hζ b = _ at hm
    rw [hb, borelDelta_element, borelDelta_element, borelDelta_element] at hm
    exact hm
  have he : (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) *
      ((u.val * KPGlobalTorusFunctionData.N F ζ hζ y) * k.val) =
      (v.val * KPGlobalTorusFunctionData.N F ζ hζ z) * k.val := by
    rw [← hv]
    change _ = ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) *
      (u.val * KPGlobalTorusFunctionData.N F ζ hζ y)) * k.val
    exact (mul_assoc _ _ _).symm
  rw [he, iwasawaNorm_formula, iwasawaNorm_formula, hd]

theorem iwasawaNorm_compact (D : IwasawaData F ζ hζ) (k : D.K) :
    iwasawaNorm F ζ hζ D k.val = 1 := by
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have h := iwasawaNorm_formula F ζ hζ D 1 0 k
  simpa [hn] using h

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport

section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def iwasawaWeight (D : IwasawaData F ζ hζ) (s : ℂ) (g : G F ζ hζ) : ℂ :=
  Complex.exp (s * (Real.log (((iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) : ℂ))

 theorem iwasawaNorm_pos (D : IwasawaData F ζ hζ) (g : G F ζ hζ) :
    0 < (((iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) := by
  exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero (iwasawaNorm F ζ hζ D g))

theorem iwasawaWeight_borel_mul (D : IwasawaData F ζ hζ) (s : ℂ)
    (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    iwasawaWeight F ζ hζ D s ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      normPower F ζ hζ s t * iwasawaWeight F ζ hζ D s g := by
  have ht : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)) := by
    exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t))
  simp only [iwasawaWeight, normPower, iwasawaNorm_borel_mul, Units.val_mul,
    NNReal.coe_mul, Real.log_mul (ne_of_gt ht) (ne_of_gt (iwasawaNorm_pos F ζ hζ D g)),
    Complex.ofReal_add, mul_add, Complex.exp_add]

theorem iwasawaWeight_right_compact (D : IwasawaData F ζ hζ) (s : ℂ)
    (g : G F ζ hζ) (k : D.K) :
    iwasawaWeight F ζ hζ D s (g * k.val) = iwasawaWeight F ζ hζ D s g := by
  simp only [iwasawaWeight, iwasawaNorm_right_compact]

@[simp] theorem iwasawaWeight_compact (D : IwasawaData F ζ hζ) (s : ℂ) (k : D.K) :
    iwasawaWeight F ζ hζ D s k.val = 1 := by
  simp [iwasawaWeight, iwasawaNorm_compact]

@[simp] theorem iwasawaWeight_cancel (D : IwasawaData F ζ hζ) (s : ℂ) (g : G F ζ hζ) :
    iwasawaWeight F ζ hζ D s g * iwasawaWeight F ζ hζ D (-s) g = 1 := by
  simp only [iwasawaWeight, neg_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

section IwasawaLowerWeightPorts
open scoped Matrix.Norms.Elementwise ContDiff
private abbrev IwasawaLocalGL := Matrix.GeneralLinearGroup (Fin 2) ℂ
private def iwasawa_inverseHalfWeight (g : IwasawaLocalGL) : ℝ :=
  (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) / ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖

private theorem iwasawa_inverseHalfWeight_pos (g : IwasawaLocalGL) : 0 < iwasawa_inverseHalfWeight g := by
  have hd := Matrix.GeneralLinearGroup.det_ne_zero g
  have hh : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
    by_contra! hh
    exact hd (by simp [Matrix.det_fin_two, hh.1, hh.2])
  unfold iwasawa_inverseHalfWeight
  rcases hh with hh | hh <;> positivity

private def iwasawa_matrixInverseHalfWeight (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) / ‖g.det‖

private theorem iwasawa_matrixInverseHalfWeight_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) iwasawa_matrixInverseHalfWeight {g | g.det ≠ 0} := by
  have hentry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun g : Matrix (Fin 2) (Fin 2) ℂ => g i j) :=
    (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)
  have hdet : ContDiff ℝ (⊤ : ℕ∞)
      (fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det) := by
    simp only [Matrix.det_fin_two]
    exact ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
  exact (((hentry 1 0).norm_sq (𝕜 := ℂ) |>.add ((hentry 1 1).norm_sq (𝕜 := ℂ))).contDiffOn).div
    (hdet.contDiffOn.norm ℂ (fun g hg => hg)) (fun g hg => norm_ne_zero_iff.mpr hg)

private theorem iwasawa_inverseHalfWeight_covariance
    (a d : ℂˣ) (b : ℂ) (g : IwasawaLocalGL) :
    let u : IwasawaLocalGL := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(a : ℂ), b; 0, (d : ℂ)] (by simp [Matrix.det_fin_two])
    iwasawa_inverseHalfWeight (u * g) = (‖(a : ℂ) / (d : ℂ)‖)⁻¹ * iwasawa_inverseHalfWeight g := by
  dsimp only
  let u : IwasawaLocalGL := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(a : ℂ), b; 0, (d : ℂ)] (by simp [Matrix.det_fin_two])
  have hu : ((Matrix.GeneralLinearGroup.det u : ℂˣ) : ℂ) = (a : ℂ) * (d : ℂ) := by
    simp [u, Matrix.det_fin_two]
  change iwasawa_inverseHalfWeight (u * g) = _
  unfold iwasawa_inverseHalfWeight
  simp only [map_mul, Units.val_mul]
  rw [hu, norm_mul, norm_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have h0 : (u : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := rfl
  have h1 : (u : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (d : ℂ) := rfl
  simp only [h0, h1, zero_mul, zero_add, norm_mul, mul_pow, norm_div]
  field_simp

private theorem iwasawa_inverseHalfWeight_scalar (c : ℂˣ) (g : IwasawaLocalGL) :
    iwasawa_inverseHalfWeight (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) =
      iwasawa_inverseHalfWeight g := by
  have he : Matrix.GeneralLinearGroup.scalar (Fin 2) c =
      Matrix.GeneralLinearGroup.mkOfDetNeZero !![(c : ℂ), 0; 0, (c : ℂ)]
        (by simp [Matrix.det_fin_two]) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar]
  rw [he, iwasawa_inverseHalfWeight_covariance]
  simp

 theorem iwasawa_compact_subtype (D : IwasawaData F ζ hζ) : CompactSpace D.K := by
  exact isCompact_iff_compactSpace.mp D.compact

 theorem iwasawa_compactAverage_normalization
    (D : IwasawaData F ζ hζ) (r : ℝ)
    (v : G F ζ hζ → ℝ) (hv : Continuous v)
    (hp : ∀ g, 0 < v g)
    (hc : ∀ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F)
      (g : G F ζ hζ),
      v ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)).rpow r * v g) :
    letI : IsTopologicalGroup (G F ζ hζ) :=
      (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
    letI : CompactSpace D.K := iwasawa_compact_subtype F ζ hζ D
    letI : MeasurableSpace D.K := borel D.K
    letI : BorelSpace D.K := ⟨rfl⟩
    let μ : Measure D.K := Measure.haar
    (0 < ∫ k : D.K, v k.val ∂μ) ∧
    ∀ g, (∫ k : D.K, v (g * k.val) ∂μ) =
      (((iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)).rpow r * (∫ k : D.K, v k.val ∂μ) := by
  dsimp only
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : CompactSpace D.K := iwasawa_compact_subtype F ζ hζ D
  letI : MeasurableSpace D.K := borel D.K
  letI : BorelSpace D.K := ⟨rfl⟩
  let μ : Measure D.K := Measure.haar
  constructor
  · apply (integral_pos_iff_support_of_nonneg (μ := μ) (fun k : D.K => (hp k.val).le)
      ((hv.comp continuous_subtype_val).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).mpr
    have he : Function.support (fun k : D.K => v k.val) = Set.univ := by
      ext k
      simp [Function.mem_support, ne_of_gt (hp k.val)]
    rw [he]
    exact isOpen_univ.measure_pos μ Set.univ_nonempty
  · intro g
    obtain ⟨t, x, k, rfl⟩ := D.decomposition g
    have heq : (fun l : D.K => v (((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val) * l.val)) =
        (fun l : D.K => (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)).rpow r * v (k.val * l.val)) := by
      funext l
      rw [mul_assoc, hc]
    rw [heq, integral_const_mul, iwasawaNorm_formula]
    congr 1
    have he : (fun l : D.K => v (k.val * l.val)) =
        (fun l : D.K => v (k * l).val) := rfl
    rw [he]
    exact integral_mul_left_eq_self (fun l : D.K => v l.val) k

end IwasawaLowerWeightPorts
end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport

end
