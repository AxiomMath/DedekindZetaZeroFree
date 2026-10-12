module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries
public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPGlobalTorusFunctionData (AdelicMatrixGroup Ideles ordinaryBorel torusRatio)
open scoped Matrix NNReal

 def upperRatio (A : AdelicMatrixGroup F) (h : A 1 0 = 0) : Ideles F :=
  (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit *
    ((KPGlobalTorusMatrixCertificates.diagonal_units A h).2.unit)⁻¹

 lemma upperRatio_mul (A B : AdelicMatrixGroup F) (h : A 1 0 = 0)
    (k : B 1 0 = 0) (hk : (A * B) 1 0 = 0) :
    upperRatio F (A * B) hk = upperRatio F A h * upperRatio F B k := by
  have h0 : (KPGlobalTorusMatrixCertificates.diagonal_units (A * B) hk).1.unit =
      (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit *
      (KPGlobalTorusMatrixCertificates.diagonal_units B k).1.unit := by
    apply Units.ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, k]
  have h1 : (KPGlobalTorusMatrixCertificates.diagonal_units (A * B) hk).2.unit =
      (KPGlobalTorusMatrixCertificates.diagonal_units A h).2.unit *
      (KPGlobalTorusMatrixCertificates.diagonal_units B k).2.unit := by
    apply Units.ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, h]
  unfold upperRatio
  rw [h0, h1]
  simp only [mul_inv_rev]
  ac_rfl

 lemma upperRatio_same (A B : AdelicMatrixGroup F) (h : A 1 0 = 0)
    (k : B 1 0 = 0)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) :
    upperRatio F A h = upperRatio F B k := by
  obtain ⟨s, hs, rfl⟩ := (QuotientGroup.mk'_eq_mk' _).mp he
  obtain ⟨u, rfl⟩ := hs
  have h0 : (KPGlobalTorusMatrixCertificates.diagonal_units
      (A * Matrix.GeneralLinearGroup.scalar (Fin 2) u) k).1.unit =
      (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit * u := by
    apply Units.ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal]
  have h1 : (KPGlobalTorusMatrixCertificates.diagonal_units
      (A * Matrix.GeneralLinearGroup.scalar (Fin 2) u) k).2.unit =
      (KPGlobalTorusMatrixCertificates.diagonal_units A h).2.unit * u := by
    apply Units.ext
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal]
  unfold upperRatio
  rw [h0, h1]
  simp [mul_inv_rev, mul_assoc]

 def borelRatio : ordinaryBorel F →* Ideles F where
  toFun b := upperRatio F (Classical.choose b.property)
    (Classical.choose_spec b.property).2
  map_one' := by
    let A := Classical.choose (1 : ordinaryBorel F).property
    have h := Classical.choose_spec (1 : ordinaryBorel F).property
    change upperRatio F A h.2 = 1
    have he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
        QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) 1 := by
      exact h.1.trans (map_one _).symm
    rw [upperRatio_same F A 1 h.2 (by simp) he]
    apply Units.ext
    simp [upperRatio]
  map_mul' := by
    intro t u
    let A := Classical.choose t.property
    let B := Classical.choose u.property
    let C := Classical.choose (t * u).property
    have hA := Classical.choose_spec t.property
    have hB := Classical.choose_spec u.property
    have hC := Classical.choose_spec (t * u).property
    change upperRatio F C hC.2 = upperRatio F A hA.2 * upperRatio F B hB.2
    have h10 : (A * B) 1 0 = 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, show A 1 0 = 0 from hA.2,
        show B 1 0 = 0 from hB.2]
    have he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) C =
        QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) (A * B) := by
      rw [map_mul, hA.1, hB.1]; exact hC.1
    rw [upperRatio_same F C (A * B) hC.2 h10 he]
    exact upperRatio_mul F A B hA.2 hB.2 h10

private lemma borelRatio_formula (b : ordinaryBorel F) (A : AdelicMatrixGroup F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = b.val)
    (h10 : A 1 0 = 0) : borelRatio F b = upperRatio F A h10 := by
  exact upperRatio_same F _ A (Classical.choose_spec b.property).2 h10
    ((Classical.choose_spec b.property).1.trans hA.symm)

private lemma preimage_upper (A : AdelicMatrixGroup F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A ∈
      ordinaryBorel F) : A 1 0 = 0 := by
  obtain ⟨B, hB, h10⟩ := hA
  rw [QuotientGroup.mk'_eq_mk'] at hB
  obtain ⟨z, hz, he⟩ := hB
  obtain ⟨u, rfl⟩ := hz
  rw [← he]
  simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h10]

private lemma ordinaryBorel_closed : IsClosed (ordinaryBorel F :
    Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F)) := by
  apply (QuotientGroup.isQuotientMap_mk (N := KPAdelicCoverRestrictedProduct.scalarSubgroup F)).isClosed_preimage.mp
  have he : (QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)) ⁻¹'
      (ordinaryBorel F : Set _) = {A : AdelicMatrixGroup F | A 1 0 = 0} := by
    ext A
    exact ⟨preimage_upper F A, fun h => ⟨A, rfl, h⟩⟩
  change IsClosed ((QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)) ⁻¹'
    (ordinaryBorel F : Set _))
  rw [he]
  exact isClosed_eq ((continuous_apply 0).comp ((continuous_apply 1).comp
    (Units.continuous_val : Continuous (fun A : AdelicMatrixGroup F => A.val)))) continuous_const

private lemma upper_inverse00 (A : AdelicMatrixGroup F) (h10 : A 1 0 = 0) :
    (KPGlobalTorusMatrixCertificates.diagonal_units A h10).1.unit⁻¹.val = A⁻¹ 0 0 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) (KPGlobalTorusFunctionData.Adeles F) => B 0 0) A.inv_mul
  have hi := KPGlobalTorusMatrixCertificates.inv10 A h10
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h10, mul_zero, add_zero,
    if_pos rfl] at h
  change A⁻¹ 0 0 * A 0 0 = 1 at h
  let u := (KPGlobalTorusMatrixCertificates.diagonal_units A h10).1.unit
  have hu : (u : KPGlobalTorusFunctionData.Adeles F) = A 0 0 := IsUnit.unit_spec _
  calc
    _ = (u⁻¹ : Ideles F).val * 1 := (mul_one _).symm
    _ = (u⁻¹ : Ideles F).val * (A⁻¹ 0 0 * A 0 0) := by rw [h]
    _ = A⁻¹ 0 0 := by rw [← hu]; simp [← mul_assoc, mul_comm]

private lemma upper_inverse11 (A : AdelicMatrixGroup F) (h10 : A 1 0 = 0) :
    (KPGlobalTorusMatrixCertificates.diagonal_units A h10).2.unit⁻¹.val = A⁻¹ 1 1 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) (KPGlobalTorusFunctionData.Adeles F) => B 1 1) A.mul_inv
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h10, zero_mul, zero_add,
    if_pos rfl] at h
  change A 1 1 * A⁻¹ 1 1 = 1 at h
  let u := (KPGlobalTorusMatrixCertificates.diagonal_units A h10).2.unit
  have hu : (u : KPGlobalTorusFunctionData.Adeles F) = A 1 1 := IsUnit.unit_spec _
  calc
    _ = (u⁻¹ : Ideles F).val * 1 := (mul_one _).symm
    _ = (u⁻¹ : Ideles F).val * (A 1 1 * A⁻¹ 1 1) := by rw [h]
    _ = A⁻¹ 1 1 := by rw [← hu]; simp [← mul_assoc]

private lemma borelRatio_continuous : Continuous (borelRatio F) := by
  let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  let S := (ordinaryBorel F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F))
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
  let u (A : q ⁻¹' S) := (KPGlobalTorusMatrixCertificates.diagonal_units A.val
    (preimage_upper F A.val A.property)).1.unit
  let w (A : q ⁻¹' S) := (KPGlobalTorusMatrixCertificates.diagonal_units A.val
    (preimage_upper F A.val A.property)).2.unit
  have hu : Continuous u := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : q ⁻¹' S => (u A).val)
      have he : (fun A : q ⁻¹' S => (u A).val) = fun A => A.val 0 0 := by
        funext A; exact IsUnit.unit_spec _
      rw [he]
      exact ((continuous_apply 0).comp ((continuous_apply 0).comp
        (Units.continuous_val : Continuous (fun A : AdelicMatrixGroup F => A.val)))).comp continuous_subtype_val
    · have he : (fun A : q ⁻¹' S => (u A)⁻¹.val) = fun A => A.val⁻¹ 0 0 := by
        funext A; exact upper_inverse00 F A.val (preimage_upper F A.val A.property)
      change Continuous (fun A : q ⁻¹' S => (u A)⁻¹.val)
      rw [he]
      exact ((continuous_apply 0).comp ((continuous_apply 0).comp
        (Units.continuous_coe_inv : Continuous (fun A : AdelicMatrixGroup F => A⁻¹.val)))).comp continuous_subtype_val
  have hw : Continuous w := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : q ⁻¹' S => (w A).val)
      have he : (fun A : q ⁻¹' S => (w A).val) = fun A => A.val 1 1 := by
        funext A; exact IsUnit.unit_spec _
      rw [he]
      exact ((continuous_apply 1).comp ((continuous_apply 1).comp
        (Units.continuous_val : Continuous (fun A : AdelicMatrixGroup F => A.val)))).comp continuous_subtype_val
    · have he : (fun A : q ⁻¹' S => (w A)⁻¹.val) = fun A => A.val⁻¹ 1 1 := by
        funext A; exact upper_inverse11 F A.val (preimage_upper F A.val A.property)
      change Continuous (fun A : q ⁻¹' S => (w A)⁻¹.val)
      rw [he]
      exact ((continuous_apply 1).comp ((continuous_apply 1).comp
        (Units.continuous_coe_inv : Continuous (fun A : AdelicMatrixGroup F => A⁻¹.val)))).comp continuous_subtype_val
  have he : (borelRatio F) ∘ S.restrictPreimage q = fun A => u A * (w A)⁻¹ := by
    funext A
    exact borelRatio_formula F _ A.val rfl (preimage_upper F A.val A.property)
  rw [he]
  exact hu.mul hw.inv

private lemma ideleAbs_continuous : Continuous (KPGlobalTorusFunctionData.ideleAbs F) := by
  have hfinite : Continuous (FiniteIdeleGroup.absoluteNorm (K := F)) := by
    apply continuous_of_continuousAt_one
    apply (continuousAt_const (y := (1 : ℝ≥0ˣ))).congr_of_eventuallyEq
    have ho : IsOpen (FiniteIdeleGroup.integralSubgroup (K := F) :
        Set (FiniteIdeleGroup F)) := by
      simpa only [Finset.coe_empty, FiniteIdeleGroup.supportedAt_empty] using
        (FiniteIdeleGroup.isOpen_supportedAt (K := F) ∅)
    filter_upwards [ho.mem_nhds (Subgroup.one_mem _)] with a ha
    exact IdeleGroup.finite_absoluteNorm_eq_one_of_integral a ha
  have hidele : Continuous (IdeleGroup.absoluteNorm (K := F)) :=
    (hfinite.comp continuous_snd).mul
      ((InfiniteIdeleGroup.continuous_archimedeanNorm.comp continuous_fst).inv)
  exact (hidele.comp (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm.continuous).inv

private lemma compact_positive_hom {H : Type*} [Group H] [TopologicalSpace H]
    [CompactSpace H] (f : H →* (ℝ≥0)ˣ) (hf : Continuous f) (a : H) : f a = 1 := by
  have hb := (isCompact_univ.image (Units.continuous_val.comp hf)).bddAbove
  obtain ⟨M, hM⟩ := hb
  have hle (b : H) : (f b : ℝ≥0) ≤ 1 := by
    by_contra hn
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (lt_of_not_ge hn)
    have hm : ((f b : ℝ≥0) ^ n) ≤ M := by
      have h := hM (Set.mem_image_of_mem (fun b : H => (f b : ℝ≥0)) (Set.mem_univ (b ^ n)))
      simpa only [map_pow, Units.val_pow_eq_pow_val] using h
    exact (not_lt_of_ge hm) hn
  apply Units.ext
  change (f a : ℝ≥0) = 1
  apply le_antisymm (hle a)
  have h := mul_le_mul_of_nonneg_left (hle a⁻¹) (show (0 : ℝ≥0) ≤ (f a : ℝ≥0) from zero_le)
  simpa only [map_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] using h

private lemma root_matrix_entries (x : KPGlobalTorusFunctionData.Adeles F) :
    let A := KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ (KPGlobalTorusFunctionData.rootTuple F ζ hζ x)
    A 1 0 = 0 ∧ A 0 0 = 1 ∧ A 1 1 = 1 := by
  constructor
  · apply Prod.ext
    · funext w; rfl
    · apply RestrictedProduct.ext; intro q; rfl
  constructor
  · apply Prod.ext
    · funext w; rfl
    · apply RestrictedProduct.ext; intro q; rfl
  · apply Prod.ext
    · funext w; rfl
    · apply RestrictedProduct.ext; intro q; rfl

 def coveredRatio : KPGlobalTorusFunctionData.borel F ζ hζ →* Ideles F :=
  (borelRatio F).comp ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).restrict
    (fun b hb => hb))

private lemma coveredRatio_continuous : Continuous (coveredRatio F ζ hζ) := by
  exact (borelRatio_continuous F).comp
    (((KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
      continuous_subtype_val).subtype_mk (fun b => b.property))

private lemma torus_mem_borel (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    t.val ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
  obtain ⟨A, he, h10, h01⟩ := t.property
  exact ⟨A, he, h10⟩

private lemma coveredRatio_torus (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    coveredRatio F ζ hζ ⟨t.val, torus_mem_borel F ζ hζ t⟩ = KPGlobalTorusFunctionData.p F ζ hζ t := by
  obtain ⟨A, he, h10, h01⟩ := t.property
  change borelRatio F _ = KPGlobalTorusFunctionData.torusRatio F _
  rw [borelRatio_formula F _ A he h10]
  apply Units.ext
  exact (KPGlobalTorusFunctionData.ratio_formula F _ A he h10 h01).symm

private lemma root_mem_borel (x : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ x ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
  exact ⟨KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ x), rfl, (root_matrix_entries F ζ hζ x).1⟩

private lemma coveredRatio_root (x : KPGlobalTorusFunctionData.Adeles F) :
    coveredRatio F ζ hζ ⟨KPGlobalTorusFunctionData.N F ζ hζ x, root_mem_borel F ζ hζ x⟩ = 1 := by
  change borelRatio F _ = 1
  rw [borelRatio_formula F _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
    (KPGlobalTorusFunctionData.rootTuple F ζ hζ x)) rfl (root_matrix_entries F ζ hζ x).1]
  apply Units.ext
  simp only [upperRatio, Units.val_mul, Units.val_one]
  have h0 : (KPGlobalTorusMatrixCertificates.diagonal_units _ (root_matrix_entries F ζ hζ x).1).1.unit = 1 := by
    apply Units.ext
    exact (IsUnit.unit_spec _).trans (root_matrix_entries F ζ hζ x).2.1
  have h1 : (KPGlobalTorusMatrixCertificates.diagonal_units _ (root_matrix_entries F ζ hζ x).1).2.unit = 1 := by
    apply Units.ext
    exact (IsUnit.unit_spec _).trans (root_matrix_entries F ζ hζ x).2.2
  rw [h0, h1]
  simp

theorem compact_overlap (K : Subgroup (G F ζ hζ))
    (hK : IsCompact (K : Set (G F ζ hζ)))
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F)
    (htx : t.val * KPGlobalTorusFunctionData.N F ζ hζ x ∈ K) :
    KPGlobalTorusFunctionData.delta F ζ hζ t = 1 := by
  let B := KPGlobalTorusFunctionData.borel F ζ hζ
  let L := K ⊓ B
  have hB : IsClosed (B : Set (G F ζ hζ)) :=
    (ordinaryBorel_closed F).preimage
      (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous
  have hL : IsCompact (L : Set (G F ζ hζ)) := hK.inter_right hB
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let r : L →* Ideles F := (coveredRatio F ζ hζ).comp
    (Subgroup.inclusion (show L ≤ B from inf_le_right))
  have hr : Continuous r := (coveredRatio_continuous F ζ hζ).comp
    (continuous_subtype_val.subtype_mk (fun a => a.property.2))
  let d : L →* (ℝ≥0)ˣ := (KPGlobalTorusFunctionData.ideleAbs F).comp r
  have hd : Continuous d := (ideleAbs_continuous F).comp hr
  let tb : B := ⟨t.val, torus_mem_borel F ζ hζ t⟩
  let nb : B := ⟨KPGlobalTorusFunctionData.N F ζ hζ x, root_mem_borel F ζ hζ x⟩
  let a : L := ⟨t.val * KPGlobalTorusFunctionData.N F ζ hζ x, htx, B.mul_mem tb.property nb.property⟩
  have h := compact_positive_hom d hd a
  change KPGlobalTorusFunctionData.ideleAbs F
    (coveredRatio F ζ hζ (tb * nb)) = 1 at h
  rw [map_mul, coveredRatio_torus, coveredRatio_root, mul_one] at h
  exact h

def literalIwasawa (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) :
    KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ where
  K := K
  compact := hK.1
  decomposition := hK.2.1
  overlap := compact_overlap F ζ hζ K hK.1
end DedekindZetaZeroFree.KPLiteralChamber

end
