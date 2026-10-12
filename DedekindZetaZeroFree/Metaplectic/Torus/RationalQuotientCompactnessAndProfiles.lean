module

public import DedekindZetaZeroFree.Eisenstein.Induction.NormalizedTorusProfiles

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw
open KPGlobalTorusFunctionData
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem actualTorusProjection_surjective :
    Function.Surjective (KPGlobalTorusFunctionData.p F ζ hζ) := by
  intro y
  obtain ⟨g, hg⟩ := KPAdelicCoverRestrictedProduct.pglProjection_surjective F ζ hζ
    (KPGlobalCubicIdelePairing.diagonalPGL F y)
  let A := KPGlobalCubicIdelePairing.diagonalMatrix F y
  have hm : g ∈ KPGlobalTorusFunctionData.E F ζ hζ := by
    change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g ∈
      KPGlobalTorusFunctionData.ordinaryTorus F
    rw [hg]
    exact ⟨A, rfl, by simp [A, KPGlobalCubicIdelePairing.diagonalMatrix],
      by simp [A, KPGlobalCubicIdelePairing.diagonalMatrix]⟩
  refine ⟨⟨g, hm⟩, ?_⟩
  apply Units.ext
  change (KPGlobalTorusFunctionData.torusRatio F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g, hm⟩ : KPAdeles F) = _
  have h10 : A 1 0 = 0 := by simp [A, KPGlobalCubicIdelePairing.diagonalMatrix]
  have h01 : A 0 1 = 0 := by simp [A, KPGlobalCubicIdelePairing.diagonalMatrix]
  have hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g := hg.symm
  rw [KPGlobalTorusFunctionData.ratio_formula F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g, hm⟩ A hA h10 h01]
  have h11 : (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit = 1 := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPGlobalCubicIdelePairing.diagonalMatrix]
  rw [h11, inv_one, Units.val_one, mul_one, IsUnit.unit_spec]
  rfl

private theorem ratio_val_formula (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    ((diagonal_entries_units F A h10 h01).1.unit : Adeles F) *
      ↑((diagonal_entries_units F A h10 h01).2.unit)⁻¹ = A 0 0 * A⁻¹ 1 1 := by
  have hi : (A⁻¹ : KPGlobalTorusFunctionData.AdelicMatrixGroup F) 1 1 =
      ↑((diagonal_entries_units F A h10 h01).2.unit)⁻¹ := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Adeles F) => M 1 1) A.val_inv
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, zero_mul, zero_add,
      Matrix.one_apply_eq] at hh
    apply (diagonal_entries_units F A h10 h01).2.mul_left_cancel
    change A.val 1 1 * A.inv 1 1 = _
    calc
      _ = 1 := hh
      _ = _ := by
        simpa only [IsUnit.unit_spec] using
          ((diagonal_entries_units F A h10 h01).2.unit.mul_inv).symm
  rw [hi, IsUnit.unit_spec]

private theorem ratio_inverse_formula (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    (↑(((diagonal_entries_units F A h10 h01).1.unit *
      ((diagonal_entries_units F A h10 h01).2.unit)⁻¹)⁻¹) : Adeles F) = A 1 1 * A⁻¹ 0 0 := by
  have hi : (A⁻¹ : KPGlobalTorusFunctionData.AdelicMatrixGroup F) 0 0 =
      ↑((diagonal_entries_units F A h10 h01).1.unit)⁻¹ := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Adeles F) => M 0 0) A.val_inv
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, zero_mul, add_zero,
      Matrix.one_apply_eq] at hh
    apply (diagonal_entries_units F A h10 h01).1.mul_left_cancel
    change A.val 0 0 * A.inv 0 0 = _
    calc
      _ = 1 := hh
      _ = _ := by
        simpa only [IsUnit.unit_spec] using
          ((diagonal_entries_units F A h10 h01).1.unit.mul_inv).symm
  simp only [mul_inv_rev, inv_inv, Units.val_mul]
  rw [hi, IsUnit.unit_spec]

 def ordinaryDiagonal (y : Ideles F) : ordinaryTorus F :=
  ⟨KPGlobalCubicIdelePairing.diagonalPGL F y,
    ⟨KPGlobalCubicIdelePairing.diagonalMatrix F y, rfl, by
      simp [KPGlobalCubicIdelePairing.diagonalMatrix], by
      simp [KPGlobalCubicIdelePairing.diagonalMatrix]⟩⟩

 theorem ordinaryRatio_diagonal (y : Ideles F) :
    torusRatio F (ordinaryDiagonal F y) = y := by
  apply Units.ext
  rw [ratio_formula F _ (KPGlobalCubicIdelePairing.diagonalMatrix F y) rfl
    (by simp [KPGlobalCubicIdelePairing.diagonalMatrix])
    (by simp [KPGlobalCubicIdelePairing.diagonalMatrix])]
  rw [ratio_val_formula F _ (by simp [KPGlobalCubicIdelePairing.diagonalMatrix])
    (by simp [KPGlobalCubicIdelePairing.diagonalMatrix])]
  simp [KPGlobalCubicIdelePairing.diagonalMatrix]

 theorem ordinaryDiagonal_continuous : Continuous (ordinaryDiagonal F) := by
  apply Continuous.subtype_mk
  apply QuotientGroup.continuous_mk.comp
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_matrix (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [KPGlobalCubicIdelePairing.diagonalPGL,
          KPGlobalCubicIdelePairing.diagonalHom,
          KPGlobalCubicIdelePairing.diagonalMatrix] <;> fun_prop)
  · exact continuous_matrix (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [KPGlobalCubicIdelePairing.diagonalPGL,
          KPGlobalCubicIdelePairing.diagonalHom,
          KPGlobalCubicIdelePairing.diagonalMatrix] <;> fun_prop)

private theorem diagonal_preimage (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A ∈
      ordinaryTorus F) : A 1 0 = 0 ∧ A 0 1 = 0 := by
  obtain ⟨B, he, h10, h01⟩ := hA
  obtain ⟨c, hc, rfl⟩ := (QuotientGroup.mk'_eq_mk' _).mp he
  obtain ⟨u, rfl⟩ := hc
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal, h10, h01]

 theorem ordinaryRatio_continuous : Continuous (torusRatio F) := by
  let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N :=
    KPAdelicCoverRestrictedProduct.scalarSubgroup F)).restrictPreimage
      (ordinaryTorus F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F))
  apply hq.isQuotientMap.continuous_iff.mpr
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun a : {A : KPGlobalTorusFunctionData.AdelicMatrixGroup F // q A ∈ ordinaryTorus F} =>
        (torusRatio F ⟨q a.val, a.property⟩ : Adeles F))
    have he : (fun a : {A : KPGlobalTorusFunctionData.AdelicMatrixGroup F // q A ∈ ordinaryTorus F} =>
        (torusRatio F ⟨q a.val, a.property⟩ : Adeles F)) =
        (fun a => a.val 0 0 * a.val⁻¹ 1 1) := by
      funext a
      rw [ratio_formula F _ a.val rfl (diagonal_preimage F a.val a.property).1
        (diagonal_preimage F a.val a.property).2, ratio_val_formula F _
          (diagonal_preimage F a.val a.property).1
          (diagonal_preimage F a.val a.property).2]
    rw [he]
    have hv : Continuous (fun a : KPGlobalTorusFunctionData.AdelicMatrixGroup F =>
        (a.val : Matrix (Fin 2) (Fin 2) (Adeles F))) := Units.continuous_val
    have hi : Continuous (fun a : KPGlobalTorusFunctionData.AdelicMatrixGroup F =>
        (a.inv : Matrix (Fin 2) (Fin 2) (Adeles F))) := Units.continuous_coe_inv
    exact ((hv.comp continuous_subtype_val).matrix_elem 0 0).mul
      ((hi.comp continuous_subtype_val).matrix_elem 1 1)
  · change Continuous (fun a : {A : KPGlobalTorusFunctionData.AdelicMatrixGroup F // q A ∈ ordinaryTorus F} =>
        (↑((torusRatio F ⟨q a.val, a.property⟩)⁻¹) : Adeles F))
    have he : (fun a : {A : KPGlobalTorusFunctionData.AdelicMatrixGroup F // q A ∈ ordinaryTorus F} =>
        (↑((torusRatio F ⟨q a.val, a.property⟩)⁻¹) : Adeles F)) =
        (fun a => a.val 1 1 * a.val⁻¹ 0 0) := by
      funext a
      have hf : torusRatio F ⟨q a.val, a.property⟩ =
        (diagonal_entries_units F a.val (diagonal_preimage F a.val a.property).1
          (diagonal_preimage F a.val a.property).2).1.unit *
        ((diagonal_entries_units F a.val (diagonal_preimage F a.val a.property).1
          (diagonal_preimage F a.val a.property).2).2.unit)⁻¹ := by
        apply Units.ext
        exact ratio_formula F _ a.val rfl (diagonal_preimage F a.val a.property).1
          (diagonal_preimage F a.val a.property).2
      rw [hf, ratio_inverse_formula F _
        (diagonal_preimage F a.val a.property).1
        (diagonal_preimage F a.val a.property).2]
    rw [he]
    have hv : Continuous (fun a : KPGlobalTorusFunctionData.AdelicMatrixGroup F =>
        (a.val : Matrix (Fin 2) (Fin 2) (Adeles F))) := Units.continuous_val
    have hi : Continuous (fun a : KPGlobalTorusFunctionData.AdelicMatrixGroup F =>
        (a.inv : Matrix (Fin 2) (Fin 2) (Adeles F))) := Units.continuous_coe_inv
    exact ((hv.comp continuous_subtype_val).matrix_elem 1 1).mul
      ((hi.comp continuous_subtype_val).matrix_elem 0 0)

 theorem ordinaryDiagonal_ratio (t : ordinaryTorus F) :
    ordinaryDiagonal F (torusRatio F t) = t := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  have hf : torusRatio F t = (diagonal_entries_units F A h10 h01).1.unit *
      ((diagonal_entries_units F A h10 h01).2.unit)⁻¹ := by
    apply Units.ext
    exact ratio_formula F t A hA h10 h01
  apply Subtype.ext
  change KPGlobalCubicIdelePairing.diagonalPGL F (torusRatio F t) = t.val
  rw [hf, ← hA]
  apply (QuotientGroup.mk'_eq_mk' _).mpr
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2)
    (diagonal_entries_units F A h10 h01).2.unit, ⟨_, rfl⟩, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KPGlobalCubicIdelePairing.diagonalMatrix,
      KPGlobalCubicIdelePairing.diagonalPGL, KPGlobalCubicIdelePairing.diagonalHom,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal, h10, h01, IsUnit.unit_spec]
  rw [mul_assoc]
  have hc := (diagonal_entries_units F A h10 h01).2.unit.inv_mul
  rw [IsUnit.unit_spec] at hc
  rw [hc, mul_one]

 def ordinaryTorusHomeomorph : ordinaryTorus F ≃ₜ Ideles F where
  toFun := torusRatio F
  invFun := ordinaryDiagonal F
  left_inv := ordinaryDiagonal_ratio F
  right_inv := ordinaryRatio_diagonal F
  continuous_toFun := ordinaryRatio_continuous F
  continuous_invFun := ordinaryDiagonal_continuous F

theorem actualTorusProjection_topology :
    Continuous (KPGlobalTorusFunctionData.p F ζ hζ) ∧
      IsOpenMap (KPGlobalTorusFunctionData.p F ζ hζ) := by
  have hc := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2
  have hr := hc.isOpenMap.restrictPreimage
    (ordinaryTorus F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F))
  have ht := hc.continuous.restrictPreimage
    (s := (ordinaryTorus F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F)))
  exact ⟨(ordinaryRatio_continuous F).comp ht,
    (ordinaryTorusHomeomorph F).isOpenMap.comp hr⟩

theorem actualR_normal : (KPGlobalCenterRationalCharacter.R F ζ hζ).Normal := by
  rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ]
  infer_instance

theorem actualR_cocompact :
    CompactSpace (KPGlobalTorusFunctionData.E F ζ hζ ⧸
      KPGlobalCenterRationalCharacter.R F ζ hζ) := by
  letI := actualR_normal F ζ hζ
  have hp := actualTorusProjection_surjective F ζ hζ
  have ht := actualTorusProjection_topology F ζ hζ
  apply KPCubicIdele.coveringTorus_quotient_compact F _
    (KPGlobalTorusFunctionData.p F ζ hζ) ht.1 ht.2 hp
    (KPGlobalCenterRationalCharacter.R F ζ hζ)
  · intro x hx
    rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ]
    change QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F))
      (KPGlobalTorusFunctionData.p F ζ hζ x) ∈ KPGlobalPrincipalCubicLagrangian.A F
    rw [MonoidHom.mem_ker.mp hx, map_one]
    exact Subgroup.one_mem _
  · rintro y ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hp (IdeleGroup.unitEmbedding (𝓞 F) F a)
    refine Subgroup.mem_map.mpr ⟨x, ?_, hx⟩
    rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ]
    change QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F))
      (KPGlobalTorusFunctionData.p F ζ hζ x) ∈ KPGlobalPrincipalCubicLagrangian.A F
    rw [hx]
    exact ⟨a, rfl⟩
  · rintro y ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hp (a ^ 3)
    refine Subgroup.mem_map.mpr ⟨x, ?_, hx⟩
    rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ]
    change QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F))
      (KPGlobalTorusFunctionData.p F ζ hζ x) ∈ KPGlobalPrincipalCubicLagrangian.A F
    rw [hx]
    have he : QuotientGroup.mk' (CubicCharacters.cubes
        (KPGlobalTorusFunctionData.Ideles F)) (a ^ 3) = 1 :=
      (QuotientGroup.eq_one_iff (N := CubicCharacters.cubes
        (KPGlobalTorusFunctionData.Ideles F)) (a ^ 3)).mpr ⟨a, rfl⟩
    rw [he]
    exact Subgroup.one_mem _

theorem normalizedTorusProfile_bounded (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K),
      normalizedTorusProfile F ζ hζ K f t k ≤ B := by
  letI := actualR_normal F ζ hζ
  letI := actualR_cocompact F ζ hζ
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  let Q := KPGlobalTorusFunctionData.E F ζ hζ ⧸ KPGlobalCenterRationalCharacter.R F ζ hζ
  let u : Q → K → ℝ := Quotient.lift
    (fun t k => normalizedTorusProfile F ζ hζ K f t k) (by
      intro a b hab
      funext k
      have hr : a⁻¹ * b ∈ KPGlobalCenterRationalCharacter.R F ζ hζ :=
        QuotientGroup.leftRel_apply.mp hab
      have hr' : b * a⁻¹ ∈ KPGlobalCenterRationalCharacter.R F ζ hζ := by
        simpa only [← mul_assoc, mul_inv_cancel, one_mul] using
          (actualR_normal F ζ hζ).conj_mem (a⁻¹ * b) hr a
      have he := normalizedTorusProfile_R_invariant F ζ hζ K f
        ⟨b * a⁻¹, hr'⟩ a k
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he.symm)
  have hu : Continuous (fun p : Q × K => u p.1 p.2) := by
    have hid : IsOpenQuotientMap (id : K → K) :=
      ⟨Function.surjective_id, continuous_id, IsOpenMap.id⟩
    apply (QuotientGroup.isOpenQuotientMap_mk.prodMap hid).isQuotientMap.continuous_iff.mpr
    exact normalizedTorusProfile_continuous F ζ hζ K f
  obtain ⟨B, hB⟩ := (isCompact_univ.image hu).bddAbove
  refine ⟨max 0 B, le_max_left _ _, fun t k => ?_⟩
  exact (hB ⟨(QuotientGroup.mk t, k), Set.mem_univ _, rfl⟩).trans (le_max_right _ _)

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
