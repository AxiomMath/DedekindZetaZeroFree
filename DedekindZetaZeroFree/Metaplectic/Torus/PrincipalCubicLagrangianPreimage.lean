module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterCharacterData

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def coveredTorusDiagonalRatioCubicProjection : E F ζ hζ →* KPGlobalCubicIdelePairing.D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp
    (KPGlobalTorusFunctionData.p F ζ hζ)

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

private theorem p_continuous : Continuous (KPGlobalTorusFunctionData.p F ζ hζ) := by
  apply (ratio_continuous F).comp
  exact ((KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
    continuous_subtype_val).subtype_mk (fun t => t.property)

private theorem pD_continuous : Continuous (coveredTorusDiagonalRatioCubicProjection F ζ hζ) :=
  (QuotientGroup.isOpenQuotientMap_mk).continuous.comp (p_continuous F ζ hζ)

private theorem p_rational (a : Fˣ) :
    KPGlobalTorusFunctionData.p F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a) =
      IdeleGroup.unitEmbedding (𝓞 F) F a := by
  let A := KPAdelicCoverRestrictedProduct.rationalBase F (KubotaRankTwo.d F a 1)
  have hp : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (KPGlobalTorusFunctionData.s F ζ hζ a).val =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A := by
    change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.projection F ζ hζ
      (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ _)) = _
    rw [KPAdelicCoverRestrictedProduct.projection_rationalSection]
    rfl
  have h10 : A 1 0 = 0 := by simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  have h01 : A 0 1 = 0 := by simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  have h := KPGlobalTorusFunctionData.ratio_formula F
    ⟨_, (KPGlobalTorusFunctionData.s F ζ hζ a).property⟩ A hp.symm h10 h01
  apply Units.ext
  change (KPGlobalTorusFunctionData.torusRatio F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a).val,
      (KPGlobalTorusFunctionData.s F ζ hζ a).property⟩ : KPGlobalTorusFunctionData.Adeles F) = _
  rw [h]
  have he1 : (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit =
      IdeleGroup.unitEmbedding (𝓞 F) F a := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPAdelicCoverRestrictedProduct.rationalBase, NumberField.IdeleGroup.unitEmbedding]
  have he2 : (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit = 1 := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  simp [he1, he2]

private theorem pD_rational (a : Fˣ) :
    coveredTorusDiagonalRatioCubicProjection F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a) =
      KPGlobalPrincipalCubicLagrangian.principalClass F a := by
  rw [coveredTorusDiagonalRatioCubicProjection, MonoidHom.comp_apply, p_rational F ζ hζ a]
  rfl

 theorem principalCubicLagrangianPreimage_diagonalPGL_torusRatio (t : KPGlobalTorusFunctionData.ordinaryTorus F) :
    KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.torusRatio F t) = t.val := by
  let A := Classical.choose t.property
  have hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = t.val ∧
      A 1 0 = 0 ∧ A 0 1 = 0 := Classical.choose_spec t.property
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).1.unit
  let w := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).2.unit
  have hu : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 0 0 := IsUnit.unit_spec _
  have hw : (w : KPAdelicCoverRestrictedProduct.Adeles F) = A 1 1 := IsUnit.unit_spec _
  have heq : A = KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hu, hA.2.1, hA.2.2]
    exact hw.symm
  change QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹)) = t.val
  rw [← hA.1, heq]
  have hs : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) w) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
  rw [(QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).map_mul, hs, mul_one]

 def coveredTorusDiagonalRatioPullbackHom : E F ζ hζ →* KPGlobalCubicIdelePairing.E F ζ hζ where
  toFun e := ⟨(e.val, KPGlobalTorusFunctionData.p F ζ hζ e),
    (principalCubicLagrangianPreimage_diagonalPGL_torusRatio F ⟨_, e.property⟩).symm⟩
  map_one' := by apply Subtype.ext; exact Prod.ext rfl (map_one _)
  map_mul' x y := by apply Subtype.ext; exact Prod.ext rfl (map_mul _ _ _)

private theorem torusPullbackBridge_injective :
    Function.Injective (coveredTorusDiagonalRatioPullbackHom F ζ hζ) := by
  intro x y h
  exact Subtype.ext (congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1) h)

private theorem torusPullbackBridge_surjective :
    Function.Surjective (coveredTorusDiagonalRatioPullbackHom F ζ hζ) := by
  intro t
  have ht : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val.1 =
      KPGlobalCubicIdelePairing.diagonalPGL F t.val.2 :=
    t.property
  have hmem : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val.1 ∈
      KPGlobalTorusFunctionData.ordinaryTorus F := by
    rw [ht]
    exact ⟨KPGlobalCubicIdelePairing.diagonalHom F t.val.2, rfl,
      by simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix],
      by simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]⟩
  refine ⟨⟨t.val.1, hmem⟩, ?_⟩
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show KPGlobalTorusFunctionData.p F ζ hζ ⟨t.val.1, hmem⟩ = t.val.2
  let A := KPGlobalCubicIdelePairing.diagonalHom F t.val.2
  have hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      (⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val.1, hmem⟩ :
        KPGlobalTorusFunctionData.ordinaryTorus F).val := by
    change QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F t.val.2) =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val.1
    rw [ht]
    rfl
  have h10 : A 1 0 = 0 := by
    simp [A, KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  have h01 : A 0 1 = 0 := by
    simp [A, KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  have h := KPGlobalTorusFunctionData.ratio_formula F
    ⟨_, hmem⟩ A hA h10 h01
  apply Units.ext
  change (KPGlobalTorusFunctionData.torusRatio F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val.1, hmem⟩ :
      KPGlobalTorusFunctionData.Adeles F) = _
  rw [h]
  have he1 : (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit = t.val.2 := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  have he2 : (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit = 1 := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  simp [he1, he2]

private theorem commute_iff_beta (x y : E F ζ hζ) :
    Commute x y ↔ KPGlobalCubicIdelePairing.beta3 F ζ hζ
      (coveredTorusDiagonalRatioCubicProjection F ζ hζ x) (coveredTorusDiagonalRatioCubicProjection F ζ hζ y) = 1 := by
  have h := KPGlobalCubicIdelePairing.commutator_annihilators F ζ hζ
    (coveredTorusDiagonalRatioPullbackHom F ζ hζ x) (coveredTorusDiagonalRatioPullbackHom F ζ hζ y)
  constructor
  · intro hc
    exact h.mp (hc.map (coveredTorusDiagonalRatioPullbackHom F ζ hζ))
  · intro hb
    apply torusPullbackBridge_injective F ζ hζ
    simpa only [map_mul] using (h.mpr hb).eq

private theorem center_eq_pD_ker : Z F ζ hζ = (coveredTorusDiagonalRatioCubicProjection F ζ hζ).ker := by
  have hcenter : (Z F ζ hζ : Subgroup (E F ζ hζ)) =
      (KPGlobalCubicIdelePairing.Z F ζ hζ).comap (coveredTorusDiagonalRatioPullbackHom F ζ hζ) := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro w
      obtain ⟨u, rfl⟩ := torusPullbackBridge_surjective F ζ hζ w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz u]
    · intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      apply torusPullbackBridge_injective F ζ hζ
      rw [map_mul, map_mul,
        Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hz) (coveredTorusDiagonalRatioPullbackHom F ζ hζ w)]
  rw [hcenter, KPGlobalCubicIdelePairing.torus_center F ζ hζ, coveredTorusDiagonalRatioCubicProjection,
    ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rfl

private theorem mem_A_iff_annihilator (x : KPGlobalCubicIdelePairing.D F) :
    x ∈ KPGlobalPrincipalCubicLagrangian.A F ↔
      x ∈ KPGlobalPrincipalCubicLagrangian.annihilator F ζ hζ
        (KPGlobalPrincipalCubicLagrangian.A F) := by
  rw [KPGlobalPrincipalCubicLagrangian.principal_self_annihilating F ζ hζ]
  simp

theorem rational_subgroup_geometry :
    rationalCenterSubgroup F ζ hζ =
      (KPGlobalPrincipalCubicLagrangian.A F).comap
        ((QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp
          (KPGlobalTorusFunctionData.p F ζ hζ)) ∧
    IsClosed (rationalCenterSubgroup F ζ hζ : Set (E F ζ hζ)) ∧
    KPLocalPolarization.IsMaximalAbelian (rationalCenterSubgroup F ζ hζ) := by
  have hiso : ∀ a ∈ KPGlobalPrincipalCubicLagrangian.A F,
      ∀ b ∈ KPGlobalPrincipalCubicLagrangian.A F,
      KPGlobalCubicIdelePairing.beta3 F ζ hζ a b = 1 := by
    intro a ha b hb
    exact (mem_A_iff_annihilator F ζ hζ a).mp ha b hb
  have hR : rationalCenterSubgroup F ζ hζ =
      (KPGlobalPrincipalCubicLagrangian.A F).comap (coveredTorusDiagonalRatioCubicProjection F ζ hζ) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_comap]
      have hx' : x ∈ (KPGlobalTorusFunctionData.s F ζ hζ).range ⊔ Z F ζ hζ := hx
      obtain ⟨u, hu, z, hz, hxz⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
      obtain ⟨a, rfl⟩ := hu
      have hz1 : coveredTorusDiagonalRatioCubicProjection F ζ hζ z = 1 := by
        have hmem : z ∈ (coveredTorusDiagonalRatioCubicProjection F ζ hζ).ker := by
          rw [← center_eq_pD_ker F ζ hζ]; exact hz
        exact MonoidHom.mem_ker.mp hmem
      rw [← hxz, map_mul, pD_rational F ζ hζ a, hz1, mul_one]
      exact ⟨a, rfl⟩
    · intro hx
      obtain ⟨a, ha⟩ := hx
      have h1 : coveredTorusDiagonalRatioCubicProjection F ζ hζ ((KPGlobalTorusFunctionData.s F ζ hζ a)⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, pD_rational F ζ hζ a, ha.symm, inv_mul_cancel]
      have hz : (KPGlobalTorusFunctionData.s F ζ hζ a)⁻¹ * x ∈ Z F ζ hζ := by
        rw [center_eq_pD_ker F ζ hζ]
        exact MonoidHom.mem_ker.mpr h1
      have hx' : x = KPGlobalTorusFunctionData.s F ζ hζ a *
          ((KPGlobalTorusFunctionData.s F ζ hζ a)⁻¹ * x) := by group
      rw [hx']
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (⟨a, rfl⟩ : KPGlobalTorusFunctionData.s F ζ hζ a ∈
          (KPGlobalTorusFunctionData.s F ζ hζ).range))
        (Subgroup.mem_sup_right hz)
  refine ⟨hR, ?_, ?_⟩
  · rw [hR]
    haveI : T2Space (KPGlobalCubicIdelePairing.D F) := KPGlobalCubicIdelePairing.hausdorff F
    haveI : DiscreteTopology (KPGlobalPrincipalCubicLagrangian.A F) :=
      KPGlobalPrincipalCubicLagrangian.principal_discrete F ζ hζ
    have hAcl : IsClosed
        (KPGlobalPrincipalCubicLagrangian.A F : Set (KPGlobalCubicIdelePairing.D F)) :=
      Subgroup.isClosed_of_discreteTopology
    show IsClosed (coveredTorusDiagonalRatioCubicProjection F ζ hζ ⁻¹'
      (KPGlobalPrincipalCubicLagrangian.A F : Set (KPGlobalCubicIdelePairing.D F)))
    exact hAcl.preimage (pD_continuous F ζ hζ)
  · rw [hR]
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      exact (commute_iff_beta F ζ hζ x y).mpr
        (hiso (coveredTorusDiagonalRatioCubicProjection F ζ hζ x) hx (coveredTorusDiagonalRatioCubicProjection F ζ hζ y) hy)
    · intro B hB hBab
      apply le_antisymm _ hB
      intro x hx
      show coveredTorusDiagonalRatioCubicProjection F ζ hζ x ∈ KPGlobalPrincipalCubicLagrangian.A F
      rw [mem_A_iff_annihilator F ζ hζ]
      intro y hy
      obtain ⟨a₀, rfl⟩ := hy
      have hs_mem : KPGlobalTorusFunctionData.s F ζ hζ a₀ ∈
          (KPGlobalPrincipalCubicLagrangian.A F).comap (coveredTorusDiagonalRatioCubicProjection F ζ hζ) := by
        rw [Subgroup.mem_comap, pD_rational F ζ hζ a₀]
        exact ⟨a₀, rfl⟩
      have hcomm : Commute x (KPGlobalTorusFunctionData.s F ζ hζ a₀) :=
        hBab x hx _ (hB hs_mem)
      have hbeta := (commute_iff_beta F ζ hζ x (KPGlobalTorusFunctionData.s F ζ hζ a₀)).mp hcomm
      rwa [pD_rational F ζ hζ a₀] at hbeta

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
