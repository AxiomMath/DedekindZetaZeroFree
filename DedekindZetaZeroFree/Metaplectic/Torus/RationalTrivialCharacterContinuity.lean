module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterCharacterData

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

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

 theorem rationalTrivialCharacterContinuity_diagonalPGL_torusRatio_eq (t : KPGlobalTorusFunctionData.ordinaryTorus F) :
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

 def ordinaryTorusCoverToCubicPullback : E F ζ hζ →* KPGlobalCubicIdelePairing.E F ζ hζ where
  toFun e := ⟨(e.val, KPGlobalTorusFunctionData.p F ζ hζ e),
    (rationalTrivialCharacterContinuity_diagonalPGL_torusRatio_eq F ⟨_, e.property⟩).symm⟩
  map_one' := by
    apply Subtype.ext
    exact Prod.ext rfl (map_one (KPGlobalTorusFunctionData.p F ζ hζ))
  map_mul' x y := by
    apply Subtype.ext
    exact Prod.ext rfl (map_mul (KPGlobalTorusFunctionData.p F ζ hζ) x y)

private theorem torusPullbackBridge_injective :
    Function.Injective (ordinaryTorusCoverToCubicPullback F ζ hζ) := by
  intro x y h
  exact Subtype.ext (congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1) h)

private theorem torusPullbackBridge_surjective :
    Function.Surjective (ordinaryTorusCoverToCubicPullback F ζ hζ) := by
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

 def ordinaryTorusCoverRatioModuloCubes : E F ζ hζ →* KPGlobalCubicIdelePairing.D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp (KPGlobalTorusFunctionData.p F ζ hζ)

 def rhoPrime : KPGlobalCubicIdelePairing.E F ζ hζ →* KPGlobalCubicIdelePairing.D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp
    (KPGlobalCubicIdelePairing.torusProjection F ζ hζ)

private theorem rhoPrime_ker :
    (rhoPrime F ζ hζ).ker = Subgroup.comap (KPGlobalCubicIdelePairing.torusProjection F ζ hζ)
      (CubicCharacters.cubes (Ideles F)) := by
  show ((QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp
    (KPGlobalCubicIdelePairing.torusProjection F ζ hζ)).ker = _
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

private theorem center_eq_ker_pD : Z F ζ hζ = (ordinaryTorusCoverRatioModuloCubes F ζ hζ).ker := by
  have hbij : Function.Bijective (ordinaryTorusCoverToCubicPullback F ζ hζ) :=
    ⟨torusPullbackBridge_injective F ζ hζ, torusPullbackBridge_surjective F ζ hζ⟩
  have hcenter : (Z F ζ hζ : Subgroup (E F ζ hζ)) =
      (KPGlobalCubicIdelePairing.Z F ζ hζ).comap (ordinaryTorusCoverToCubicPullback F ζ hζ) := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro w
      obtain ⟨u, rfl⟩ := hbij.2 w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz u]
    · intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      apply hbij.1
      rw [map_mul, map_mul,
        Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hz) (ordinaryTorusCoverToCubicPullback F ζ hζ w)]
  have hZ' : KPGlobalCubicIdelePairing.Z F ζ hζ = (rhoPrime F ζ hζ).ker := by
    rw [KPGlobalCubicIdelePairing.torus_center F ζ hζ, rhoPrime_ker F ζ hζ]
  have hcomp : (rhoPrime F ζ hζ).comp (ordinaryTorusCoverToCubicPullback F ζ hζ) = ordinaryTorusCoverRatioModuloCubes F ζ hζ := by
    ext e
    rfl
  rw [hcenter, hZ',
    MonoidHom.comap_ker (rhoPrime F ζ hζ) (ordinaryTorusCoverToCubicPullback F ζ hζ), hcomp]

private theorem pD_mem_A (g : E F ζ hζ) (hg : g ∈ rationalCenterSubgroup F ζ hζ) :
    ordinaryTorusCoverRatioModuloCubes F ζ hζ g ∈ KPGlobalPrincipalCubicLagrangian.A F := by
  have hg' : g ∈ (KPGlobalTorusFunctionData.s F ζ hζ).range ⊔ Z F ζ hζ := hg
  obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hg'
  obtain ⟨a, rfl⟩ := hx
  have hy1 : ordinaryTorusCoverRatioModuloCubes F ζ hζ y = 1 := by
    have hmem : y ∈ (ordinaryTorusCoverRatioModuloCubes F ζ hζ).ker := by
      rw [← center_eq_ker_pD F ζ hζ]; exact hy
    exact MonoidHom.mem_ker.mp hmem
  have hsa : ordinaryTorusCoverRatioModuloCubes F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a) =
      KPGlobalPrincipalCubicLagrangian.principalClass F a := by
    rw [ordinaryTorusCoverRatioModuloCubes, MonoidHom.comp_apply, p_rational]
    rfl
  rw [← hxy, map_mul, hsa, hy1, mul_one]
  exact ⟨a, rfl⟩

theorem rational_extension_continuous (χ : Z F ζ hζ →ₜ* ℂˣ)
    (f : rationalCenterSubgroup F ζ hζ → ℂˣ)
    (hf : ∀ (g : rationalCenterSubgroup F ζ hζ) (a : Fˣ) (z : Z F ζ hζ),
      KPGlobalTorusFunctionData.s F ζ hζ a * z.val = g.val → f g = χ z) :
    Continuous f := by
  classical
  have decomp : ∀ g : rationalCenterSubgroup F ζ hζ, ∃ a : Fˣ, ∃ z : Z F ζ hζ,
      KPGlobalTorusFunctionData.s F ζ hζ a * z.val = g.val := by
    intro g
    have hg : g.val ∈ (KPGlobalTorusFunctionData.s F ζ hζ).range ⊔ Z F ζ hζ := g.property
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, ⟨y, hy⟩, hxy⟩
  have hf1 : f 1 = 1 := by
    have h := hf 1 1 1 (by simp)
    simpa using h
  have hfmul : ∀ g h : rationalCenterSubgroup F ζ hζ, f (g * h) = f g * f h := by
    intro g h
    obtain ⟨a₁, z₁, hz₁⟩ := decomp g
    obtain ⟨a₂, z₂, hz₂⟩ := decomp h
    have hc : Commute (KPGlobalTorusFunctionData.s F ζ hζ a₂) z₁.val :=
      Subgroup.mem_center_iff.mp z₁.property _
    have hgh : KPGlobalTorusFunctionData.s F ζ hζ (a₁ * a₂) * (z₁ * z₂).val = (g * h).val := by
      rw [map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      calc (KPGlobalTorusFunctionData.s F ζ hζ a₁ * KPGlobalTorusFunctionData.s F ζ hζ a₂) *
            (z₁.val * z₂.val)
          = (KPGlobalTorusFunctionData.s F ζ hζ a₁ * z₁.val) *
              (KPGlobalTorusFunctionData.s F ζ hζ a₂ * z₂.val) :=
            hc.mul_mul_mul_comm _ _
        _ = g.val * h.val := by rw [hz₁, hz₂]
    have h1 := hf (g * h) (a₁ * a₂) (z₁ * z₂) hgh
    rw [h1, map_mul, hf g a₁ z₁ hz₁, hf h a₂ z₂ hz₂]
  let fM : rationalCenterSubgroup F ζ hζ →* ℂˣ :=
    { toFun := f, map_one' := hf1, map_mul' := hfmul }
  have hZR : Z F ζ hζ ≤ rationalCenterSubgroup F ζ hζ :=
    fun z hz => Subgroup.mem_sup_right hz

  haveI : IsTopologicalGroup (KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hpDcont : Continuous (ordinaryTorusCoverRatioModuloCubes F ζ hζ) :=
    (QuotientGroup.isOpenQuotientMap_mk).continuous.comp (p_continuous F ζ hζ)
  haveI : DiscreteTopology (KPGlobalPrincipalCubicLagrangian.A F) :=
    KPGlobalPrincipalCubicLagrangian.principal_discrete F ζ hζ
  have h1open : IsOpen ({1} : Set (KPGlobalPrincipalCubicLagrangian.A F)) :=
    discreteTopology_iff_isOpen_singleton_one.mp inferInstance
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.mp h1open
  have honeU : (1 : KPGlobalCubicIdelePairing.D F) ∈ U := by
    have h := (Set.ext_iff.mp hUeq (1 : KPGlobalPrincipalCubicLagrangian.A F))
    simpa using h.mpr rfl
  have hZopen : IsOpen {g : rationalCenterSubgroup F ζ hζ | g.val ∈ Z F ζ hζ} := by
    have hZeq : {g : rationalCenterSubgroup F ζ hζ | g.val ∈ Z F ζ hζ} =
        {g : rationalCenterSubgroup F ζ hζ | ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val ∈ U} := by
      ext g
      constructor
      · intro hg
        show ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val ∈ U
        have hmem : g.val ∈ (ordinaryTorusCoverRatioModuloCubes F ζ hζ).ker := by
          rw [← center_eq_ker_pD F ζ hζ]; exact hg
        rw [MonoidHom.mem_ker.mp hmem]; exact honeU
      · intro hg
        show g.val ∈ Z F ζ hζ
        have hA : ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val ∈ KPGlobalPrincipalCubicLagrangian.A F :=
          pD_mem_A F ζ hζ g.val g.property
        have haux : (⟨ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val, hA⟩ : KPGlobalPrincipalCubicLagrangian.A F) = 1 :=
          (Set.ext_iff.mp hUeq ⟨ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val, hA⟩).mp hg
        have : ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val = 1 := congrArg Subtype.val haux
        rw [center_eq_ker_pD F ζ hζ]
        exact MonoidHom.mem_ker.mpr this
    rw [hZeq]
    exact (hpDcont.comp continuous_subtype_val).isOpen_preimage U hUopen

  have hfOnZ : (fM ∘ Subgroup.inclusion hZR) = fun z : Z F ζ hζ => χ z := by
    funext z
    change f ⟨(z : E F ζ hζ), hZR z.property⟩ = χ z
    exact hf _ 1 z (by simp)
  have hcont1 : ContinuousAt fM 1 := by
    have hiind : Topology.IsInducing (Subgroup.inclusion hZR) :=
      (Topology.IsEmbedding.inclusion hZR).isInducing
    have hrange : Set.range (Subgroup.inclusion hZR) =
        {g : rationalCenterSubgroup F ζ hζ | g.val ∈ Z F ζ hζ} := by
      ext g; constructor
      · rintro ⟨z, rfl⟩; exact z.property
      · intro hg; exact ⟨⟨g.val, hg⟩, Subtype.ext rfl⟩
    have hmem : Set.range (Subgroup.inclusion hZR) ∈ nhds (Subgroup.inclusion hZR 1) := by
      rw [hrange]
      exact hZopen.mem_nhds (by simp)
    have hc : Continuous (fM ∘ Subgroup.inclusion hZR) := by
      rw [hfOnZ]; exact χ.continuous
    have hcat := (hiind.continuousAt_iff' hmem).mp (hc.continuousAt (x := (1 : Z F ζ hζ)))
    simpa only [map_one] using hcat
  exact continuous_of_continuousAt_one fM hcont1

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
