module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterCharacterData

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def torusHom :
    KPGlobalCubicIdelePairing.E F ζ hζ →* KPGlobalTorusFunctionData.E F ζ hζ where
  toFun u := ⟨u.val.1, by
    change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ u.val.1 ∈
      KPGlobalTorusFunctionData.ordinaryTorus F
    have hmem : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ u.val.1 =
        KPGlobalCubicIdelePairing.diagonalPGL F u.val.2 := u.property
    rw [hmem]
    refine ⟨KPGlobalCubicIdelePairing.diagonalMatrix F u.val.2, rfl, ?_, ?_⟩
    · simp [KPGlobalCubicIdelePairing.diagonalMatrix]
    · simp [KPGlobalCubicIdelePairing.diagonalMatrix]⟩
  map_one' := Subtype.ext rfl
  map_mul' u v := Subtype.ext rfl

theorem diagonalPGL_injective :
    Function.Injective (KPGlobalCubicIdelePairing.diagonalPGL F) := by
  intro y y' h
  have h2 := h
  rw [KPGlobalCubicIdelePairing.diagonalPGL, MonoidHom.comp_apply, MonoidHom.comp_apply]
    at h2
  rw [QuotientGroup.mk'_eq_mk'] at h2
  obtain ⟨z, hz, hzy⟩ := h2
  obtain ⟨l, rfl⟩ := hz
  have hzy' : KPGlobalCubicIdelePairing.diagonalMatrix F y *
      Matrix.GeneralLinearGroup.scalar (Fin 2) l =
      KPGlobalCubicIdelePairing.diagonalMatrix F y' := hzy
  have h11 := congrArg (fun A : KPAdelicCoverRestrictedProduct.AdelicGL2 F =>
    (A : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 1 1) hzy'
  have h00 := congrArg (fun A : KPAdelicCoverRestrictedProduct.AdelicGL2 F =>
    (A : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 0 0) hzy'
  simp [KPGlobalCubicIdelePairing.diagonalMatrix, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne] at h11 h00
  rw [h11] at h00
  exact Units.ext (by simpa using h00)

private theorem torusHom_injective : Function.Injective (torusHom F ζ hζ) := by
  intro u v huv
  have h1 : u.val.1 = v.val.1 := congrArg Subtype.val huv
  have hu : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ u.val.1 =
      KPGlobalCubicIdelePairing.diagonalPGL F u.val.2 := u.property
  have hv : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ v.val.1 =
      KPGlobalCubicIdelePairing.diagonalPGL F v.val.2 := v.property
  have h2 : KPGlobalCubicIdelePairing.diagonalPGL F u.val.2 =
      KPGlobalCubicIdelePairing.diagonalPGL F v.val.2 := by
    rw [← hu, h1, hv]
  have h3 : u.val.2 = v.val.2 := diagonalPGL_injective F h2
  exact Subtype.ext (Prod.ext h1 h3)

 def toOrdinary (x : KPGlobalTorusFunctionData.E F ζ hζ) :
    KPGlobalTorusFunctionData.ordinaryTorus F :=
  ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ x.val, x.property⟩

theorem diagonalPGL_torusRatio (t : KPGlobalTorusFunctionData.ordinaryTorus F) :
    KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.torusRatio F t) =
      t.val := by
  let A := Classical.choose t.property
  have hA := Classical.choose_spec t.property
  have h10 : A 1 0 = 0 := hA.2.1
  have h01 : A 0 1 = 0 := hA.2.2
  have hratio : ((KPGlobalTorusFunctionData.torusRatio F t : KPAdelicCoverRestrictedProduct.Ideles F) :
      KPAdelicCoverRestrictedProduct.Adeles F) =
      ((KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit :
        KPAdelicCoverRestrictedProduct.Adeles F) *
      (((KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit⁻¹ :
        (KPAdelicCoverRestrictedProduct.Adeles F)ˣ) :
        KPAdelicCoverRestrictedProduct.Adeles F) :=
    KPGlobalTorusFunctionData.ratio_formula F t A hA.1 h10 h01
  have hmat : KPGlobalCubicIdelePairing.diagonalMatrix F (KPGlobalTorusFunctionData.torusRatio F t) *
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit = A := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        KPGlobalCubicIdelePairing.diagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]
    · rw [← IsUnit.unit_spec (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2]
      rw [hratio, IsUnit.unit_spec
        (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1]
      rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    · rw [h01]
    · rw [h10]
  rw [KPGlobalCubicIdelePairing.diagonalPGL, MonoidHom.comp_apply, ← hA.1]
  rw [QuotientGroup.mk'_eq_mk']
  exact ⟨Matrix.GeneralLinearGroup.scalar (Fin 2)
    (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit,
    ⟨(KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit, rfl⟩, hmat⟩

private theorem torusHom_surjective : Function.Surjective (torusHom F ζ hζ) := by
  intro w
  refine ⟨⟨(w.val, KPGlobalTorusFunctionData.torusRatio F (toOrdinary F ζ hζ w)), ?_⟩, ?_⟩
  · exact (diagonalPGL_torusRatio F (toOrdinary F ζ hζ w)).symm
  · exact Subtype.ext rfl

private theorem p_torusHom (u : KPGlobalCubicIdelePairing.E F ζ hζ) :
    KPGlobalTorusFunctionData.p F ζ hζ (torusHom F ζ hζ u) =
      KPGlobalCubicIdelePairing.torusProjection F ζ hζ u := by
  have h := diagonalPGL_torusRatio F (toOrdinary F ζ hζ (torusHom F ζ hζ u))
  have h1 : KPGlobalTorusFunctionData.p F ζ hζ (torusHom F ζ hζ u) =
      KPGlobalTorusFunctionData.torusRatio F (toOrdinary F ζ hζ (torusHom F ζ hζ u)) :=
    rfl
  rw [h1]
  refine diagonalPGL_injective F (h.trans ?_)
  show KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (torusHom F ζ hζ u).val =
    KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalCubicIdelePairing.torusProjection F ζ hζ u)
  exact u.property

theorem covered_torus_center_eq_cubes :
    Z F ζ hζ = (CubicCharacters.cubes (Ideles F)).comap
      (KPGlobalTorusFunctionData.p F ζ hζ) := by
  ext x
  change x ∈ Subgroup.center (KPGlobalTorusFunctionData.E F ζ hζ) ↔
    KPGlobalTorusFunctionData.p F ζ hζ x ∈
      CubicCharacters.cubes (KPAdelicCoverRestrictedProduct.Ideles F)
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := torusHom_surjective F ζ hζ x
    rw [p_torusHom F ζ hζ u]
    rw [← Subgroup.mem_comap, ← KPGlobalCubicIdelePairing.torus_center F ζ hζ]
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply torusHom_injective F ζ hζ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hx (torusHom F ζ hζ y)
  · intro hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨u, rfl⟩ := torusHom_surjective F ζ hζ x
    obtain ⟨v, rfl⟩ := torusHom_surjective F ζ hζ y
    rw [p_torusHom F ζ hζ u] at hx
    rw [← Subgroup.mem_comap, ← KPGlobalCubicIdelePairing.torus_center F ζ hζ] at hx
    rw [← map_mul, ← map_mul]
    exact congrArg (torusHom F ζ hζ) (Subgroup.mem_center_iff.mp hx v)

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct
