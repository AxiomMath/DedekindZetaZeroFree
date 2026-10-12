module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterCharacterData

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterModulus
noncomputable section
set_option autoImplicit false

theorem raw_torus_local_ratio (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (x : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : KPGlobalTorusFunctionData.E F ζ hζ)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) = t.val)
    (v : KPHilbert.Place F) :
    ∃ h : IsUnit ((x v).g 0 0) ∧ IsUnit ((x v).g 1 1),
      h.1.unit * h.2.unit⁻¹ =
        KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ t) := by
  classical
  set A : KPAdelicCoverRestrictedProduct.AdelicGL2 F :=
    KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x with hA

  have hpgl : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A := by
    rw [hA, ← hx]
    simp only [KPAdelicCoverRestrictedProduct.pglProjection,
      KPAdelicCoverRestrictedProduct.scalarQuotient,
      KPAdelicCoverRestrictedProduct.projection_amalgamation,
      QuotientGroup.mk'_apply, QuotientGroup.lift_mk', MonoidHom.comp_apply]

  obtain ⟨B, hB, hB10, hB01⟩ := t.property
  have hAB : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B := by
    rw [← hpgl, hB]

  obtain ⟨z, hz, hzA⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := KPAdelicCoverRestrictedProduct.scalarSubgroup F)).mp hAB
  obtain ⟨s, rfl⟩ := hz
  have hA10 : A 1 0 = 0 := by
    have h1 : (A : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 1 0 *
        (s : KPAdelicCoverRestrictedProduct.Adeles F) = 0 := by
      have h := congrArg (fun M : KPAdelicCoverRestrictedProduct.AdelicGL2 F =>
        (M : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 1 0) hzA
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
        hB10, mul_zero, add_zero, zero_add, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h
      simpa using h
    exact (IsUnit.mul_left_eq_zero ⟨s, rfl⟩).mp h1
  have hA01 : A 0 1 = 0 := by
    have h1 : (A : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 0 1 *
        (s : KPAdelicCoverRestrictedProduct.Adeles F) = 0 := by
      have h := congrArg (fun M : KPAdelicCoverRestrictedProduct.AdelicGL2 F =>
        (M : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 0 1) hzA
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
        hB01, mul_zero, add_zero, zero_add, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h
      simpa using h
    exact (IsUnit.mul_left_eq_zero ⟨s, rfl⟩).mp h1

  let ot : KPGlobalTorusFunctionData.ordinaryTorus F :=
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val, t.property⟩
  have hp_eq : KPGlobalTorusFunctionData.p F ζ hζ t =
      KPGlobalTorusFunctionData.torusRatio F ot := by
    simp only [KPGlobalTorusFunctionData.p, MonoidHom.comp_apply]
    congr 1
  let D : IsUnit (A 0 0) ∧ IsUnit (A 1 1) :=
    KPGlobalTorusFunctionData.diagonal_entries_units F A hA10 hA01
  have hratio : (KPGlobalTorusFunctionData.torusRatio F ot :
      KPAdelicCoverRestrictedProduct.Adeles F) = ↑D.1.unit * ↑D.2.unit⁻¹ :=
    KPGlobalTorusFunctionData.ratio_formula F ot A hpgl.symm hA10 hA01
  have hratio' : KPGlobalTorusFunctionData.torusRatio F ot = D.1.unit * D.2.unit⁻¹ := by
    apply Units.ext
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val] using hratio
  let u0 : (KPHilbert.Completion F v)ˣ :=
    Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v :
      KPAdelicCoverRestrictedProduct.Adeles F →* KPHilbert.Completion F v) D.1.unit
  let u1 : (KPHilbert.Completion F v)ˣ :=
    Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v :
      KPAdelicCoverRestrictedProduct.Adeles F →* KPHilbert.Completion F v) D.2.unit
  have hkey : KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ t) =
      u0 * u1⁻¹ := by
    show Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v :
        KPAdelicCoverRestrictedProduct.Adeles F →* KPHilbert.Completion F v)
      (KPGlobalTorusFunctionData.p F ζ hζ t) = _
    rw [hp_eq, hratio']
    simp only [map_mul, map_inv]
    rfl

  have hentry (i j : Fin 2) :
      (x v).g i j = KPAdelicCoverRestrictedProduct.adeleEval F v (A i j) := by
    have h1 : KPAdelicCoverRestrictedProduct.matrixEval F v A = (x v).g := by
      rw [hA, KPAdelicCoverRestrictedProduct.restrictedProjection_eval]
      rfl
    rw [← h1]
    simp only [KPAdelicCoverRestrictedProduct.matrixEval, Matrix.GeneralLinearGroup.map_apply]
  have hval0 : (u0 : KPHilbert.Completion F v) = (x v).g 0 0 := by
    simp only [u0, Units.coe_map, IsUnit.unit_spec]
    exact (hentry 0 0).symm
  have hval1 : (u1 : KPHilbert.Completion F v) = (x v).g 1 1 := by
    simp only [u1, Units.coe_map, IsUnit.unit_spec]
    exact (hentry 1 1).symm
  refine ⟨⟨⟨u0, hval0⟩, ⟨u1, hval1⟩⟩, ?_⟩
  have e0 : (⟨⟨u0, hval0⟩, ⟨u1, hval1⟩⟩ :
      IsUnit ((x v).g 0 0) ∧ IsUnit ((x v).g 1 1)).1.unit = u0 :=
    Units.ext ((IsUnit.unit_spec ⟨u0, hval0⟩).trans hval0.symm)
  have e1 : (⟨⟨u0, hval0⟩, ⟨u1, hval1⟩⟩ :
      IsUnit ((x v).g 0 0) ∧ IsUnit ((x v).g 1 1)).2.unit = u1 :=
    Units.ext ((IsUnit.unit_spec ⟨u1, hval1⟩).trans hval1.symm)
  rw [e0, e1, hkey]

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterModulus
