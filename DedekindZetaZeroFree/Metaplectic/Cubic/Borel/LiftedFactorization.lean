module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Borel.RootLiftRigidity

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.FiniteCentralBorel

open KPRankOneInductionRaw
open IsDedekindDomain NumberField

variable (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))

open scoped Matrix

private lemma diag_ne_zero {A : GL2 F v} (hu : A 1 0 = 0) : A 0 0 ≠ 0 ∧ A 1 1 ≠ 0 := by
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_two] at hdet
  rw [show (A : Matrix (Fin 2) (Fin 2) (LocalField F v)) 1 0 = 0 from hu,
    mul_zero, sub_zero] at hdet
  exact mul_ne_zero_iff.mp hdet
private lemma diagonal_mem (y : (LocalField F v)ˣ) : diagonalElement F v y ∈ diagonalTorus F v := by
  refine ⟨diagonalMatrix F v y, rfl, ?_, ?_⟩ <;>
    simp [diagonalMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]
private lemma ordinary_factor (b : upperBorel F v) :
    ∃ a : LocalField F v, (b : PGL2 F v) = upperRootElement F v a *
      diagonalElement F v (borelRatio F v b) := by
  obtain ⟨A, hA, hu⟩ := b.property
  have h11 := (diag_ne_zero F v hu).2
  let u : (LocalField F v)ˣ := Units.mk0 (A 1 1) h11
  refine ⟨A 0 1 / A 1 1, ?_⟩
  have heq : (upperRootMatrix F v (A 0 1 / A 1 1) *
      diagonalMatrix F v (borelRatio F v b)) * Matrix.GeneralLinearGroup.scalar (Fin 2) u = A := by
    apply Units.ext
    ext i j
    rw [Units.val_mul, Units.val_mul]
    simp only [Matrix.GeneralLinearGroup.coe_scalar]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [upperRootMatrix, diagonalMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
        u, borelRatio_eq F v b A hA hu, hu, h11]
  rw [← hA]
  unfold upperRootElement diagonalElement
  rw [← map_mul]
  exact (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr ⟨u, heq⟩ |>.symm
private lemma root_in_torus_zero (x : LocalField F v)
    (h : upperRootElement F v x ∈ diagonalTorus F v) : x = 0 := by
  obtain ⟨A, hA, hu, hv⟩ := h
  obtain ⟨u, heq⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hA
  have he := congrArg (fun B : GL2 F v => B 0 1) heq
  simp [upperRootMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, hv] at he
  exact he.symm

theorem exists_unique_lifted_factorization
    {G : Type*} [Group G] (π : G →* PGL2 F v)
    (n : Multiplicative (LocalField F v) →* G)
    (hn : ∀ x, π (n x) = ordinaryUpperRootHom F v x)
    (b : G) (hb : π b ∈ upperBorel F v) :
    ∃ (a : LocalField F v) (t : G),
      π t ∈ diagonalTorus F v ∧
      b = n (Multiplicative.ofAdd a) * t ∧
      t = n (Multiplicative.ofAdd (-a)) * b ∧
      π t = diagonalElement F v (borelRatio F v ⟨π b, hb⟩) ∧
      (∀ (a' : LocalField F v) (t' : G),
        π t' ∈ diagonalTorus F v →
        b = n (Multiplicative.ofAdd a') * t' → a' = a ∧ t' = t) := by
  obtain ⟨a, ha⟩ := ordinary_factor F v ⟨π b, hb⟩
  change π b = upperRootElement F v a * diagonalElement F v (borelRatio F v ⟨π b, hb⟩) at ha
  let t := n (Multiplicative.ofAdd (-a)) * b
  have hfac : b = n (Multiplicative.ofAdd a) * t := by
    simp [t, ← mul_assoc, ← map_mul]
  have hproj : π t = diagonalElement F v (borelRatio F v ⟨π b, hb⟩) := by
    change π (n (Multiplicative.ofAdd (-a)) * b) = _
    rw [map_mul, hn]
    conv_lhs => rw [ha]
    change ordinaryUpperRootHom F v (Multiplicative.ofAdd (-a)) *
      (ordinaryUpperRootHom F v (Multiplicative.ofAdd a) * _) = _
    simp [← mul_assoc, ← map_mul]
  have ht : π t ∈ diagonalTorus F v := by
    rw [hproj]
    exact diagonal_mem F v _
  refine ⟨a, t, ht, hfac, rfl, hproj, ?_⟩
  intro a' t' ht' hfac'
  have heq : n (Multiplicative.ofAdd (-a')) * n (Multiplicative.ofAdd a) = t' * t⁻¹ := by
    calc
      _ = n (Multiplicative.ofAdd (-a')) * (n (Multiplicative.ofAdd a) * t) * t⁻¹ := by
        simp [mul_assoc]
      _ = n (Multiplicative.ofAdd (-a')) * (n (Multiplicative.ofAdd a') * t') * t⁻¹ := by
        rw [← hfac, hfac']
      _ = _ := by simp [← mul_assoc, ← map_mul]
  have hroot : upperRootElement F v (-a' + a) ∈ diagonalTorus F v := by
    have hm := (diagonalTorus F v).mul_mem ht' ((diagonalTorus F v).inv_mem ht)
    rw [← map_inv, ← map_mul, ← heq, ← map_mul, hn] at hm
    exact hm
  have heqa : a' = a := by
    have hz := root_in_torus_zero F v (-a' + a) hroot
    exact neg_add_eq_zero.mp hz
  refine ⟨heqa, ?_⟩
  subst a'
  exact mul_left_cancel (hfac'.symm.trans hfac)

end DedekindZetaZeroFree.FiniteCentralBorel

end
