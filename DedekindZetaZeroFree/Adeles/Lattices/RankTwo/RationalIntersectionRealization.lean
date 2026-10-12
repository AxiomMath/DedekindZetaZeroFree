module

public import DedekindZetaZeroFree.Adeles.Approximation.PGL.BoundedCRT
public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.SteinitzClassification

@[expose] public section

open scoped Pointwise nonZeroDivisors NumberField

open IsDedekindDomain NumberField

namespace DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

private theorem counts_nonneg_integral (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0)
    (h : ∀ v, 0 ≤ FractionalIdeal.count F v I) : I ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hI]
  apply finprod_induction (fun J : FractionalIdeal (RingOfIntegers F)⁰ F => J ≤ 1)
  · exact le_rfl
  · intro J J' hJ hJ'
    simpa using mul_le_mul' hJ hJ'
  · intro v
    exact zpow_le_one₀ (bot_lt_iff_ne_bot.mpr
      (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))
      FractionalIdeal.coeIdeal_le_one (h v)
private theorem ideal_le_of_counts (F : Type*) [Field F] [NumberField F]
    (I J : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v, FractionalIdeal.count F v J ≤ FractionalIdeal.count F v I) : I ≤ J := by
  have hi := counts_nonneg_integral F (I * J⁻¹) (mul_ne_zero hI (inv_ne_zero hJ)) (by
    intro v
    rw [FractionalIdeal.count_mul F v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
    exact sub_nonneg.mpr (h v))
  have hh := mul_le_mul_right hi J
  rw [mul_comm J (I * J⁻¹), mul_assoc, inv_mul_cancel₀ hJ, mul_one] at hh
  simpa only [mul_one] using hh

private theorem ideal_mem_counts (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0) (x : F) (hx : x ≠ 0) :
    x ∈ I ↔ ∀ v, FractionalIdeal.count F v I ≤
      -WithZero.log (v.valuation F x) := by
  have hc (v : HeightOneSpectrum (RingOfIntegers F)) :
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton (RingOfIntegers F)⁰ x) =
      -WithZero.log (v.valuation F x) := by
    simpa [coe_toPrincipalIdeal] using IdeleGroup.count_toPrincipalIdeal (Units.mk0 x hx) v
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  constructor
  · intro h v
    rw [← hc]
    exact FractionalIdeal.count_mono F v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) h
  · intro h
    apply ideal_le_of_counts F _ _ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) hI
    intro v
    simpa [hc] using h v

private theorem scalar_intersection (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0)
    (a : FiniteIdeleGroup F) (ha : FiniteIdeleGroup.fractionalIdeal a = Units.mk0 I hI)
    (x : F) :
    x ∈ I ↔ ∀ v, (a v)⁻¹.val * algebraMap F (v.adicCompletion F) x ∈
      v.adicCompletionIntegers F := by
  by_cases hx : x = 0
  · subst x; simp [FractionalIdeal.zero_mem]
  rw [ideal_mem_counts F I hI x hx]
  have hc (v : HeightOneSpectrum (RingOfIntegers F)) :
      FractionalIdeal.count F v I = -WithZero.log (Valued.v (a v).val) := by
    have h := FractionalIdealGroup.count_factorization (FiniteIdeleGroup.valuationVector a) v
    change FractionalIdeal.count F v (FiniteIdeleGroup.fractionalIdeal a).val = _ at h
    simpa [ha, FiniteIdeleGroup.valuationVector_apply, FiniteIdeleGroup.localOrder_apply] using h
  apply forall_congr'
  intro v
  rw [hc, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul]
  rw [show Valued.v (a v)⁻¹.val = (Valued.v (a v).val)⁻¹ by simp]
  change -(Valued.v (a v).val).log ≤ -(v.valuation F x).log ↔
    (Valued.v (a v).val)⁻¹ * Valued.v (WithVal.toVal (v.valuation F) x : v.adicCompletion F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hv : v.valuation F x ≠ 0 := (v.valuation F).ne_zero_iff.mpr hx
  have hav : Valued.v (a v).val ≠ 0 := by simp
  rw [← WithZero.log_le_log (by simp [hav, hv]) one_ne_zero,
    WithZero.log_mul (inv_ne_zero hav) hv, WithZero.log_inv]
  simp only [WithZero.log_one]
  omega

 noncomputable def rankTwoDiagonal (F : Type*) [Field F] [NumberField F]
    (u : (Adeles F)ˣ) : AdelicGL F where
  val := Matrix.diagonal (fun i => if i = 0 then 1 else u.val)
  inv := Matrix.diagonal (fun i => if i = 0 then 1 else u.inv)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp only [Matrix.diagonal_apply_eq, Pi.mul_apply]
      split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, hij]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp only [Matrix.diagonal_apply_eq, Pi.mul_apply]
      split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, hij]

private theorem coordinate_realization (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0) :
    ∃ g : AdelicGL F, ∀ x : F × F,
      x ∈ coordinateLattice (RingOfIntegers F) F 1 I ↔
        diagonalVector F x ∈ g • integralVectors F := by
  obtain ⟨a, ha⟩ := FiniteIdeleGroup.fractionalIdeal_surjective (Units.mk0 I hI)
  let u := IdeleGroup.finiteEquivFiniteAdeleUnits a
  refine ⟨rankTwoDiagonal F u, ?_⟩
  intro x
  change x ∈ coordinateLattice (RingOfIntegers F) F 1 I ↔
    diagonalVector F x ∈ rankTwoDiagonal F u • integralVectors F
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have hd (i : Fin 2) (j : Fin 1) (v : HeightOneSpectrum (RingOfIntegers F)) :
      (((rankTwoDiagonal F u)⁻¹ • diagonalVector F x) i j) v =
      if i = 0 then algebraMap F (v.adicCompletion F) x.1
      else (a v)⁻¹.val * algebraMap F (v.adicCompletion F) x.2 := by
    change ((Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else u.inv) * diagonalVector F x) i j) v = _
    rw [Matrix.diagonal_mul]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ite_true, one_mul, diagonalVector]
      rfl
    · simp only [Fin.isValue, Fin.reduceEq, ite_false, diagonalVector]
      change u.inv v * algebraMap F (v.adicCompletion F) x.2 = _
      rfl
  have hfirst : x.1 ∈ (1 : FractionalIdeal (RingOfIntegers F)⁰ F) ↔
      ∀ v : HeightOneSpectrum (RingOfIntegers F),
        algebraMap F (v.adicCompletion F) x.1 ∈ v.adicCompletionIntegers F := by

    simpa using scalar_intersection F 1 one_ne_zero (1 : FiniteIdeleGroup F) (by simp) x.1
  change (x.1 ∈ (1 : FractionalIdeal (RingOfIntegers F)⁰ F) ∧ x.2 ∈ I) ↔ _
  rw [hfirst, scalar_intersection F I hI a ha x.2]
  constructor
  · rintro ⟨h1, h2⟩ i j v
    rw [hd]
    split_ifs
    · exact h1 v
    · exact h2 v
  · intro h
    change (∀ i j v, (((rankTwoDiagonal F u)⁻¹ • diagonalVector F x) i j) v ∈
      v.adicCompletionIntegers F) at h
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have hh := h 0 0 v
      rw [hd] at hh
      simpa using hh
    · have hh := h 1 0 v
      rw [hd] at hh
      simpa only [Fin.reduceEq, if_false] using hh

 noncomputable def rationalAction (F : Type*) [Field F] (h : RationalGL F) :
    (F × F) ≃ₗ[F] (F × F) :=
  (LinearEquiv.finTwoArrow F F).symm.trans
    ((Matrix.GeneralLinearGroup.toLin h).toLinearEquiv.trans
      (LinearEquiv.finTwoArrow F F))

private theorem diagonal_action (F : Type*) [Field F] [NumberField F]
    (h : RationalGL F) (x : F × F) :
    diagonalVector F (rationalAction F h x) = diagonalGL F h • diagonalVector F x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalVector, rationalAction, diagonalGL,
      Matrix.GeneralLinearGroup.smul_def, Matrix.GeneralLinearGroup.toLin_apply,
      Matrix.mul_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, LinearEquiv.finTwoArrow, finTwoArrowEquiv]

private theorem rationalAction_surjective (F : Type*) [Field F]
    (e : (F × F) ≃ₗ[F] (F × F)) : ∃ h : RationalGL F, rationalAction F h = e := by
  let t := LinearEquiv.finTwoArrow F F
  let u := t.trans (e.trans t.symm)
  let h := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv u)
  refine ⟨h, ?_⟩
  apply LinearEquiv.ext
  intro x
  change t (((Matrix.GeneralLinearGroup.toLin h).toLinearEquiv) (t.symm x)) = e x
  dsimp only [h]
  rw [MulEquiv.apply_symm_apply]
  change t (u (t.symm x)) = e x
  simp [u]

theorem full_lattice_adelic_realization (F : Type*) [Field F] [NumberField F] :
    ∀ M : FullLattice (NumberField.RingOfIntegers F) F,
      ∃ g : AdelicGL F, ∀ x : F × F,
        x ∈ M.val ↔ diagonalVector F x ∈ g • integralVectors F := by
  intro M
  obtain ⟨I, hI, e, he, _⟩ := kp_cusp_rank_two_normal_form (RingOfIntegers F) F M
  obtain ⟨h, hh⟩ := rationalAction_surjective F e
  obtain ⟨g, hg⟩ := coordinate_realization F I hI
  refine ⟨(diagonalGL F h)⁻¹ * g, ?_⟩
  intro x
  have hm : x ∈ M.val ↔ e x ∈ coordinateLattice (RingOfIntegers F) F 1 I := by
    rw [← he]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, heq⟩
      exact e.injective heq ▸ hy
  rw [hm, hg]
  rw [← hh, diagonal_action, mul_smul]
  conv_rhs => rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]

end DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers
