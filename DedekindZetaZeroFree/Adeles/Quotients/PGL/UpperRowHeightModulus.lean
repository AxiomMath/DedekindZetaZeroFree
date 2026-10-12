module

public import DedekindZetaZeroFree.Eisenstein.Induction.PGLAdelicRowHeight

@[expose] public section

noncomputable section
open Matrix
open scoped NumberField
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm
private theorem upper_local {K : Type*} [NormedField K]
    (A : GL (Fin 2) K) (h10 : A 1 0 = 0) :
    (‖A 1 1‖ / Real.sqrt ‖(GeneralLinearGroup.det A : K)‖) ^ (-2 : ℤ) =
      ‖A 0 0‖ / ‖A 1 1‖ := by
  have hd : (GeneralLinearGroup.det A : K) = A 0 0 * A 1 1 := by
    simp [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10]
  have hn : (GeneralLinearGroup.det A : K) ≠ 0 := Units.ne_zero _
  have ha : A 0 0 ≠ 0 := by intro h; apply hn; simp [hd, h]
  have hb : A 1 1 ≠ 0 := by intro h; apply hn; simp [hd, h]
  have hdpos : 0 < ‖(GeneralLinearGroup.det A : K)‖ := norm_pos_iff.mpr hn
  have hbpos : 0 < ‖A 1 1‖ := norm_pos_iff.mpr hb
  rw [_root_.zpow_neg, zpow_ofNat]
  have hs := Real.sq_sqrt (le_of_lt hdpos)
  have hsqrt : Real.sqrt ‖(GeneralLinearGroup.det A : K)‖ ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  rw [div_pow, hs, hd, norm_mul]
  field_simp
  <;> ring

variable (F : Type) [Field F] [NumberField F]

theorem finite_row_modulus
    (A : KPChamberHeight.AdelGL F) (h10 : A 1 0 = 0)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (KPChamberHeight.finiteFactor F ![0, 1] A v) ^ (-2 : ℤ) =
      ‖KPChamberHeight.finiteEval F v (A 0 0)‖ /
        ‖KPChamberHeight.finiteEval F v (A 1 1)‖ := by
  let Av := GeneralLinearGroup.map (KPChamberHeight.finiteEval F v) A
  have hv : Av 1 0 = 0 := by
    change KPChamberHeight.finiteEval F v (A 1 0) = 0
    rw [h10, map_zero]
  have he : KPChamberHeight.finiteFactor F ![0, 1] A v =
      ‖Av 1 1‖ / Real.sqrt ‖(GeneralLinearGroup.det Av : v.adicCompletion F)‖ := by
    simp [KPChamberHeight.finiteFactor, KPChamberHeight.rowAction,
      Fin.sum_univ_two, hv, Av, h10]
  rw [he]
  exact upper_local Av hv

theorem infinite_row_modulus
    (A : KPChamberHeight.AdelGL F) (h10 : A 1 0 = 0)
    (v : NumberField.InfinitePlace F) :
    (KPChamberHeight.infiniteFactor F ![0, 1] A v) ^ (-2 : ℤ) =
      (‖KPChamberHeight.infiniteEval F v (A 0 0)‖ /
        ‖KPChamberHeight.infiniteEval F v (A 1 1)‖) ^
          KPChamberHeight.infiniteDegree F v := by
  let Av := GeneralLinearGroup.map (KPChamberHeight.infiniteEval F v) A
  have hv : Av 1 0 = 0 := by
    change KPChamberHeight.infiniteEval F v (A 1 0) = 0
    rw [h10, map_zero]
  have he : KPChamberHeight.infiniteFactor F ![0, 1] A v =
      (‖Av 1 1‖ / Real.sqrt ‖(GeneralLinearGroup.det Av : v.Completion)‖) ^
        KPChamberHeight.infiniteDegree F v := by
    unfold KPChamberHeight.infiniteFactor
    dsimp only
    change (Real.sqrt (‖KPChamberHeight.rowAction
      (fun i => algebraMap F v.Completion (![0, 1] i)) Av 0‖ ^ 2 +
      ‖KPChamberHeight.rowAction
      (fun i => algebraMap F v.Completion (![0, 1] i)) Av 1‖ ^ 2) / _) ^ _ = _
    simp only [KPChamberHeight.rowAction, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      map_zero, map_one, zero_mul, one_mul, zero_add, hv, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_sq (norm_nonneg _)]
    rfl
  rw [he, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
    upper_local Av hv, zpow_natCast]
  rfl

open scoped BigOperators

theorem upper_rowHeight_modulus
    (A : KPChamberHeight.AdelGL F) (h10 : A 1 0 = 0) :
    (KPChamberHeight.rowHeight F ![0, 1] A) ^ (-2 : ℤ) =
      (∏ v : NumberField.InfinitePlace F,
        (‖KPChamberHeight.infiniteEval F v (A 0 0)‖ /
          ‖KPChamberHeight.infiniteEval F v (A 1 1)‖) ^
            KPChamberHeight.infiniteDegree F v) *
      ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        ‖KPChamberHeight.finiteEval F v (A 0 0)‖ /
          ‖KPChamberHeight.finiteEval F v (A 1 1)‖ := by
  have hr : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simpa using this
  have hf : Function.HasFiniteMulSupport (KPChamberHeight.finiteFactor F ![0, 1] A) :=
    Filter.eventually_cofinite.mp
      (KPChamberHeight.finiteFactor_eventually_one F ![0, 1] hr A)
  unfold KPChamberHeight.rowHeight
  rw [mul_zpow, ← Finset.prod_zpow]
  simp_rw [infinite_row_modulus F A h10]
  congr 1
  rw [_root_.zpow_neg, zpow_ofNat, finprod_pow hf, ← finprod_inv_distrib]
  apply finprod_congr
  intro v
  exact finite_row_modulus F A h10 v
end DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm

end
