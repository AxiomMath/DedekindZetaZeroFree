module

public import DedekindZetaZeroFree.Adeles.Quotients.PGL.UpperRowHeightModulus

@[expose] public section

noncomputable section
open Matrix
open scoped NumberField BigOperators
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm

private theorem bottom_mul {K : Type*} [CommRing K]
    (B C : GL (Fin 2) K) (h10 : B 1 0 = 0) (j : Fin 2) :
    (B * C) 1 j = B 1 1 * C 1 j := by
  change (B.val * C.val) 1 j = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, h10]

private theorem max_row_mul {K : Type*} [NormedField K]
    (B C : GL (Fin 2) K) (h10 : B 1 0 = 0) :
    max ‖(B * C) 1 0‖ ‖(B * C) 1 1‖ /
        Real.sqrt ‖(GeneralLinearGroup.det (B * C) : K)‖ =
      (‖B 1 1‖ / Real.sqrt ‖(GeneralLinearGroup.det B : K)‖) *
      (max ‖C 1 0‖ ‖C 1 1‖ / Real.sqrt ‖(GeneralLinearGroup.det C : K)‖) := by
  rw [bottom_mul B C h10, bottom_mul B C h10, norm_mul, norm_mul,
    ← mul_max_of_nonneg _ _ (norm_nonneg _), map_mul, Units.val_mul, norm_mul,
    Real.sqrt_mul (norm_nonneg _)]
  ring

private theorem euclidean_row_mul {K : Type*} [NormedField K]
    (B C : GL (Fin 2) K) (h10 : B 1 0 = 0) :
    Real.sqrt (‖(B * C) 1 0‖ ^ 2 + ‖(B * C) 1 1‖ ^ 2) /
        Real.sqrt ‖(GeneralLinearGroup.det (B * C) : K)‖ =
      (‖B 1 1‖ / Real.sqrt ‖(GeneralLinearGroup.det B : K)‖) *
      (Real.sqrt (‖C 1 0‖ ^ 2 + ‖C 1 1‖ ^ 2) /
        Real.sqrt ‖(GeneralLinearGroup.det C : K)‖) := by
  rw [bottom_mul B C h10, bottom_mul B C h10, norm_mul, norm_mul]
  have he : (‖B 1 1‖ * ‖C 1 0‖) ^ 2 + (‖B 1 1‖ * ‖C 1 1‖) ^ 2 =
      ‖B 1 1‖ ^ 2 * (‖C 1 0‖ ^ 2 + ‖C 1 1‖ ^ 2) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    map_mul, Units.val_mul, norm_mul, Real.sqrt_mul (norm_nonneg _)]
  ring

variable (F : Type) [Field F] [NumberField F]

theorem finiteFactor_upper_mul (B C : KPChamberHeight.AdelGL F)
    (h10 : B 1 0 = 0)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    KPChamberHeight.finiteFactor F ![0, 1] (B * C) v =
      KPChamberHeight.finiteFactor F ![0, 1] B v *
        KPChamberHeight.finiteFactor F ![0, 1] C v := by
  let Bv := GeneralLinearGroup.map (KPChamberHeight.finiteEval F v) B
  let Cv := GeneralLinearGroup.map (KPChamberHeight.finiteEval F v) C
  have hv : Bv 1 0 = 0 := by
    change KPChamberHeight.finiteEval F v (B 1 0) = 0
    rw [h10, map_zero]
  simpa [KPChamberHeight.finiteFactor, KPChamberHeight.rowAction,
    Fin.sum_univ_two, map_mul, Bv, Cv, h10] using max_row_mul Bv Cv hv

theorem infiniteFactor_upper_mul (B C : KPChamberHeight.AdelGL F)
    (h10 : B 1 0 = 0) (v : NumberField.InfinitePlace F) :
    KPChamberHeight.infiniteFactor F ![0, 1] (B * C) v =
      KPChamberHeight.infiniteFactor F ![0, 1] B v *
        KPChamberHeight.infiniteFactor F ![0, 1] C v := by
  let Bv := GeneralLinearGroup.map (KPChamberHeight.infiniteEval F v) B
  let Cv := GeneralLinearGroup.map (KPChamberHeight.infiniteEval F v) C
  have hv : Bv 1 0 = 0 := by
    change KPChamberHeight.infiniteEval F v (B 1 0) = 0
    rw [h10, map_zero]
  have hrow (A : KPChamberHeight.AdelGL F) :
      KPChamberHeight.infiniteFactor F ![0, 1] A v =
        (Real.sqrt (‖(GeneralLinearGroup.map (KPChamberHeight.infiniteEval F v) A) 1 0‖ ^ 2 +
          ‖(GeneralLinearGroup.map (KPChamberHeight.infiniteEval F v) A) 1 1‖ ^ 2) /
          Real.sqrt ‖(GeneralLinearGroup.det
            (GeneralLinearGroup.map (KPChamberHeight.infiniteEval F v) A) : v.Completion)‖) ^
          KPChamberHeight.infiniteDegree F v := by
    unfold KPChamberHeight.infiniteFactor
    dsimp only
    simp only [KPChamberHeight.rowAction, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      map_zero, map_one, zero_mul, one_mul, zero_add]
  rw [hrow, hrow, hrow, map_mul]
  change _ = (Real.sqrt (‖Bv 1 0‖ ^ 2 + ‖Bv 1 1‖ ^ 2) / _) ^ _ * _
  rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    Real.sqrt_sq (norm_nonneg _), euclidean_row_mul Bv Cv hv, mul_pow]

theorem rowHeight_upper_mul (B C : KPChamberHeight.AdelGL F)
    (h10 : B 1 0 = 0) :
    KPChamberHeight.rowHeight F ![0, 1] (B * C) =
      KPChamberHeight.rowHeight F ![0, 1] B *
        KPChamberHeight.rowHeight F ![0, 1] C := by
  have hr : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simpa using this
  have hf (A : KPChamberHeight.AdelGL F) :
      Function.HasFiniteMulSupport (KPChamberHeight.finiteFactor F ![0, 1] A) :=
    Filter.eventually_cofinite.mp
      (KPChamberHeight.finiteFactor_eventually_one F ![0, 1] hr A)
  unfold KPChamberHeight.rowHeight
  simp_rw [finiteFactor_upper_mul F B C h10, infiniteFactor_upper_mul F B C h10]
  rw [Finset.prod_mul_distrib, finprod_mul_distrib (hf B) (hf C)]
  ring

theorem rowHeight_upper_compact_bounds
    (S : Set (KPChamberHeight.AdelPGL F)) (hS : IsCompact S) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ (B C : KPChamberHeight.AdelGL F), B 1 0 = 0 →
        ProjGenLinGroup.mk C ∈ S →
          m * KPChamberHeight.rowHeight F ![0, 1] B ≤
            KPChamberHeight.rowHeight F ![0, 1] (B * C) ∧
          KPChamberHeight.rowHeight F ![0, 1] (B * C) ≤
            M * KPChamberHeight.rowHeight F ![0, 1] B := by
  have hr : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simpa using this
  let ℓ : KPChamberHeight.Line F := Projectivization.mk F ![0, 1] hr
  obtain ⟨m, M, hm, hmM, hb⟩ := KPChamberHeight.compact_uniform_height F S hS
  let z := KPChamberHeight.height F ℓ 1
  have hz : 0 < z := KPChamberHeight.height_pos F ℓ 1
  refine ⟨m * z, M * z, mul_pos hm hz, mul_le_mul_of_nonneg_right hmM hz.le, ?_⟩
  intro B C h10 hC
  obtain ⟨hl, hu⟩ := hb ℓ (ProjGenLinGroup.mk C) hC
  rw [KPChamberHeight.height_mk F ![0, 1] hr C] at hl hu
  have hB : 0 ≤ KPChamberHeight.rowHeight F ![0, 1] B :=
    (KPChamberHeight.rowHeight_pos F ![0, 1] hr B).le
  rw [rowHeight_upper_mul F B C h10]
  constructor
  · simpa only [z, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hl hB
  · simpa only [z, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hu hB

end DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm

end
