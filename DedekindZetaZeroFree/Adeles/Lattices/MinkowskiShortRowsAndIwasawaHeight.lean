module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Algebra.Module.ZLattice.Covolume

@[expose] public section

noncomputable section

open Module MeasureTheory

open scoped ENNReal

namespace DedekindZetaZeroFree

namespace CuspShortRows

abbrev Space (d : ℕ) := EuclideanSpace ℂ (Fin d × Fin 2)

end CuspShortRows

end DedekindZetaZeroFree

end

section

noncomputable section

open Module MeasureTheory
open scoped ENNReal

namespace DedekindZetaZeroFree
namespace CuspShortRows

def row (d : ℕ) (r : Space d) (i : Fin d) : Fin 2 → ℂ :=
  fun j => r (i, j)

def rowNormSq (d : ℕ) (r : Space d)
    (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) (i : Fin d) : ℝ :=
  ‖WithLp.toLp 2 (Matrix.vecMul (row d r i) (T i : Matrix (Fin 2) (Fin 2) ℂ))‖ ^ 2

def iwasawaMatrix (z : ℂ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt z.2 : ℝ) : ℂ), z.1 / (Real.sqrt z.2 : ℝ);
      0, 1 / (Real.sqrt z.2 : ℝ)]

theorem iwasawaMatrix_det (z : ℂ × ℝ) (hz : 0 < z.2) :
    (iwasawaMatrix z).det = 1 := by
  have hs : (Real.sqrt z.2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hz))
  simp [iwasawaMatrix, Matrix.det_fin_two, hs]

def iwasawa (z : ℂ × ℝ) (hz : 0 < z.2) :
    Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨iwasawaMatrix z, iwasawaMatrix_det z hz⟩

def height (d : ℕ) (r : Space d)
    (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) : ℝ :=
  (∏ i : Fin d, rowNormSq d r T i)⁻¹

private def linT (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (Fin d × Fin 2 → ℂ) →ₗ[ℂ] (Fin d × Fin 2 → ℂ) where
  toFun r := fun ij => ∑ k, r (ij.1, k) * (T ij.1 : Matrix (Fin 2) (Fin 2) ℂ) k ij.2
  map_add' r s := by
    funext ij
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c r := by
    funext ij
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    ring

private def curT (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (Fin d → Fin 2 → ℂ) →ₗ[ℂ] (Fin d → Fin 2 → ℂ) :=
  (LinearEquiv.curry ℂ ℂ (Fin d) (Fin 2)).conj (linT d T)

private theorem curT_eq (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    curT d T = LinearMap.pi
      (fun i => (Matrix.toLin' ((T i : Matrix (Fin 2) (Fin 2) ℂ).transpose)).comp
        (LinearMap.proj i)) := by
  apply LinearMap.ext
  intro r
  funext i j
  simp only [curT, LinearEquiv.conj_apply_apply, LinearEquiv.coe_curry, LinearEquiv.coe_curry_symm,
    LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, linT,
    LinearMap.pi_apply, LinearMap.proj_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

private theorem det_curT (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    LinearMap.det (curT d T) = 1 := by
  rw [curT_eq, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe]

private def transform (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    Space d →ₗ[ℂ] Space d :=
  (WithLp.linearEquiv 2 ℂ (Fin d × Fin 2 → ℂ)).symm.conj (linT d T)

private theorem transform_apply (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (r : Space d) :
    transform d T r = WithLp.toLp 2
      (fun ij => ∑ k, WithLp.ofLp r (ij.1, k) *
        (T ij.1 : Matrix (Fin 2) (Fin 2) ℂ) k ij.2) := rfl

private theorem transform_det (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    LinearMap.det (transform d T) = 1 := by
  have h1 : LinearMap.det
      ((WithLp.linearEquiv 2 ℂ (Fin d × Fin 2 → ℂ)).symm.conj (linT d T)) =
        LinearMap.det (linT d T) :=
    LinearMap.det_conj (linT d T) (WithLp.linearEquiv 2 ℂ (Fin d × Fin 2 → ℂ)).symm
  rw [transform, h1]
  exact (LinearMap.det_conj (linT d T) (LinearEquiv.curry ℂ ℂ (Fin d) (Fin 2))).symm.trans
    (det_curT d T)

private theorem transform_det_real (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    LinearMap.det ((transform d T).restrictScalars ℝ) = 1 := by
  rw [LinearMap.det_restrictScalars, transform_det]
  simp

private theorem sum_rowNormSq_eq (d : ℕ) (r : Space d)
    (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    ∑ i, rowNormSq d r T i = ‖transform d T r‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowNormSq, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [transform_apply, row, Matrix.vecMul, WithLp.ofLp_toLp]

private theorem rowNormSq_nonneg (d : ℕ) (r : Space d)
    (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ) (i : Fin d) :
    0 ≤ rowNormSq d r T i := by
  rw [rowNormSq]; exact sq_nonneg _

private theorem prod_le_mean_pow {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / (Fintype.card ι : ℝ)) ^ Fintype.card ι := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (1 / (Fintype.card ι : ℝ) : ℝ) :=
    fun i _ => by positivity
  have hw' : ∑ i ∈ (Finset.univ : Finset ι), (1 / (Fintype.card ι : ℝ) : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have key := Real.geom_mean_le_arith_mean_weighted (s := (Finset.univ : Finset ι))
    (fun _ : ι => (1 / (Fintype.card ι : ℝ) : ℝ)) z hw hw' (fun i _ => hz i)
  rw [Real.finsetProd_rpow (Finset.univ : Finset ι) z (fun i _ => hz i), ← Finset.mul_sum] at key
  have key2 : (∏ i, z i) ^ (1 / (Fintype.card ι : ℝ)) ≤ (∑ i, z i) / (Fintype.card ι : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using key
  have hnn : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  have hstep : ((∏ i, z i) ^ (1 / (Fintype.card ι : ℝ))) ^ (Fintype.card ι : ℝ) ≤
      ((∑ i, z i) / (Fintype.card ι : ℝ)) ^ (Fintype.card ι : ℝ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hnn _) key2 (by positivity)
  simpa only [← Real.rpow_mul hnn, one_div_mul_cancel (ne_of_gt hn), Real.rpow_one,
    Real.rpow_natCast] using hstep

end CuspShortRows

theorem kp_cusp_minkowski_short_rows (d : ℕ) (hd : 1 ≤ d)
    (Λ : Submodule ℤ (CuspShortRows.Space d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℂ,
        ∃ r : CuspShortRows.Space d, r ∈ Λ ∧ r ≠ 0 ∧
          (∑ i : Fin d, CuspShortRows.rowNormSq d r T i) ≤ C ∧
          (∏ i : Fin d, CuspShortRows.rowNormSq d r T i) ≤ (C / d) ^ d := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nontrivial (CuspShortRows.Space d) := inferInstance
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Module.finrank ℝ (CuspShortRows.Space d) := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by rw [hn]; exact Module.finrank_pos
  obtain ⟨k, hk⟩ : ∃ k : ℝ,
      k = Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := ⟨_, rfl⟩
  have hkpos : 0 < k := by
    rw [hk]
    exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) n)
      (Real.Gamma_pos_of_pos (by positivity))

  let b := Module.Free.chooseBasis ℤ Λ
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hF : IsAddFundamentalDomain Λ F volume := ZLattice.isAddFundamentalDomain b volume
  have hFfin : volume F ≠ ⊤ := by
    intro htop
    have hzero : volume.real F = 0 := by
      show (volume F).toReal = 0
      rw [htop]; simp
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hF] at hzero
    exact ZLattice.covolume_ne_zero Λ volume hzero
  have hFvol : volume F = ENNReal.ofReal (volume.real F) :=
    (ENNReal.ofReal_toReal hFfin).symm

  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max 1 (volume.real F * 2 ^ n / k + 1) := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR]; exact le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRle : R ≤ R ^ n := by
    simpa using pow_le_pow_right₀ hR1 hn1
  have hRk : volume.real F * 2 ^ n < R ^ n * k := by
    have h1 : volume.real F * 2 ^ n / k + 1 ≤ R := by rw [hR]; exact le_max_right _ _
    have h2 : (volume.real F * 2 ^ n / k + 1) * k ≤ R * k :=
      mul_le_mul_of_nonneg_right h1 hkpos.le
    rw [add_mul, div_mul_cancel₀ _ hkpos.ne', one_mul] at h2
    have h3 : R * k ≤ R ^ n * k := mul_le_mul_of_nonneg_right hRle hkpos.le
    exact lt_of_lt_of_le (lt_add_of_pos_right _ hkpos) (le_trans h2 h3)
  have hball : volume (Metric.ball (0 : CuspShortRows.Space d) R) =
      ENNReal.ofReal (R ^ n * k) := by
    rw [InnerProductSpace.volume_ball]
    simp only [hn, hk]
    rw [← ENNReal.ofReal_pow hRpos.le, ← ENNReal.ofReal_mul (by positivity)]
  refine ⟨R ^ 2, by positivity, fun T => ?_⟩
  have hdet : LinearMap.det ((CuspShortRows.transform d T).restrictScalars ℝ) = 1 :=
    CuspShortRows.transform_det_real d T
  have hdetne : LinearMap.det ((CuspShortRows.transform d T).restrictScalars ℝ) ≠ 0 := by
    rw [hdet]; norm_num
  let s : Set (CuspShortRows.Space d) :=
    ((CuspShortRows.transform d T).restrictScalars ℝ) ⁻¹' Metric.ball 0 R
  have hconv : Convex ℝ s := (convex_ball (0 : CuspShortRows.Space d) R).linear_preimage _
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, Set.mem_preimage, Metric.mem_ball, dist_zero_right, map_neg, norm_neg] at hx ⊢
    exact hx
  have hvol : volume s = volume (Metric.ball (0 : CuspShortRows.Space d) R) := by
    rw [Measure.addHaar_preimage_linearMap volume hdetne, hdet]
    norm_num
  have hpow2 : ENNReal.ofReal ((2 : ℝ) ^ n) = (2 : ℝ≥0∞) ^ n := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hlt : volume F * 2 ^ Module.finrank ℝ (CuspShortRows.Space d) < volume s := by
    rw [← hn, hFvol, hvol, hball, ← hpow2, ← ENNReal.ofReal_mul (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hRk
  haveI : Countable ↥(Λ.toAddSubgroup) := inferInstanceAs (Countable ↥Λ)
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := Λ.toAddSubgroup) (μ := volume) hF hsymm hconv hlt
  have hxs' : ‖(CuspShortRows.transform d T) (x : CuspShortRows.Space d)‖ < R := by
    simpa only [s, Set.mem_preimage, Metric.mem_ball, dist_zero_right,
      LinearMap.coe_restrictScalars] using hxs
  have hsum : (∑ i : Fin d, CuspShortRows.rowNormSq d (x : CuspShortRows.Space d) T i) ≤ R ^ 2 := by
    rw [CuspShortRows.sum_rowNormSq_eq]
    nlinarith [hxs', norm_nonneg ((CuspShortRows.transform d T) (x : CuspShortRows.Space d))]
  refine ⟨(x : CuspShortRows.Space d), x.2, ?_, hsum, ?_⟩
  · intro h
    exact hx0 (Subtype.ext h)
  · refine le_trans (CuspShortRows.prod_le_mean_pow (z := fun i =>
      CuspShortRows.rowNormSq d (x : CuspShortRows.Space d) T i)
      (fun i => CuspShortRows.rowNormSq_nonneg d _ T i)) ?_
    simp only [Fintype.card_fin]
    refine pow_le_pow_left₀ (div_nonneg (Finset.sum_nonneg fun i _ =>
      CuspShortRows.rowNormSq_nonneg d (x : CuspShortRows.Space d) T i)
      (Nat.cast_nonneg d)) ?_ d
    exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg d)

theorem kp_cusp_minkowski_iwasawa_height (d : ℕ) (hd : 1 ≤ d)
    (Λ : Submodule ℤ (CuspShortRows.Space d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ]
    (hnonzero : ∀ r : CuspShortRows.Space d, r ∈ Λ → r ≠ 0 →
      ∀ i : Fin d, CuspShortRows.row d r i ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (z : Fin d → ℂ × ℝ) (hz : ∀ i, 0 < (z i).2),
        ∃ r : CuspShortRows.Space d, r ∈ Λ ∧ r ≠ 0 ∧
          c ≤ CuspShortRows.height d r (fun i => CuspShortRows.iwasawa (z i) (hz i)) := by
  obtain ⟨C, hCpos, hC⟩ := kp_cusp_minkowski_short_rows d hd Λ
  refine ⟨(d / C) ^ d, by positivity, fun z hz => ?_⟩
  obtain ⟨r, hrΛ, hr0, hsum, hprod⟩ := hC fun i => CuspShortRows.iwasawa (z i) (hz i)
  refine ⟨r, hrΛ, hr0, ?_⟩
  have hrow : ∀ i : Fin d, CuspShortRows.row d r i ≠ 0 := hnonzero r hrΛ hr0
  have hpos : 0 < ∏ i : Fin d,
      CuspShortRows.rowNormSq d r (fun i => CuspShortRows.iwasawa (z i) (hz i)) i := by
    refine Finset.prod_pos fun i _ => ?_
    rw [CuspShortRows.rowNormSq]
    refine pow_pos (norm_pos_iff.mpr ?_) 2
    intro hzero
    have hdet : ((CuspShortRows.iwasawa (z i) (hz i) :
        Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
      Matrix.SpecialLinearGroup.det_coe _
    have hsingle : Matrix.vecMul (CuspShortRows.row d r i)
        ((CuspShortRows.iwasawa (z i) (hz i) : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
      have := congrArg WithLp.ofLp hzero
      simpa [WithLp.ofLp_toLp] using this
    have hdet0 : ((CuspShortRows.iwasawa (z i) (hz i) :
        Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = 0 :=
      Matrix.exists_vecMul_eq_zero_iff.mp ⟨CuspShortRows.row d r i, hrow i, hsingle⟩
    rw [hdet] at hdet0
    exact one_ne_zero hdet0
  have hmain : ((C / d) ^ d)⁻¹ ≤ (∏ i : Fin d,
      CuspShortRows.rowNormSq d r (fun i => CuspShortRows.iwasawa (z i) (hz i)) i)⁻¹ :=
    inv_anti₀ hpos hprod
  have heq : ((C / d) ^ d)⁻¹ = (d / C) ^ d := by
    rw [← inv_pow, inv_div]
  rw [CuspShortRows.height, ← heq]
  exact hmain

end DedekindZetaZeroFree

end
end
