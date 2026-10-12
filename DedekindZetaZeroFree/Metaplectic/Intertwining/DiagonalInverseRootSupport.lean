module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.DiagonalJacobiansAndUnitWeights

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation

theorem fullDiagonal_lower_row_constraint {K : Type*} [Field K]
    (B k : GL (Fin 2) K) (a p₁ p₂ : Kˣ) (v x : K)
    (hB10 : B 1 0 = 0) (hB11 : B 1 1 ≠ 0) (hk11 : k 1 1 ≠ 0)
    (h : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w K * KubotaRankTwo.n K v * KubotaRankTwo.d K a 1 *
        KPStandardLocalRootLifts.weylSwap K * KubotaRankTwo.n K x) =
      Matrix.ProjGenLinGroup.mk
        (B * KubotaRankTwo.d K p₁ p₂ * k * KPStandardLocalRootLifts.weylSwap K)) :
    v ≠ 0 ∧ x + (a : K) / v = k 1 0 / k 1 1 := by
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h10 := congrArg (fun g : GL (Fin 2) K => g 1 0) hc
  have h11 := congrArg (fun g : GL (Fin 2) K => g 1 1) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.w,
    KubotaRankTwo.n, KubotaRankTwo.d, KPStandardLocalRootLifts.weylSwap,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply,
    hB10] at h10 h11
  have hv : v ≠ 0 := by
    intro hv
    rw [hv, zero_mul] at h10
    exact mul_ne_zero (mul_ne_zero hB11 p₂.ne_zero) hk11 h10.symm
  refine ⟨hv, ?_⟩
  have he : ((a : K) + v * x) * k 1 1 = v * k 1 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hB11 p₂.ne_zero)
    calc
      _ = ((a : K) + v * x) * (B 1 1 * (p₂ : K) * k 1 1) := by ring
      _ = ((a : K) + v * x) * (v * (c : K)) := by rw [h10]
      _ = v * (((a : K) + v * x) * (c : K)) := by ring
      _ = _ := by rw [add_comm (a : K) (v * x), h11]; ring
  apply (eq_div_iff hk11).mpr
  apply mul_left_cancel₀ hv
  calc
    _ = ((a : K) + v * x) * k 1 1 := by field_simp; ring
    _ = _ := he

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem fullDiagonal_actual_support_lower_row
    (π : (LocalField F q)ˣ) (i : Fin 3) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) (v x : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) v *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) m) :
    v ≠ 0 ∧ ∃ k : KPLocalCube.Gamma F q m,
      x + (π ^ i.val : (LocalField F q)ˣ) / v = k.val 1 0 / k.val 1 1 := by
  obtain ⟨b, k, hk, hg⟩ := hg
  obtain ⟨k, rfl⟩ := hk
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition (inBorel F ζ hζ q S P b)
  let B : GL (Fin 2) (LocalField F q) :=
    KubotaRankTwo.d (LocalField F q) (S.borel.coordinate (retractL F ζ hζ q S P b)) 1 *
      KubotaRankTwo.n (LocalField F q) t.toAdd
  have pb : S.borel.projection b.val = Matrix.ProjGenLinGroup.mk B := by
    have he : (inBorel F ζ hζ q S P b).val =
        (S.borel.torus (S.borel.retract (inBorel F ζ hζ q S P b)) : ActualCover F ζ hζ q) *
          (S.borel.upperRoot t : ActualCover F ζ hζ q) := congrArg Subtype.val ht
    change S.borel.projection ((inBorel F ζ hζ q S P b).val) = _
    rw [he, map_mul, S.borel.torus_projection, S.borel.upperRoot_projection, map_mul]
    rfl
  have pa : S.borel.projection (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (LocalField F q) (π ^ (-1 : ℤ)) (π ^ ((i.val : ℤ) + 1))) :=
    (S.openCell P).projection_eq _
  have pe : S.borel.projection (eta F ζ hζ q π i) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1) :=
    (S.openCell P).projection_eq _
  have pw : S.borel.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (LocalField F q)) :=
    (S.openCell P).projection_eq _
  have pn (z : LocalField F q) : S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) z) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) z) :=
    (S.openCell P).projection_eq _
  have pk : S.borel.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val)) = Matrix.ProjGenLinGroup.mk k.val :=
    (S.openCell P).projection_eq _
  have pkw : S.borel.projection (kernelW (LocalField F q) S.borel .minus) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (LocalField F q)) := by
    rw [kernelW, (S.openCell P).weyl_eq, KPRankOneOpenCellKernel.signedWeyl,
      (S.openCell P).projection_eq, KPRankOneOpenCellKernel.signedWeyl_matrix]
  have hp := congrArg S.borel.projection hg
  simp only [map_mul, pb, pa, pe, pw, pn, pk, pkw] at hp
  have hp' : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w (LocalField F q) * KubotaRankTwo.n (LocalField F q) v *
        KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1 *
        KPStandardLocalRootLifts.weylSwap (LocalField F q) * KubotaRankTwo.n (LocalField F q) x) =
      Matrix.ProjGenLinGroup.mk
        (B * KubotaRankTwo.d (LocalField F q) (π ^ (-1 : ℤ)) (π ^ ((i.val : ℤ) + 1)) *
          k.val * KPStandardLocalRootLifts.weylSwap (LocalField F q)) := by
    simpa only [map_mul, mul_assoc] using hp
  have hB10 : B 1 0 = 0 := by simp [B, Matrix.mul_apply, Fin.sum_univ_two]
  have hB11 : B 1 1 ≠ 0 := by simp [B, Matrix.mul_apply, Fin.sum_univ_two]
  have hk11 : k.val 1 1 ≠ 0 := by
    obtain ⟨r, hr⟩ := (hm.2 k.val k.property).1 1
    rw [← hr]
    exact pow_ne_zero _ r.ne_zero
  obtain ⟨hv, he⟩ := fullDiagonal_lower_row_constraint B k.val (π ^ i.val)
    (π ^ (-1 : ℤ)) (π ^ ((i.val : ℤ) + 1)) v x hB10 hB11 hk11 hp'
  exact ⟨hv, k, he⟩

theorem fullDiagonal_actual_support_residual
    (π : (LocalField F q)ˣ) (i : Fin 3) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) (v x : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) v *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) m) :
    v ≠ 0 ∧
      (∃ y : KPLocalCube.LocalIntegers F q,
        y ∈ KPLocalCube.maximalIdeal F q ^ m ∧
          (y : LocalField F q) = x + (π ^ i.val : (LocalField F q)ˣ) / v) ∧
      x + (π ^ i.val : (LocalField F q)ˣ) / v ∈ rootLevelSet F ζ hζ q m := by
  obtain ⟨hv, k, hk⟩ := fullDiagonal_actual_support_lower_row F ζ hζ q S P π i m hm v x hg
  obtain ⟨k₀, hk₀, he₀⟩ := k.property
  have hentries := (KPLocalCube.mem_integerCongruence_iff F q m k₀).mp hk₀
  have h11ideal : k₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q ^ m := by
    simpa using hentries 1 1
  have h10ideal : k₀ 1 0 ∈ KPLocalCube.maximalIdeal F q ^ m := by
    simpa using hentries 1 0
  have hisunit : IsUnit (k₀ 1 1) := by
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    have hmem : k₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q :=
      Ideal.pow_le_self (by have := hm.1; omega) h11ideal
    change 1 - k₀ 1 1 ∈ KPLocalCube.maximalIdeal F q
    simpa only [neg_sub] using (KPLocalCube.maximalIdeal F q).neg_mem hmem
  obtain ⟨u, hu⟩ := hisunit
  let y : KPLocalCube.LocalIntegers F q := k₀ 1 0 * (↑u⁻¹)
  have hyideal : y ∈ KPLocalCube.maximalIdeal F q ^ m :=
    (KPLocalCube.maximalIdeal F q ^ m).mul_mem_right _ h10ideal
  have hy : (y : LocalField F q) = x + (π ^ i.val : (LocalField F q)ˣ) / v := by
    rw [hk]
    have hratio : k.val 1 0 / k.val 1 1 =
        (k₀ 1 0 : LocalField F q) / (k₀ 1 1 : LocalField F q) := by
      rw [← he₀]
      rfl
    rw [hratio, ← hu]
    change (k₀ 1 0 : LocalField F q) * ((↑u⁻¹ : KPLocalCube.LocalIntegers F q) : LocalField F q) = _
    have huinv : ((↑u⁻¹ : KPLocalCube.LocalIntegers F q) : LocalField F q) =
        ((u : KPLocalCube.LocalIntegers F q) : LocalField F q)⁻¹ :=
      Units.val_inv_eq_inv_val (Units.map (KPLocalCube.LocalIntegers F q).subtype.toMonoidHom u)
    rw [huinv, div_eq_mul_inv]
  refine ⟨hv, ⟨y, hyideal, hy⟩, ?_⟩
  let n₀ : KPLocalCube.IntegerGL2 F q :=
    ⟨!![1,y;0,1], !![1,-y;0,1], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]⟩
  have hn₀ : n₀ ∈ KPLocalCube.integerCongruence F q m := by
    rw [KPLocalCube.mem_integerCongruence_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [n₀, hyideal]
  have hn : KubotaRankTwo.n (LocalField F q)
      (x + (π ^ i.val : (LocalField F q)ˣ) / v) ∈ KPLocalCube.Gamma F q m := by
    refine ⟨n₀, hn₀, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [n₀, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply,
        KubotaRankTwo.n, hy]
  exact ⟨⟨_, hn⟩, rfl⟩

theorem fullDiagonal_shifted_unit
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (u : (KPTameCompact.O F q)ˣ) (t : KPLocalCube.LocalIntegers F q) :
    ∃ w : (KPTameCompact.O F q)ˣ,
      (KPTameCompact.unitInclusion F q w : LocalField F q) =
        (KPTameCompact.unitInclusion F q u : LocalField F q) +
          (π : LocalField F q) * t := by
  have hp : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (map_lt_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q))).mp
    rw [hπ, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hpt : valuation (LocalField F q) ((π : LocalField F q) * t) < 1 := by
    rw [map_mul]
    have ht : valuation (LocalField F q) (t : LocalField F q) ≤ 1 := t.property
    exact (mul_le_mul_right ht _).trans_lt (by simpa using hp)
  have hu : valuation (LocalField F q)
      (KPTameCompact.unitInclusion F q u : LocalField F q) = 1 :=
    (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit u
  have hw : valuation (LocalField F q)
      ((KPTameCompact.unitInclusion F q u : LocalField F q) +
        (π : LocalField F q) * t) = 1 := by
    rw [(valuation (LocalField F q)).map_add_eq_of_lt_left (hu ▸ hpt), hu]
  let z : KPTameCompact.O F q := ⟨_, hw.le⟩
  have hz : IsUnit z :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation (LocalField F q)))).mpr hw
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, congrArg (fun z : KPTameCompact.O F q => (z : LocalField F q)) hw⟩

theorem fullDiagonal_actual_support_inverse_root_chart
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (i : Fin 3) (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (u : (KPTameCompact.O F q)ˣ) (v : LocalField F q)
    (hg : kernelW (LocalField F q) S.borel .minus *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) v *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q)
          (-(KPTameCompact.unitInclusion F q u : LocalField F q) / π)) ∈
      testSupport F ζ hζ q S P (diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1)) m) :
    ∃ (t : KPLocalCube.LocalIntegers F q) (w : (KPTameCompact.O F q)ˣ),
      (t : LocalField F q) ∈ rootLevelSet F ζ hζ q m ∧
      (KPTameCompact.unitInclusion F q w : LocalField F q) =
        (KPTameCompact.unitInclusion F q u : LocalField F q) + (π : LocalField F q) * t ∧
      v = ((π ^ ((i.val : ℤ) + 1) / KPTameCompact.unitInclusion F q w :
        (LocalField F q)ˣ) : LocalField F q) := by
  obtain ⟨hv, ⟨t, _, ht⟩, hr⟩ := fullDiagonal_actual_support_residual
    F ζ hζ q S P π i m hm v _ hg
  obtain ⟨w, hw⟩ := fullDiagonal_shifted_unit F q π hπ u t
  refine ⟨t, w, ht ▸ hr, hw, ?_⟩
  rw [Units.val_div_eq_div_val, hw, zpow_add, zpow_one, zpow_natCast, Units.val_mul]
  have hd : (KPTameCompact.unitInclusion F q u : LocalField F q) +
      (π : LocalField F q) * t ≠ 0 := by
    rw [← hw]
    exact (KPTameCompact.unitInclusion F q w).ne_zero
  apply (eq_div_iff (by simpa only [mul_comm] using hd)).mpr
  field_simp at ht
  linear_combination ht

end DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps

end
