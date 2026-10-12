module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.CubicUnitConjugationOfBruhatTests

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (q : HeightOneSpectrum (𝓞 F))
local notation "K" => LocalField F q
local notation "v" => Sum.inr q
private lemma B1 (y : Kˣ) : KPHilbert.B3 F ζ hζ v 1 y = 1 :=
    KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1 y
private lemma B2 (y : Kˣ) : KPHilbert.B3 F ζ hζ v y 1 = 1 :=
    KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1 y
private lemma A_N (y : Kˣ) (x : K) :
    KPPGLLocalCover.A F ζ hζ v y * KPPGLLocalCover.N F ζ hζ v x =
      KPPGLLocalCover.N F ζ hζ v ((y : K) * x) * KPPGLLocalCover.A F ζ hζ v y := by
  have hm : KubotaRankTwo.d K y 1 * KubotaRankTwo.n K x =
      KubotaRankTwo.n K ((y : K) * x) * KubotaRankTwo.d K y 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.d, KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hs1 : KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.d K y 1) (KubotaRankTwo.n K x) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, B1, B2]
  have hs2 : KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.n K ((y : K) * x)) (KubotaRankTwo.d K y 1) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, B1, B2]
  change KPPGLLocalCover.coverQuotient F ζ hζ v (KPLocalCover.sectionMap F ζ hζ v _) *
    KPPGLLocalCover.coverQuotient F ζ hζ v (KPLocalCover.sectionMap F ζ hζ v _) = _
  rw [← map_mul, KPLocalCover.sectionMap_mul, hs1, map_one, one_mul, hm]
  symm
  change KPPGLLocalCover.coverQuotient F ζ hζ v (KPLocalCover.sectionMap F ζ hζ v _) *
    KPPGLLocalCover.coverQuotient F ζ hζ v (KPLocalCover.sectionMap F ζ hζ v _) = _
  rw [← map_mul, KPLocalCover.sectionMap_mul, hs2, map_one, one_mul]
private lemma w_d (y : Kˣ) : KPStandardLocalRootLifts.weylSwap K * KubotaRankTwo.d K y 1 =
      KPScalarSplitCentral.scalarMatrix F v y *
        (KubotaRankTwo.d K y⁻¹ 1 * KPStandardLocalRootLifts.weylSwap K) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        KPScalarSplitCentral.scalarMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply]
private lemma X_wd (y : Kˣ) :
      KubotaRankTwo.X K (KPStandardLocalRootLifts.weylSwap K * KubotaRankTwo.d K y 1) = y := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.d,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, y.ne_zero]
private lemma X_dw (y : Kˣ) :
      KubotaRankTwo.X K (KubotaRankTwo.d K y 1 * KPStandardLocalRootLifts.weylSwap K) = 1 := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.d,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
private lemma swap_det : KubotaRankTwo.det K (KPStandardLocalRootLifts.weylSwap K) = -1 := by
  apply Units.ext
  simp [KubotaRankTwo.det, KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
private lemma swap_X : KubotaRankTwo.X K (KPStandardLocalRootLifts.weylSwap K) = 1 := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap]
private lemma Bminus (y : Kˣ) : KPHilbert.B3 F ζ hζ v (-1) y = 1 := by
  rw [(KPHilbert.B3_laws F ζ hζ v).2.2.1]
  simp [(KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2]
private lemma sigma_wd (y : Kˣ) :
      KPLocalCover.sigmaTwo F ζ hζ v (KPStandardLocalRootLifts.weylSwap K) (KubotaRankTwo.d K y 1) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_wd,
      B1, B2, swap_X, swap_det]
    have hn : y / (-1 : Kˣ) = -y := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_neg, Units.val_one, div_neg, div_one]
    rw [Bminus F ζ hζ q y, hn, ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 y).2.2]
    simp
private lemma sigma_dw (y : Kˣ) :
      KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.d K y 1) (KPStandardLocalRootLifts.weylSwap K) = 1 := by
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_dw,
      B1, B2, swap_det, (KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2]
private lemma sigma_scalar_dw (y : Kˣ) :
      KPLocalCover.sigmaTwo F ζ hζ v (KPScalarSplitCentral.scalarMatrix F v y)
        (KubotaRankTwo.d K y⁻¹ 1 * KPStandardLocalRootLifts.weylSwap K) = 1 := by
    have hx : KubotaRankTwo.X K (KPScalarSplitCentral.scalarMatrix F v y) = y := by
      apply Units.ext
      simp [KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix,
        Matrix.scalar, Matrix.diagonal_apply]
    have hd : KubotaRankTwo.det K (KPScalarSplitCentral.scalarMatrix F v y) = y^2 := by
      apply Units.ext
      simp [KubotaRankTwo.det, KPScalarSplitCentral.scalarMatrix,
        Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, pow_two]
    have hb : KPHilbert.B3 F ζ hζ v (y ^ 2) y⁻¹ = 1 := by
      rw [KubotaDefectSymbolAlgebra.inv_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1]
      simp only [pow_two, (KPHilbert.B3_laws F ζ hζ v).1,
        ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 y).1, one_mul, inv_one]
    have hb' : KPHilbert.B3 F ζ hζ v (y ^ 2) (y⁻¹ * -1) = 1 := by
      rw [(KPHilbert.B3_laws F ζ hζ v).2.1, hb,
        ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 (y ^ 2)).2.1, one_mul]
    have hn : y⁻¹ * (-1 : Kˣ) = -y⁻¹ := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg, Units.val_one, mul_neg, mul_one]
    rw [hn] at hb'
    simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_dw,
      ← w_d F q y, X_wd, hx, hd, B1, B2, hb, hb', swap_det]
private lemma W_A (y : Kˣ) :
      KPPGLLocalCover.W F ζ hζ v * KPPGLLocalCover.A F ζ hζ v y =
        KPPGLLocalCover.A F ζ hζ v y⁻¹ * KPPGLLocalCover.W F ζ hζ v := by
    have hr : KPStandardLocalRootLifts.W F ζ hζ v * KPStandardLocalRootLifts.A F ζ hζ v y =
        KPScalarSplitCentral.scalarHom F ζ hζ v y *
          (KPStandardLocalRootLifts.A F ζ hζ v y⁻¹ * KPStandardLocalRootLifts.W F ζ hζ v) := by
      rw [KPStandardLocalRootLifts.W, KPStandardLocalRootLifts.A,
        KPStandardLocalRootLifts.A, KPLocalCover.sectionMap_mul, sigma_wd,
        map_one, one_mul, KPLocalCover.sectionMap_mul, sigma_dw, map_one, one_mul]
      change _ = KPLocalCover.sectionMap F ζ hζ v
        (KPScalarSplitCentral.scalarMatrix F v y) * _
      rw [KPLocalCover.sectionMap_mul, sigma_scalar_dw, map_one, one_mul, w_d F q y]
    have he := congrArg (KPPGLLocalCover.coverQuotient F ζ hζ v) hr
    have hs : KPPGLLocalCover.coverQuotient F ζ hζ v
        (KPScalarSplitCentral.scalarHom F ζ hζ v y) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
    simpa only [map_mul, hs, one_mul, KPPGLLocalCover.W, KPPGLLocalCover.A] using he
private lemma cube_A_comm (c a : Kˣ) :
    KPPGLLocalCover.A F ζ hζ v (c^3) * KPPGLLocalCover.A F ζ hζ v a =
      KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.A F ζ hζ v (c^3) := by
  rw [KPPGLLocalCover.A_mul, KPPGLLocalCover.A_mul,
    ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 c a).1,
    ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 a c).2]
  simp [mul_comm]
private lemma cube_A_inv (S : CanonicalFiniteInducingData F ζ hζ q) (c : Kˣ) :
    (KPPGLLocalCover.A F ζ hζ v (c^3))⁻¹ = KPPGLLocalCover.A F ζ hζ v (c⁻¹^3) := by
  rw [← S.cube_actual c, ← S.cube_actual c⁻¹, map_inv]
  rfl
private lemma cube_A_kernelW (S : CanonicalFiniteInducingData F ζ hζ q) (c : Kˣ) :
    KPPGLLocalCover.A F ζ hζ v (c^3) * kernelW K S.borel .minus =
      kernelW K S.borel .minus * KPPGLLocalCover.A F ζ hζ v (c⁻¹^3) := by
  have he := congrArg (fun h : actualTorus F ζ hζ q => (S.borel.torus h : ActualCover F ζ hζ q))
    (congrArg (fun z : S.heisenberg.C => (z : actualTorus F ζ hζ q)) (S.borel.weyl_cube c))
  rw [S.borel.weylCenter_coe, S.borel.weyl_from_lift,
    S.torus_full, S.torus_full, S.cube_actual, S.cube_actual] at he
  change KPPGLLocalCover.A F ζ hζ v (c^3) * S.borel.liftedW =
    S.borel.liftedW * KPPGLLocalCover.A F ζ hζ v (c⁻¹^3)
  rw [← he]
  group
set_option maxHeartbeats 1200000 in
private lemma word_identity (S : CanonicalFiniteInducingData F ζ hζ q)
    (a c : Kˣ) (u x : K) :
    KPPGLLocalCover.A F ζ hζ v (c^3) *
      (kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v u *
        (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
          KPPGLLocalCover.N F ζ hζ v x)) *
      (KPPGLLocalCover.A F ζ hζ v (c^3))⁻¹ =
    kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v ((c⁻¹^3 : Kˣ) * u) *
      (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
        KPPGLLocalCover.N F ζ hζ v ((c^3 : Kˣ) * x)) := by
  let T := KPPGLLocalCover.A F ζ hζ v (c^3)
  let w := kernelW K S.borel .minus
  let N := KPPGLLocalCover.N F ζ hζ v
  let b := KPPGLLocalCover.A F ζ hζ v a
  let W := KPPGLLocalCover.W F ζ hζ v
  have hkw : T * w = w * T⁻¹ := by
    dsimp only [T, w]
    rw [cube_A_inv F ζ hζ q S c]
    exact cube_A_kernelW F ζ hζ q S c
  have hn : T⁻¹ * N u = N ((c⁻¹^3 : Kˣ) * u) * T⁻¹ := by
    dsimp only [T, N]
    rw [cube_A_inv F ζ hζ q S c]
    exact A_N F ζ hζ q (c⁻¹^3) u
  have hb : T⁻¹ * b = b * T⁻¹ := by
    dsimp only [T, b]
    rw [cube_A_inv F ζ hζ q S c]
    exact cube_A_comm F ζ hζ q c⁻¹ a
  have hw : T⁻¹ * W = W * T := by
    have h := W_A F ζ hζ q (c^3)
    change W * T = KPPGLLocalCover.A F ζ hζ v ((c^3)⁻¹) * W at h
    rw [← inv_pow, ← cube_A_inv F ζ hζ q S c] at h
    exact h.symm
  have hn' : T * N x = N ((c^3 : Kˣ) * x) * T := A_N F ζ hζ q (c^3) x
  change T * (w * N u * (b * W * N x)) * T⁻¹ = w * N _ * (b * W * N _)
  calc
    T * (w * N u * (b * W * N x)) * T⁻¹ = (T * w) * N u * b * W * N x * T⁻¹ := by group
    _ = w * (T⁻¹ * N u) * b * W * N x * T⁻¹ := by rw [hkw]; group
    _ = w * N ((c⁻¹^3 : Kˣ) * u) * (T⁻¹ * b) * W * N x * T⁻¹ := by rw [hn]; group
    _ = w * N ((c⁻¹^3 : Kˣ) * u) * b * (T⁻¹ * W) * N x * T⁻¹ := by rw [hb]; group
    _ = w * N ((c⁻¹^3 : Kˣ) * u) * b * W * (T * N x) * T⁻¹ := by rw [hw]; group
    _ = w * N ((c⁻¹^3 : Kˣ) * u) * (b * W * N ((c^3 : Kˣ) * x)) := by rw [hn']; group

variable (S : CanonicalFiniteInducingData F ζ hζ q)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]

set_option maxHeartbeats 1200000 in

theorem reverse_integral_cubic_unit_change_variable
    (a : (LocalField F q)ˣ) (c : (LocalField F q)ˣ)
    (hc : localAbs (LocalField F q) c = 1)
    (φ : ActualCover F ζ hζ q → ℂ)
    (hφ : ∀ g : ActualCover F ζ hζ q,
      φ (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3) * g *
        (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (c ^ 3))⁻¹) = φ g)
    (x : LocalField F q) :
    (∫ u : LocalField F q,
      φ (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (KPPGLLocalCover.A F ζ hζ (Sum.inr q) a *
          KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) ((c ^ 3 : (LocalField F q)ˣ) * x))) ∂μ) =
    (∫ u : LocalField F q,
      φ (kernelW (LocalField F q) S.borel .minus *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) u *
        (KPPGLLocalCover.A F ζ hζ (Sum.inr q) a *
          KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) ∂μ) := by
  let d : Kˣ := c⁻¹ ^ 3
  have hci : localAbs K c⁻¹ = 1 := by
    have h := localAbs_mul K c c⁻¹
    simpa only [mul_inv_cancel, localAbs_one, hc, one_mul] using h.symm
  have hd : localAbs K d = 1 := by
    dsimp only [d]
    simp only [pow_succ, pow_zero, localAbs_mul, localAbs_one, hci, one_mul]
  have habs : KPCubicHaar.abs K (d : K) = 1 := by
    have he : localAbs K d = KPCubicHaar.abs K (d : K) := by
      simp only [localAbs, KPCubicHaar.abs, if_neg d.ne_zero, Real.rpow_intCast]
      rfl
    rw [← he, hd]
  let e : K ≃ᵐ K :=
    { toEquiv :=
        { toFun := fun u => (d : K) * u
          invFun := fun u => (d⁻¹ : Kˣ) * u
          left_inv := by intro u; simp [mul_assoc]
          right_inv := by intro u; simp [mul_assoc] }
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }
  have hmap : Measure.map e μ = μ := by
    change Measure.map (fun u : K => (d : K) * u) μ = μ
    rw [NonarchimedeanHaarScaling.map_mul K μ (d : K) d.ne_zero, habs]
    simp
  let H : K → ℂ := fun u =>
    φ (kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v u *
      (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
        KPPGLLocalCover.N F ζ hζ v ((c^3 : Kˣ) * x)))
  have hp (u : K) : H (e u) =
    φ (kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v u *
      (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
        KPPGLLocalCover.N F ζ hζ v x)) := by
    dsimp only [H]
    change φ (kernelW K S.borel .minus * KPPGLLocalCover.N F ζ hζ v ((c⁻¹^3 : Kˣ) * u) *
      (KPPGLLocalCover.A F ζ hζ v a * KPPGLLocalCover.W F ζ hζ v *
        KPPGLLocalCover.N F ζ hζ v ((c^3 : Kˣ) * x))) = _
    rw [← word_identity F ζ hζ q S a c u x]
    exact hφ _
  change (∫ u : K, H u ∂μ) = _
  calc
    (∫ u : K, H u ∂μ) = ∫ u : K, H (e u) ∂μ := by
      conv_lhs => rw [← hmap]
      exact integral_map_equiv e H
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hp)

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (q : HeightOneSpectrum (𝓞 F))

private theorem valuation_norm_le (x y : LocalField F q) :
    valuation (LocalField F q) x ≤ valuation (LocalField F q) y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← Valuation.Compatible.vle_iff_le]
  change Valued.v x ≤ Valued.v y ↔ _
  exact (Valued.toNormedField.norm_le_iff).symm
private theorem ball_norm (π : (LocalField F q)ˣ) (r : ℕ) (x : LocalField F q) :
    x ∈ expandingBall F q π r ↔ ‖x‖ ≤ ‖(π : LocalField F q)‖⁻¹ ^ r := by
  let a : LocalField F q := ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (π ^ r).ne_zero
  have hn : ‖a‖ = ‖(π : LocalField F q)‖⁻¹ ^ r := by
    simp [a, norm_inv, norm_pow, inv_pow]
  have hm : ∀ y : LocalField F q, y ∈ (valuation (LocalField F q)).integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← map_one (valuation (LocalField F q)), valuation_norm_le]
    simp
  change (∃ u : (valuation (LocalField F q)).integer, x = a * (u : LocalField F q)) ↔ _
  rw [← hn]
  constructor
  · rintro ⟨u, rfl⟩
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((hm _).mp u.property)
  · intro hx
    refine ⟨⟨x / a, (hm _).mpr ?_⟩, (mul_div_cancel₀ x ha).symm⟩
    rw [norm_div, div_le_one (norm_pos_iff.mpr ha)]
    exact hx

theorem high_shell_translation_is_cubic_unit_multiple
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (r : ℕ) (hr : 2 ≤ r)
    (x : LocalField F q)
    (hx : x ∈ expandingBall F q π r \ expandingBall F q π (r - 1))
    (t : LocalField F q) (ht : t ∈ expandingBall F q π 1) :
    ∃ c : (LocalField F q)ˣ, localAbs (LocalField F q) c = 1 ∧
      x + t = (c ^ 3 : (LocalField F q)ˣ) * x := by
  have hv : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  have hp : 0 < ‖(π : LocalField F q)‖ := norm_pos_iff.mpr π.ne_zero
  have hp1 : ‖(π : LocalField F q)‖ < 1 := by
    have h := not_le.mpr hv
    rw [← map_one (valuation (LocalField F q)), valuation_norm_le] at h
    simpa using not_le.mp h
  have hb : 1 ≤ ‖(π : LocalField F q)‖⁻¹ := le_of_lt ((one_lt_inv₀ hp).mpr hp1)
  have hxt : ‖t‖ < ‖x‖ := by
    have hxn : ‖(π : LocalField F q)‖⁻¹ ^ (r - 1) < ‖x‖ :=
      lt_of_not_ge (fun h => hx.2 ((ball_norm F q π (r-1) x).mpr h))
    have htn : ‖t‖ ≤ ‖(π : LocalField F q)‖⁻¹ := by
      simpa using (ball_norm F q π 1 t).mp ht
    exact lt_of_le_of_lt (htn.trans (by
      simpa using pow_le_pow_right₀ hb (show 1 ≤ r - 1 by omega))) hxn
  have hx0 : x ≠ 0 := by
    intro h
    exact (not_lt_of_ge (norm_nonneg t)) (by simpa [h] using hxt)
  have hy : valuation (LocalField F q) (t / x) < 1 := by
    have hn : ‖t / x‖ < ‖(1 : LocalField F q)‖ := by
      rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr hx0)]
      exact hxt
    have h := not_le.mpr hn
    rw [← valuation_norm_le] at h
    simpa using not_le.mp h
  let z : KPTameCompact.O F q := ⟨1 + t / x, by
    rw [Valuation.mem_integer_iff]
    exact le_of_eq ((valuation (LocalField F q)).map_one_add_of_lt hy)⟩
  have hz : valuation (LocalField F q) (z : LocalField F q) = 1 :=
    (valuation (LocalField F q)).map_one_add_of_lt hy
  letI : HenselianRing (KPTameCompact.O F q) (KPTameCompact.p F q) :=
    (LocalFieldTheory.localCompleteDVF (LocalField F q)).henselianRing
  let Q := Ideal.Quotient.mk (KPTameCompact.p F q)
  have heq : Q z = 1 := by
    have hm : z - 1 ∈ KPTameCompact.p F q := by
      change z - 1 ∈ IsLocalRing.maximalIdeal (KPTameCompact.O F q)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      simpa [z] using hy
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    exact sub_eq_zero.mp (by simpa [map_sub, Q] using h)
  let P : Polynomial (KPTameCompact.O F q) := Polynomial.X ^ 3 - Polynomial.C z
  have hm : P.Monic := by
    exact Polynomial.monic_X_pow_sub_C z (by decide)
  have he : P.eval 1 ∈ KPTameCompact.p F q := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Q (P.eval 1) = 0
    simp [P, heq]
  have hthree : IsUnit (3 : KPTameCompact.O F q) := by
    letI : Nontrivial (KPTameCompact.O F q ⧸ KPTameCompact.p F q) :=
      Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (KPTameCompact.O F q)).ne_top
    letI : (KPTameCompact.p F q).IsMaximal := IsLocalRing.maximalIdeal.isMaximal (KPTameCompact.O F q)
    letI : IsLocalHom Q := IsLocalHom.of_surjective Q Ideal.Quotient.mk_surjective
    apply isUnit_of_map_unit Q
    letI : Field (KPTameCompact.O F q ⧸ KPTameCompact.p F q) := Ideal.Quotient.field (KPTameCompact.p F q)
    apply isUnit_iff_ne_zero.mpr
    simpa only [Q, map_ofNat, Nat.cast_ofNat] using
      CharP.cast_ne_zero_of_ne_of_prime (KPTameCompact.O F q ⧸ KPTameCompact.p F q) Nat.prime_three htame
  have hd : IsUnit (Q (P.derivative.eval 1)) := by
    have h : P.derivative.eval 1 = (3 : KPTameCompact.O F q) := by
      simp [P, Polynomial.derivative_sub, Polynomial.derivative_pow]
    rw [h]
    exact hthree.map Q
  obtain ⟨w, hw, hwp⟩ := HenselianRing.is_henselian P hm 1 he hd
  have hw3 : w ^ 3 = z := by
    simpa only [Polynomial.IsRoot, P, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hw
  have hwf : (w : LocalField F q) ^ 3 = (z : LocalField F q) :=
    congrArg (fun a : KPTameCompact.O F q => (a : LocalField F q)) hw3
  have hwv : valuation (LocalField F q) (w : LocalField F q) = 1 := by
    have h : valuation (LocalField F q) (w : LocalField F q) ^ 3 = 1 := by
      rw [← map_pow, hwf, hz]
    exact (pow_eq_one_iff_of_nonneg (zero_le : 0 ≤ valuation (LocalField F q) (w : LocalField F q)) (by decide : (3 : ℕ) ≠ 0)).mp h
  have hw0 : (w : LocalField F q) ≠ 0 := by
    intro h
    simpa [h] using hwv
  refine ⟨Units.mk0 (w : LocalField F q) hw0, ?_, ?_⟩
  · simp [localAbs, hwv]
  · change x + t = (w : LocalField F q) ^ 3 * x
    rw [hwf]
    change x + t = (1 + t / x) * x
    field_simp

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (coordinates : ∀ ε : Sign,
    sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε)
  (hcoordinates : ∀ ε f g, (coordinates ε f).val g = (f.val g).val 1)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ξ : (valuation (LocalField F q)).integer) (hξ : IsPrimitiveRoot ξ 3)

theorem deformedTest_vector_value
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ)
    (g : ActualCover F ζ hζ q) :
    (deformedTest F ζ hζ q S P hP coordinates f s).val g =
      normPower (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
        (sourceParameter .minus s) •
        ((coordinates .minus).symm f).val g := by
  let f₀ := (coordinates .minus).symm f
  have hc := f₀.property.1 (S.iwasawa.borelPart g)
    (S.iwasawa.compactPart g : ActualCover F ζ hζ q)
  rw [← S.iwasawa.decomposition g] at hc
  change inducingAction S.borel P .minus (sourceParameter .minus s)
    (S.iwasawa.borelPart g)
    (f₀.val (S.iwasawa.compactPart g : ActualCover F ζ hζ q)) = _
  rw [hc]
  change (deltaHalf S.borel (S.iwasawa.borelPart g) *
    normPower (LocalField F q) _ (sourceParameter .minus s)) •
    ((borelAction S.borel P .minus (S.iwasawa.borelPart g)) _) =
    _ • ((deltaHalf S.borel (S.iwasawa.borelPart g) *
      normPower (LocalField F q) _ 0) • _)
  simp only [normPower, zero_mul, Complex.exp_zero, mul_one, smul_smul]
  congr 1
  ring

include hcoordinates in

theorem deformedTest_scalar_value
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ)
    (g : ActualCover F ζ hζ q) :
    ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1 =
      normPower (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
        (sourceParameter .minus s) * f.val g := by
  rw [deformedTest_vector_value]
  change _ * (((coordinates .minus).symm f).val g).val 1 = _
  have hc := hcoordinates .minus ((coordinates .minus).symm f) g
  rw [LinearEquiv.apply_symm_apply] at hc
  rw [← hc]

include hcoordinates in

theorem deformedTest_scalar_support
    (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ) :
    Function.support (fun g =>
      ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1) =
      Function.support f.val := by
  ext g
  rw [Function.mem_support, Function.mem_support, deformedTest_scalar_value
    F ζ hζ q S P hP coordinates hcoordinates]
  have hn : normPower (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
      (sourceParameter .minus s) ≠ 0 := Complex.exp_ne_zero _
  simp only [ne_eq, mul_eq_zero, hn, false_or]

include hcoordinates in

theorem deformedTest_support_of_minusTest
    (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f) (s : ℂ) :
    Function.support (fun g =>
      ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1) ⊆
      testSupport F ζ hζ q S P a m := by
  rw [deformedTest_scalar_support F ζ hζ q S P hP coordinates hcoordinates]
  exact hf.2.1

theorem iwasawa_norm_right_compact
    (g : ActualCover F ζ hζ q)
    (k : S.iwasawa.compact.toOpenSubgroup) :
    localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (g * k)))) =
    localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g))) := by
  let b : S.borel.B :=
    (S.iwasawa.borelPart (g * k))⁻¹ * S.iwasawa.borelPart g
  have he : (b : ActualCover F ζ hζ q) =
      (S.iwasawa.compactPart (g * k) : ActualCover F ζ hζ q) *
        (k : ActualCover F ζ hζ q)⁻¹ *
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹ := by
    have h₁ := S.iwasawa.decomposition g
    have h₂ := S.iwasawa.decomposition (g * k)
    dsimp [b]
    conv at h₂ => lhs; lhs; rw [h₁]
    have hh := congrArg (fun z : ActualCover F ζ hζ q =>
      (S.iwasawa.borelPart (g * k) : ActualCover F ζ hζ q)⁻¹ * z *
        (k : ActualCover F ζ hζ q)⁻¹ *
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹) h₂
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh
  have hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    rw [he]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem
      (S.iwasawa.compact.toOpenSubgroup.mul_mem
        (S.iwasawa.compactPart _).property
        (S.iwasawa.compact.toOpenSubgroup.inv_mem k.property))
      (S.iwasawa.compact.toOpenSubgroup.inv_mem (S.iwasawa.compactPart _).property)
  have hn := S.iwasawa.intersection_norm b hb
  have hprod : S.iwasawa.borelPart (g * k) * b = S.iwasawa.borelPart g := by
    dsimp [b]
    group
  have ha := congrArg (fun c : S.borel.B =>
    localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract c))) hprod
  simpa only [map_mul, localAbs_mul, hn, mul_one] using ha

theorem minusTest_bruhat_value
    (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f)
    (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q)
    (hk : (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m) :
    f.val (b * a * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      chi F ζ hζ q S P hP .minus b := by
  let w := KPPGLLocalCover.W F ζ hζ (Sum.inr q)
  have hfixed := congrArg
    (fun v : scalarSections F ζ hζ q S P hP .minus => v.val (a * w))
    (hf.1 (w⁻¹ * k * w) hk)
  change f.val ((a * w) * (w⁻¹ * k * w)) = f.val (a * w) at hfixed
  have he : (a * w) * (w⁻¹ * k * w) = a * k * w := by group
  rw [he, hf.2.2] at hfixed
  change f.val ((b : ActualCover F ζ hζ q) * a * k * w) = _
  rw [show (b : ActualCover F ζ hζ q) * a * k * w =
      (b : ActualCover F ζ hζ q) * (a * k * w) by group,
    f.property.1, hfixed, mul_one]

include hcoordinates in

theorem deformedTest_bruhat_scalar_value
    (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f)
    (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q)
    (hk : (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m)
    (s : ℂ) :
    let g := b * a * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)
    ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1 =
      normPower (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)))
        (sourceParameter .minus s) * chi F ζ hζ q S P hP .minus b := by
  dsimp only
  rw [deformedTest_scalar_value F ζ hζ q S P hP coordinates hcoordinates,
    minusTest_bruhat_value F ζ hζ q S P hP a m f hf b k hk]

theorem iwasawa_norm_left_borel
    (c : S.borel.B) (g : ActualCover F ζ hζ q) :
    localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (c * g)))) =
    localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract c)) *
      localAbs (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g))) := by
  let b : S.borel.B :=
    (S.iwasawa.borelPart (c * g))⁻¹ * c * S.iwasawa.borelPart g
  have he : (b : ActualCover F ζ hζ q) =
      (S.iwasawa.compactPart (c * g) : ActualCover F ζ hζ q) *
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹ := by
    have h₁ := S.iwasawa.decomposition g
    have h₂ := S.iwasawa.decomposition (c * g)
    dsimp [b]
    conv at h₂ => lhs; rhs; rw [h₁]
    have hh := congrArg (fun z : ActualCover F ζ hζ q =>
      (S.iwasawa.borelPart (c * g) : ActualCover F ζ hζ q)⁻¹ * z *
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q)⁻¹) h₂
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh
  have hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    rw [he]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem
      (S.iwasawa.compactPart _).property
      (S.iwasawa.compact.toOpenSubgroup.inv_mem (S.iwasawa.compactPart _).property)
  have hn := S.iwasawa.intersection_norm b hb
  have hprod : S.iwasawa.borelPart (c * g) * b = c * S.iwasawa.borelPart g := by
    dsimp [b]
    group
  have ha := congrArg (fun d : S.borel.B =>
    localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract d))) hprod
  simpa only [map_mul, localAbs_mul, hn, mul_one] using ha

include hcoordinates in

theorem deformedTest_scalar_borel_covariance
    (f : scalarSections F ζ hζ q S P hP .minus)
    (b : BL F ζ hζ q S P) (s : ℂ) (g : ActualCover F ζ hζ q) :
    ((deformedTest F ζ hζ q S P hP coordinates f s).val (b * g)).val 1 =
      (chi F ζ hζ q S P hP .minus b *
        normPower (LocalField F q)
          (S.borel.coordinate (S.borel.retract (inBorel F ζ hζ q S P b)))
          (sourceParameter .minus s)) *
        ((deformedTest F ζ hζ q S P hP coordinates f s).val g).val 1 := by
  rw [deformedTest_scalar_value F ζ hζ q S P hP coordinates hcoordinates,
    deformedTest_scalar_value F ζ hζ q S P hP coordinates hcoordinates,
    f.property.1]
  have hn := iwasawa_norm_left_borel F ζ hζ q S
    (inBorel F ζ hζ q S P b) g
  change localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart (b * g)))) = _ at hn
  unfold normPower
  rw [hn, Real.log_mul
    (ne_of_gt (localAbs_pos (LocalField F q) _))
    (ne_of_gt (localAbs_pos (LocalField F q) _))]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation

end

end
