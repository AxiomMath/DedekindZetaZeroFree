module

public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.CenterCharacterPolarization
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellKernel

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel.Geometry
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
local notation "K" => q.adicCompletion F
local notation "v" => Sum.inr q
private lemma w_d (y : Kˣ) : KubotaRankTwo.w K * KubotaRankTwo.d K y 1 =
    KPScalarSplitCentral.scalarMatrix F v y *
      (KubotaRankTwo.d K y⁻¹ 1 * KubotaRankTwo.w K) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KubotaRankTwo.w, KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      KPScalarSplitCentral.scalarMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply]
private lemma X_wd (y : Kˣ) :
    KubotaRankTwo.X K (KubotaRankTwo.w K * KubotaRankTwo.d K y 1) = y := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, KubotaRankTwo.w, KubotaRankTwo.d,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, y.ne_zero]
private lemma X_dw (y : Kˣ) :
    KubotaRankTwo.X K (KubotaRankTwo.d K y 1 * KubotaRankTwo.w K) = 1 := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, KubotaRankTwo.w, KubotaRankTwo.d,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
private lemma B1 (y : Kˣ) : KPHilbert.B3 F ζ hζ v 1 y = 1 :=
  KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1 y
private lemma B2 (y : Kˣ) : KPHilbert.B3 F ζ hζ v y 1 = 1 :=
  KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1 y
private lemma sigma_wd (y : Kˣ) :
    KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.w K) (KubotaRankTwo.d K y 1) = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_wd,
    B1, B2, (KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2]
private lemma sigma_dw (y : Kˣ) :
    KPLocalCover.sigmaTwo F ζ hζ v (KubotaRankTwo.d K y 1) (KubotaRankTwo.w K) = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_dw,
    B1, B2]
private lemma sigma_scalar_dw (y : Kˣ) :
    KPLocalCover.sigmaTwo F ζ hζ v (KPScalarSplitCentral.scalarMatrix F v y)
      (KubotaRankTwo.d K y⁻¹ 1 * KubotaRankTwo.w K) = 1 := by
  have hx : KubotaRankTwo.X K (KPScalarSplitCentral.scalarMatrix F v y) = y := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix,
      Matrix.scalar, Matrix.diagonal_apply]
  have hb : KPHilbert.B3 F ζ hζ v (y ^ 2) y⁻¹ = 1 := by
    rw [KubotaDefectSymbolAlgebra.inv_right _ _ _ (KPHilbert.B3_laws F ζ hζ v).2.1]
    simp only [pow_two, (KPHilbert.B3_laws F ζ hζ v).1,
      (KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2, one_mul, inv_one]
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, X_dw,
    ← w_d F q y, X_wd, hx, B1, B2, hb]
private lemma raw_w_A (y : Kˣ) :
    KPStandardLocalRootLifts.signedW F ζ hζ v * KPStandardLocalRootLifts.A F ζ hζ v y =
      KPScalarSplitCentral.scalarHom F ζ hζ v y *
        (KPStandardLocalRootLifts.A F ζ hζ v y⁻¹ * KPStandardLocalRootLifts.signedW F ζ hζ v) := by
  rw [KPStandardLocalRootLifts.signedW, KPStandardLocalRootLifts.A,
    KPStandardLocalRootLifts.A, KPLocalCover.sectionMap_mul, sigma_wd,
    map_one, one_mul, KPLocalCover.sectionMap_mul, sigma_dw, map_one, one_mul]
  change _ = KPLocalCover.sectionMap F ζ hζ v
    (KPScalarSplitCentral.scalarMatrix F v y) * _
  rw [KPLocalCover.sectionMap_mul, sigma_scalar_dw, map_one, one_mul, w_d F q y]

theorem signedW_conjugates_A (y : Kˣ) :
    (KPPGLLocalCover.signedW F ζ hζ v)⁻¹ * KPPGLLocalCover.A F ζ hζ v y *
      KPPGLLocalCover.signedW F ζ hζ v = KPPGLLocalCover.A F ζ hζ v y⁻¹ := by
  have he := congrArg (KPPGLLocalCover.coverQuotient F ζ hζ v) (raw_w_A F ζ hζ q y)
  have hs : KPPGLLocalCover.coverQuotient F ζ hζ v
      (KPScalarSplitCentral.scalarHom F ζ hζ v y) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
  simp only [map_mul, hs, one_mul] at he
  change KPPGLLocalCover.signedW F ζ hζ v * KPPGLLocalCover.A F ζ hζ v y =
    KPPGLLocalCover.A F ζ hζ v y⁻¹ * KPPGLLocalCover.signedW F ζ hζ v at he
  have hw : (KPPGLLocalCover.signedW F ζ hζ v)⁻¹ = KPPGLLocalCover.signedW F ζ hζ v := by
    apply inv_eq_of_mul_eq_one_left
    exact (pow_two _).symm.trans (KPPGLLocalCover.signedW_sq F ζ hζ v)
  rw [hw, he, mul_assoc]
  simpa [← pow_two, KPPGLLocalCover.signedW_sq] using
    congrArg (fun w => KPPGLLocalCover.A F ζ hζ v y⁻¹ * w)
      (KPPGLLocalCover.signedW_sq F ζ hζ v)

theorem signedW_conjugates_normalWord (e : rootsOfUnity 3 F) (y : Kˣ) :
    (KPPGLLocalCover.signedW F ζ hζ v)⁻¹ * ActualFiniteTorus.normalWord F ζ hζ q e y *
      KPPGLLocalCover.signedW F ζ hζ v = ActualFiniteTorus.normalWord F ζ hζ q e y⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ v ⟨e, rfl⟩)
    ((KPPGLLocalCover.signedW F ζ hζ v)⁻¹)
  unfold ActualFiniteTorus.normalWord
  rw [← mul_assoc, hc, mul_assoc, mul_assoc, ← mul_assoc
    ((KPPGLLocalCover.signedW F ζ hζ v)⁻¹), signedW_conjugates_A]

theorem signedW_preserves_torus (t : ActualFiniteTorus.H F ζ hζ q) :
    (KPPGLLocalCover.signedW F ζ hζ v)⁻¹ * t.val * KPPGLLocalCover.signedW F ζ hζ v ∈
      ActualFiniteTorus.H F ζ hζ q := by
  rw [(ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 t,
    signedW_conjugates_normalWord]
  exact (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).1 _ _

end
end DedekindZetaZeroFree.ActualFiniteBorel.Geometry
