module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenBruhatCellCorrespondence
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.CubicCharacterExpansion

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail
namespace SignedBlockAlgebra
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
private lemma winv (K : Type*) [Field K] : (KubotaRankTwo.w K)⁻¹ = KubotaRankTwo.d K (-1) (-1) * KubotaRankTwo.w K := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
private lemma Xwinv (K : Type*) [Field K] : KubotaRankTwo.X K (KubotaRankTwo.w K)⁻¹ = -1 := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply]
private lemma Xwnw (K : Type*) [Field K] (v : Kˣ) :
    KubotaRankTwo.X K ((KubotaRankTwo.w K)⁻¹ * KubotaRankTwo.n K (-((v⁻¹ : Kˣ) : K)) * (KubotaRankTwo.w K)⁻¹) = -v⁻¹ := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply, Units.ne_zero]

private lemma BoneL (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) 1 a = 1 :=
  KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 a
private lemma BoneR (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) a 1 = 1 :=
  KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 a
private lemma BnegR (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) a (-1) = 1 :=
  (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 a |>.2.1
private lemma sigmanR (g : KubotaRankTwo.GL2 (LocalField F q)) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q) g (KubotaRankTwo.n (LocalField F q) s) = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, BoneL, BoneR]
private lemma sigww : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    (KubotaRankTwo.w (LocalField F q)) (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xwinv, BoneL, BoneR]
private lemma sigwnw (v : (LocalField F q)ˣ) : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    ((KubotaRankTwo.w (LocalField F q))⁻¹ * KubotaRankTwo.n (LocalField F q) (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)))
    (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xwnw, KubotaRankTwo.X_mul_n,
    Xwinv, map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w, inv_one, one_mul,
    mul_one, one_pow]
  have hr : (-v⁻¹) / (-1) = v⁻¹ := by simp
  rw [hr, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 v⁻¹ |>.1, BoneL]
  simp
private lemma Xdnw (K : Type*) [Field K] (v : Kˣ) (s : K) :
    KubotaRankTwo.X K (KubotaRankTwo.d K (v ^ 2) 1 * KubotaRankTwo.n K s * (KubotaRankTwo.w K)⁻¹) = -1 := by
  rw [winv]
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply]
private lemma Bselfpow (a : (LocalField F q)ˣ) (m n : ℤ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) (a ^ m) (a ^ n) = 1 := by
  let BL (b : (LocalField F q)ˣ) : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := fun x => KPHilbert.B3 F ζ hζ (Sum.inr q) x b
      map_one' := BoneL F ζ hζ q b
      map_mul' := fun x y => (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 x y b }
  let BR : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := KPHilbert.B3 F ζ hζ (Sum.inr q) a
      map_one' := BoneR F ζ hζ q a
      map_mul' := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 a }
  change BL (a ^ n) (a ^ m) = 1
  rw [map_zpow]
  change (BR (a ^ n)) ^ m = 1
  rw [map_zpow]
  change (KPHilbert.B3 F ζ hζ (Sum.inr q) a a ^ n) ^ m = 1
  rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 a |>.1]
  simp
private lemma BnegL (a : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) (-1) a = 1 := by
  rw [(KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.1, BnegR]
  simp
private lemma sigdnw (v : (LocalField F q)ˣ) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (KubotaRankTwo.d (LocalField F q) (v ^ 2) 1 * KubotaRankTwo.n (LocalField F q) s)
      (KubotaRankTwo.w (LocalField F q))⁻¹ = 1 := by
  simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, Xdnw, KubotaRankTwo.X_mul_n,
    KubotaRankTwo.X_d, Xwinv, map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w,
    KubotaRankTwo.det_d, inv_one, mul_one, div_one, one_mul, one_pow]
  rw [BnegL, BoneR]
  simp
private lemma Xscalar (K : Type*) [Field K] (v : Kˣ) :
    KubotaRankTwo.X K (Matrix.GeneralLinearGroup.scalar (Fin 2) v) = v := by
  apply Units.ext
  simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.scalar]
private lemma Xscalar_mul (K : Type*) [Field K] (v : Kˣ) (g : KubotaRankTwo.GL2 K) :
    KubotaRankTwo.X K (Matrix.GeneralLinearGroup.scalar (Fin 2) v * g) = v * KubotaRankTwo.X K g := by
  classical
  apply Units.ext
  simp only [KubotaRankTwo.X, Units.val_mk0, Units.val_mul]
  unfold KubotaRankTwo.x
  have he (i j : Fin 2) : (Matrix.GeneralLinearGroup.scalar (Fin 2) v * g) i j = (v : K) * g i j := by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.scalar]
  rw [he 1 0, he 1 1]
  simp only [mul_eq_zero, v.ne_zero, false_or]
  split_ifs <;> rfl
private lemma sigscalar (v : (LocalField F q)ˣ) (s : LocalField F q) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) v⁻¹)
      (KubotaRankTwo.d (LocalField F q) (v ^ 2) 1 * KubotaRankTwo.n (LocalField F q) ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
        (KubotaRankTwo.w (LocalField F q))⁻¹ * KubotaRankTwo.n (LocalField F q) s) = 1 := by
  change KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
    ((Matrix.GeneralLinearGroup.scalar (Fin 2)) v⁻¹) _ = 1
  unfold KPLocalCover.sigmaTwo KubotaElementaryLastArgument.tau
  simp only [Xscalar_mul, Xscalar,
    KubotaRankTwo.X_mul_n, Xdnw,
    KubotaRankTwo.det,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_one, mul_one]
  have h1 : v⁻¹ * (-1) / v⁻¹ = -1 := by simp
  rw [h1, BnegL]
  have hB : KPHilbert.B3 F ζ hζ (Sum.inr q) (v⁻¹ ^ 2) (v ^ 2) = 1 := by
    convert Bselfpow F ζ hζ q v (-2) 2 using 1 <;> simp
  simp only [map_mul, map_inv, KubotaRankTwo.det_n, KubotaRankTwo.det_w,
    KubotaRankTwo.det_d, inv_one, mul_one, ← inv_pow, hB, one_pow]
theorem kappa_eq_one (v : (LocalField F q)ˣ) (s : LocalField F q) : kappa F ζ hζ q v s = 1 := by
  rw [kappa, bruhatLeft, bruhatRight, signedWeyl_eq_prescribed_signed]
  have he : ∀ x : (LocalField F q)ˣ,
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) x).epsilon = 1 := fun _ => rfl
  have hg : ∀ x : (LocalField F q)ˣ,
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) x).g = Matrix.GeneralLinearGroup.scalar (Fin 2) x := fun _ => rfl
  simp only [KPLocalCover.mul_epsilon, KPLocalCover.inv_epsilon, KPLocalCover.mul_g,
    KPLocalCover.inv_g, KPStandardLocalRootLifts.signedW, KPStandardLocalRootLifts.N,
    KPStandardLocalRootLifts.A, he, hg,
    KPLocalCover.sectionMap_epsilon, KPLocalCover.sectionMap_g]
  simp only [sigww F ζ hζ q, sigmanR F ζ hζ q, sigwnw F ζ hζ q,
    sigdnw F ζ hζ q, sigscalar F ζ hζ q, one_mul, mul_one,
    inv_one, div_one]

namespace WeylAux
local notation "K" => LocalField F q
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

private theorem signedW_conjugates_A (y : Kˣ) :
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

end WeylAux

variable {H D : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T) (B : Binding F ζ hζ q A P)
local instance : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
  KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
include P B in
private lemma proj_eq (g : Cover F ζ hζ q) : A.projection g = KPLocalSmoothRepresentation.projection F ζ hζ q g := by
  induction g using QuotientGroup.induction_on with | _ g =>
    exact B.projection_eq g
private lemma pgl_inj : Function.Injective (KPLocalSmoothRepresentation.ordinaryPGLMap F q) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
  intro a b
  induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
      intro h
      change Matrix.ProjGenLinGroup.mk a = Matrix.ProjGenLinGroup.mk b at h
      obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
      apply (QuotientGroup.mk'_eq_mk' _).mpr
      exact ⟨KPScalarSplitCentral.scalarMatrix F (Sum.inr q) u, ⟨u, rfl⟩, hu⟩
include P B in
private lemma fiber (x y : Cover F ζ hζ q) (he : A.projection x = A.projection y) :
    ∃ e, x = KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e * y := by
  have hp : KPPGLLocalCover.projection F ζ hζ (Sum.inr q) (x * y⁻¹) = 1 := by
    apply pgl_inj F q
    change KPLocalSmoothRepresentation.projection F ζ hζ q (x * y⁻¹) =
      KPLocalSmoothRepresentation.ordinaryPGLMap F q 1
    rw [← proj_eq F ζ hζ q T A P B, map_mul, map_inv, he, mul_inv_cancel, map_one]
  have hm : x * y⁻¹ ∈ (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)).range := by
    rw [KPPGLLocalCover.range_centralInjection_eq_ker_projection]
    exact hp
  obtain ⟨e, he⟩ := hm
  exact ⟨e, (eq_mul_inv_iff_mul_eq.mp he).symm⟩
include P B in
theorem cube_sheet (y : (LocalField F q)ˣ) :
    (A.torus (A.cubeLift y : H) : Cover F ζ hζ q) = KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) := by
  let c := (A.torus (A.cubeLift y : H) : Cover F ζ hζ q)
  let d := KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3)
  have hp : A.projection c = A.projection d := by
    rw [A.torus_projection, A.cube_coordinate]
    change _ = A.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (y ^ 3)))
    rw [B.projection_eq]
    rfl
  obtain ⟨e, he⟩ := fiber F ζ hζ q T A P B c d hp
  have hi : d⁻¹ = KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y⁻¹ ^ 3) := by
    apply inv_eq_of_mul_eq_one_right
    rw [KPPGLLocalCover.A_mul]
    have hB : KPHilbert.B3 F ζ hζ (Sum.inr q) (y ^ 3) (y⁻¹ ^ 3) = 1 := by
      rw [pow_succ, pow_succ, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1,
        (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1]
      simp only [pow_one]
      rw [← pow_two, ← pow_succ]
      exact Subtype.ext (KPHilbert.B3 F ζ hζ (Sum.inr q) y (y⁻¹ ^ 3)).property
    simp only [hB, one_pow, map_one, one_mul]
    rw [← mul_pow, mul_inv_cancel, one_pow]
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) 1) = 1
    rw [KPStandardLocalRootLifts.A_one, map_one]
  have hw : A.liftedW = KPPGLLocalCover.signedW F ζ hζ (Sum.inr q) := by
    rw [B.weyl_eq]
    unfold signedWeyl
    rw [signedWeyl_eq_prescribed_signed]
    rfl
  have hc : A.liftedW⁻¹ * c * A.liftedW = c⁻¹ := by
    rw [← A.weyl_from_lift, ← A.weylCenter_coe, A.weyl_cube, map_inv,
      Subgroup.coe_inv, map_inv]
    rfl
  have hd : A.liftedW⁻¹ * d * A.liftedW = d⁻¹ := by
    rw [hw, WeylAux.signedW_conjugates_A, hi]
    simp
  let z := KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e
  have hz := Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q) ⟨e, rfl⟩)
  have he2 : z = z⁻¹ := by
    rw [he] at hc
    change A.liftedW⁻¹ * (z * d) * A.liftedW = (z * d)⁻¹ at hc
    rw [← mul_assoc, hz A.liftedW⁻¹, mul_assoc z, mul_assoc z, hd,
      mul_inv_rev, ← hz d⁻¹] at hc
    exact mul_left_cancel hc
  have h2 : e ^ 2 = 1 := by
    apply KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inr q)
    rw [map_pow, map_one]
    change z ^ 2 = 1
    rw [pow_two]
    conv_lhs => lhs; rw [he2]
    exact inv_mul_cancel _
  have h3 : e ^ 3 = 1 := Subtype.ext e.property
  have he1 : e = 1 := by
    simpa [pow_succ, h2] using h3
  simpa [he1] using he
theorem BcubeL (x y : (LocalField F q)ˣ) : KPHilbert.B3 F ζ hζ (Sum.inr q) (x ^ 3) y = 1 := by
  rw [pow_succ, pow_succ, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1,
    (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1]
  simp only [pow_one]
  rw [← pow_two, ← pow_succ]
  exact Subtype.ext (KPHilbert.B3 F ζ hζ (Sum.inr q) x y).property

end
end SignedBlockAlgebra
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail
