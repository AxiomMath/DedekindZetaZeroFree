module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.DoubleCocycleAndBetaArithmetic

@[expose] public section

namespace DedekindZetaZeroFree.KPActualFullKernelArithmetic

open scoped NumberField Valued
open NumberField IsDedekindDomain
open KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneOpenCellKernel KPRankOneLiftedRegulatedDiagonalAlgebra
open KPActualScalarBinding
open KPRankOneCenterInducedDiagonalComparison

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

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
private lemma kappa_eq_one (v : (LocalField F q)ˣ) (s : LocalField F q) : kappa F ζ hζ q v s = 1 := by
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
private lemma norm_mul (x y : (LocalField F q)ˣ) (z : ℂ) :
    normPower (LocalField F q) (x * y) z =
      normPower (LocalField F q) x z * normPower (LocalField F q) y z := by
  rw [normPower, localAbs_mul, Real.log_mul (ne_of_gt (localAbs_pos _ x))
    (ne_of_gt (localAbs_pos _ y)), Complex.ofReal_add, mul_add, Complex.exp_add]
  rfl
private lemma norm_pow (x : (LocalField F q)ˣ) (n : ℕ) (z : ℂ) :
    normPower (LocalField F q) (x ^ n) z = normPower (LocalField F q) x (n * z) := by
  have ha : localAbs (LocalField F q) (x ^ n) = localAbs (LocalField F q) x ^ n := by
    induction n with
    | zero => simp [localAbs_one]
    | succ n ih => rw [pow_succ, localAbs_mul, ih, pow_succ]
  simp only [normPower, ha, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
  congr 1
  ring
private lemma Bpow (x y : (LocalField F q)ˣ) (i j : ℤ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) (x^i) (y^j) =
      KPHilbert.B3 F ζ hζ (Sum.inr q) x y ^ (i*j) := by
  let BL (c : (LocalField F q)ˣ) : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := fun x => KPHilbert.B3 F ζ hζ (Sum.inr q) x c
      map_one' := BoneL F ζ hζ q c
      map_mul' := fun x y => (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 x y c }
  let BR (c : (LocalField F q)ˣ) : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := KPHilbert.B3 F ζ hζ (Sum.inr q) c
      map_one' := BoneR F ζ hζ q c
      map_mul' := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1 c }
  change BL (y^j) (x^i) = _
  rw [map_zpow]
  change (BR x (y^j)) ^ i = _
  rw [map_zpow, ← zpow_mul, Int.mul_comm]; rfl

private lemma ratio_phase (c x y : (LocalField F q)ˣ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) ((c*x)^2)⁻¹ ((x*y^3)^2) ^ 2 =
      KPHilbert.B3 F ζ hζ (Sum.inr q) c x := by
  have hL := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1
  have hR := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1
  have hcube := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1
  have hm : ((c*x)^2)⁻¹ = c^(-2:ℤ)*x^(-2:ℤ) := by simp [mul_pow, mul_inv_rev, zpow_neg]; ac_rfl
  have hn : (x*y^3)^2 = x^2*(y^2)^3 := by simp [mul_pow, ← pow_mul]
  rw [hm, hn, hR, (hcube _ _).2, mul_one, hL]
  have hs : KPHilbert.B3 F ζ hζ (Sum.inr q) (x^(-2:ℤ)) (x^2) = 1 := by
    have he := Bpow F ζ hζ q x x (-2) 2
    simp only [Int.reduceNeg, zpow_ofNat] at he
    rw [he, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 x |>.1]; simp
  rw [hs, mul_one]
  have hp := Bpow F ζ hζ q c x (-2) 2
  simp only [Int.reduceNeg, zpow_ofNat] at hp
  rw [hp]
  let w := KPHilbert.B3 F ζ hζ (Sum.inr q) c x
  have hw : w^3=1 := Subtype.ext w.property
  change (w^(-4:ℤ))^2=w
  have he : (-4:ℤ) = 2-2*3 := by omega
  rw [he, zpow_sub, zpow_mul]
  simp only [zpow_ofNat]
  rw [← pow_mul, show 2*3=3*2 by omega, pow_mul, hw]
  simp only [one_pow, inv_one, mul_one]
  rw [← pow_mul]
  norm_num only [Nat.reduceMul]
  rw [show 4=3+1 by omega, pow_add, hw]; simp

private lemma actual_word
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (c x y : (LocalField F q)ˣ) :
    S.borel.weyl ((S.openCell P).rootTorus (c*x)) *
      (S.openCell P).rootTorus (x*y^3) =
    (S.central (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : _) *
      (S.borel.weyl ((S.openCell P).rootTorus c) *
        (S.openCell P).rootTorus 1) *
      (S.borel.cubeLift (y^2) : _) := by
  have hr (w : (LocalField F q)ˣ) :
      ((S.openCell P).rootTorus w : Cover F ζ hζ q) =
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (w^2) := by
    rw [← S.torus_full, (S.openCell P).torus_eq]; rfl
  have hw (w : (LocalField F q)ˣ) :
      (S.borel.weyl ((S.openCell P).rootTorus w) : Cover F ζ hζ q) =
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (w^2)⁻¹ := by
    rw [← S.torus_full, S.borel.weyl_from_lift, S.torus_full, hr,
      (S.openCell P).weyl_eq]
    have he : signedWeyl F ζ hζ q = KPPGLLocalCover.signedW F ζ hζ (Sum.inr q) := by
      unfold signedWeyl; rw [signedWeyl_eq_prescribed_signed]; rfl
    rw [he, WeylAux.signedW_conjugates_A]
  apply Subtype.val_injective
  simp only [Subgroup.coe_mul, hw, hr, S.central_actual, S.cube_actual]
  rw [KPPGLLocalCover.A_mul, ratio_phase]
  simp only [one_pow]
  have hB1 : KPHilbert.B3 F ζ hζ (Sum.inr q) (c^2)⁻¹ 1 = 1 := BoneR F ζ hζ q _
  rw [KPPGLLocalCover.A_mul, hB1]
  simp only [one_pow, map_one, one_mul, mul_one]
  rw [mul_assoc, KPPGLLocalCover.A_mul,
    (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1 _ _ |>.2]
  simp only [one_pow, map_one, one_mul]
  congr 2
  simp only [mul_pow, inv_pow]
  group
  rw [mul_right_comm (x^(-2:ℤ)), ← zpow_add, neg_add_cancel]
  simp

private lemma center_word_action
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (c x y : (LocalField F q)ˣ)
    (V : CenterModule S.heisenberg) (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    ((centerTorus F ζ hζ q S.heisenberg S.borel .minus ((S.openCell P).rootTorus (c*x)))
      ((centerTorus F ζ hζ q S.heisenberg S.borel .plus
        ((S.openCell P).rootTorus (x*y^3))) V)).val h =
      (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) *
      normPower (LocalField F q) ((y^2)^3) (1/6) *
      ((centerTorus F ζ hζ q S.heisenberg S.borel .minus ((S.openCell P).rootTorus c))
        ((centerTorus F ζ hζ q S.heisenberg S.borel .plus
          ((S.openCell P).rootTorus 1)) V)).val h := by
  change V.val (h * S.borel.weyl ((S.openCell P).rootTorus (c*x)) *
    (S.openCell P).rootTorus (x*y^3)) = _
  rw [mul_assoc, actual_word F ζ hζ q S P]
  let e := KPHilbert.B3 F ζ hζ (Sum.inr q) c x
  let W := S.borel.weyl ((S.openCell P).rootTorus c) * (S.openCell P).rootTorus 1
  let C := S.borel.cubeLift (y^2)
  have hcent (z : S.heisenberg.C) (g : KPExceptionalRaw.actualTorus F ζ hζ q) :
      g * z = z * g := (Subgroup.mem_center_iff.mp (S.heisenberg.central z.property) g)
  change V.val (h * (((S.central e : _) * W) * (C : _))) = _
  rw [← mul_assoc, ← mul_assoc, hcent (S.central e), mul_assoc, mul_assoc,
    V.property]
  rw [← mul_assoc, hcent C, V.property]
  change (S.heisenberg.ω (S.central e) : ℂ) *
    ((S.heisenberg.ω (S.borel.cubeLift (y^2)) : ℂ) * V.val (h*W)) = _
  rw [S.central_character, S.borel.exceptional_cube]
  change _ = _ * _ * V.val (h * S.borel.weyl ((S.openCell P).rootTorus c) *
    (S.openCell P).rootTorus 1)
  simp [W, C, e, mul_assoc]

private lemma norm_unram_direct (s : ℂ) (r t : ℂˣ)
    (hr : (r : ℂ) = KPRankOneRootParameter.r (LocalField F q) s)
    (ht : (t : ℂ) = (residueCardinality (LocalField F q) : ℂ)⁻¹ * (r : ℂ)^6)
    (y : (LocalField F q)ˣ) :
    normPower (LocalField F q) y (1+6*s) = KPCubicExpansion.omega (LocalField F q) t y := by
  let L : ℂ := Real.log (residueCardinality (LocalField F q) : ℝ)
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (ValuativeRel.valuation (LocalField F q)).integer))
  have hl : (Real.log (localAbs (LocalField F q) y) : ℂ) =
      -(KPCubicExpansion.valuationExponent (LocalField F q) y : ℂ) * L := by
    simp only [localAbs, KPCubicExpansion.valuationExponent]
    rw [Real.log_rpow hq]
    rw [Complex.ofReal_mul, Complex.ofReal_intCast, Int.cast_neg, neg_neg]
  have he : Complex.exp (-(1+6*s)*L) = (t:ℂ) := by
    rw [show -(1+6*s)*L = -L+6*(-s*L) by ring, Complex.exp_add]
    rw [show (6:ℂ)=((6:ℕ):ℂ) by norm_num, Complex.exp_nat_mul]
    change Complex.exp (-L) * KPRankOneRootParameter.r (LocalField F q) s ^ 6 = _
    rw [← hr, ht]; congr 1
    rw [Complex.exp_neg]; congr 1
    exact (Complex.ofReal_exp (Real.log (residueCardinality (LocalField F q) : ℝ))).symm |>.trans
      (congrArg Complex.ofReal (Real.exp_log hq))
  rw [normPower, hl]
  rw [show (1+6*s)*(-(KPCubicExpansion.valuationExponent (LocalField F q) y : ℂ)*L) =
    (KPCubicExpansion.valuationExponent (LocalField F q) y : ℂ)*(-(1+6*s)*L) by ring,
    Complex.exp_int_mul, he]
  simp [KPCubicExpansion.omega]

private lemma norm_weights (c x y : (LocalField F q)ˣ) (s ρ : ℂ) :
    normPower (LocalField F q) ((c*x)^2) (-s) *
      normPower (LocalField F q) ((x*y^3)^2) s *
      normPower (LocalField F q) ((y^2)^3) (1/6) *
      normPower (LocalField F q) (c*x) ρ =
    normPower (LocalField F q) y (1+6*s) * normPower (LocalField F q) c ρ *
      normPower (LocalField F q) (c^2) (-s) * normPower (LocalField F q) x ρ := by
  simp only [norm_pow, norm_mul]
  simp only [normPower]
  repeat rw [← Complex.exp_add]
  congr 1
  ring

theorem actual_doubleKernel_all_ratios
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    [DecidableEq S.D]
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (s ρ : ℂ) (r t : ℂˣ)
    (hr : (r : ℂ) = KPRankOneRootParameter.r (LocalField F q) s)
    (ht : (t : ℂ) = (residueCardinality (LocalField F q) : ℂ)⁻¹ * (r : ℂ) ^ 6)
    (h : KPExceptionalRaw.actualTorus F ζ hζ q)
    (a b u v : (LocalField F q)ˣ) :
    doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d φ s ρ h a b u v =
      KPCubicExpansion.omega (LocalField F q) t (u / v) *
        normPower (LocalField F q) (b / a) ρ *
        (KPExceptionalRaw.ordinaryIota F ζ hζ
          (KPHilbert.B3 F ζ hζ (Sum.inr q) (b / a) (a * v ^ 3)) : ℂ) *
        doubleKernel F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep d (fun _ => 1) s 0 h 1 (b / a) 1 1 *
        φ (((a * v ^ 3 : (LocalField F q)ˣ) : LocalField F q) *
          (((u / v : (LocalField F q)ˣ) : LocalField F q) ^ 3 +
            ((b / a : (LocalField F q)ˣ) : LocalField F q))) *
        normPower (LocalField F q) (a * v ^ 3) ρ := by
  let c := b/a
  let x := a*v^3
  let y := u/v
  have hc : c*x = b*v^3 := by dsimp [c,x]; simp [← mul_assoc]
  have hx : x*y^3 = a*u^3 := by dsimp [x,y]; simp [div_eq_mul_inv, mul_pow, inv_pow, mul_comm, mul_left_comm, mul_assoc]
  have hφ : sourceTranslation F q a b u v =
      (x:LocalField F q)*((y:LocalField F q)^3+(c:LocalField F q)) := by
    dsimp [sourceTranslation,c,x,y]
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    field_simp
  dsimp only [doubleKernel, reverseIncrement]
  simp only [kappa_eq_one F ζ hζ q, S.openCell_ordinary, map_one, Units.val_one,
    one_mul, one_pow, mul_one]
  have n1 : ∀ z : ℂ, normPower (LocalField F q) 1 z = 1 := by
    intro z; simp [normPower, localAbs_one]
  have n0 : ∀ w : (LocalField F q)ˣ, normPower (LocalField F q) w 0 = 1 := by
    intro w; simp [normPower]
  simp only [n1, n0, mul_one]
  rw [hφ, ← hc, ← hx]
  simp only [map_smul]
  have hsval (z : ℂ) (V : CenterModule S.heisenberg) :
      (z • V).val h = z * V.val h := rfl
  simp only [hsval, one_smul]
  rw [center_word_action F ζ hζ q S P c x y]
  change _ = KPCubicExpansion.omega (LocalField F q) t y * normPower (LocalField F q) c ρ *
    (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) *
    (normPower (LocalField F q) (c^2) (-s) * _) * φ ((x:LocalField F q)*((y:LocalField F q)^3+(c:LocalField F q))) *
    normPower (LocalField F q) x ρ
  rw [← norm_unram_direct F q s r t hr ht]
  have he := norm_weights F q c x y s ρ
  linear_combination (KPExceptionalRaw.ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) c x) : ℂ) *
    φ ((x:LocalField F q)*((y:LocalField F q)^3+(c:LocalField F q))) *
    (((centerTorus F ζ hζ q S.heisenberg S.borel .minus ((S.openCell P).rootTorus c))
      ((centerTorus F ζ hζ q S.heisenberg S.borel .plus ((S.openCell P).rootTorus 1))
        ((centerCoordinates S.heisenberg rep hrep).symm (Pi.single d 1)))).val h) * he

end
end DedekindZetaZeroFree.KPActualFullKernelArithmetic
