module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightDifferentialWords.CompactSeminormBounds
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.SpectralDeformation
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberSeries.SpatialDifferentiation
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.RaisingOperators.SphericalDerivativeReconstruction

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped Classical Matrix.Norms.Elementwise Topology ContDiff
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir
open RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction KPSmoothActualFlowData

private theorem pauli_native_matrix (j : Fin 3) :
    noncompactMatrix j = (Real.sqrt 2)⁻¹ •
      (![basisMatrix 0, basisMatrix 2 + basisMatrix 4, basisMatrix 3 - basisMatrix 5] j) ∧
    compactMatrix j = (Real.sqrt 2)⁻¹ •
      (![basisMatrix 1, basisMatrix 3 + basisMatrix 5, -basisMatrix 2 + basisMatrix 4] j) := by
  fin_cases j <;> constructor <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [noncompactMatrix, compactMatrix, basisMatrix, sl2Matrix, Complex.real_smul] <;>
    ring_nf <;> simp [Complex.I_sq]

private theorem quadratic_contraction
    (Q : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ j : Fin 3, Q (g * noncompactMatrix j) (g * noncompactMatrix j)) -
      (∑ j : Fin 3, Q (g * compactMatrix j) (g * compactMatrix j)) =
    (1 / 2 : ℂ) *
      (Q (g * basisMatrix 0) (g * basisMatrix 0) -
       Q (g * basisMatrix 1) (g * basisMatrix 1) +
       2 * (Q (g * basisMatrix 2) (g * basisMatrix 4) +
         Q (g * basisMatrix 4) (g * basisMatrix 2) -
         Q (g * basisMatrix 3) (g * basisMatrix 5) -
         Q (g * basisMatrix 5) (g * basisMatrix 3))) := by
  have hn (j : Fin 3) := (pauli_native_matrix j).1
  have hc (j : Fin 3) := (pauli_native_matrix j).2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hn, hc, Matrix.mul_smul,
    Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, map_smul, map_add, map_sub,
    map_neg, smul_apply, add_apply, sub_apply, neg_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Complex.real_smul, Complex.ofReal_inv]
  have hs : ((Real.sqrt 2)⁻¹ : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linear_combination (Q (g * basisMatrix 0) (g * basisMatrix 0) -
    Q (g * basisMatrix 1) (g * basisMatrix 1) + 2 *
      (Q (g * basisMatrix 2) (g * basisMatrix 4) + Q (g * basisMatrix 4) (g * basisMatrix 2) -
        Q (g * basisMatrix 3) (g * basisMatrix 5) - Q (g * basisMatrix 5) (g * basisMatrix 3))) * hs

open scoped Matrix.Norms.Operator in
private theorem exp_path_hasDeriv_components (g X : Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j) ((g * X) i j) 0 := by
  have he := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    (f := fun t : ℝ => (t : ℂ)) 0 Complex.ofRealCLM.hasDerivAt
  have hh := he.const_mul g
  have hi := (ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hh
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hi
  change HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j)
    ((g * (ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.toSpanSingleton ℂ (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X))) 1) i j) 0 at hj
  simpa using hj

 theorem exp_path_hasDeriv (g X : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => exp_path_hasDeriv_components g X i j

 def matrixRightDerivative (X : Matrix (Fin 2) (Fin 2) ℂ)
    (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  deriv (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) 0

 theorem matrixRightDerivative_eq_fderiv
    (X : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (hφ : DifferentiableAt ℝ φ g) :
    matrixRightDerivative X φ g = fderiv ℝ φ g (g * X) := by
  exact (hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (exp_path_hasDeriv g X) (by simp)).deriv

private theorem matrixRightDerivative_twice
    (X Y : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ O) :
    matrixRightDerivative Y (matrixRightDerivative X φ) g =
      fderiv ℝ (fderiv ℝ φ) g (g * Y) (g * X) +
        fderiv ℝ φ g (g * (Y * X)) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) g :=
    ((hφ.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).differentiableOn
      (by simp)).differentiableAt (hO.mem_nhds hg)
  let R : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => y * X
        map_add' := fun y z => Matrix.add_mul y z X
        map_smul' := fun a y => Matrix.smul_mul a y X }
  have hmul : HasFDerivAt (fun y : Matrix (Fin 2) (Fin 2) ℂ => y * X) R g := R.hasFDerivAt
  have he : matrixRightDerivative X φ =ᶠ[nhds g]
      (fun y : Matrix (Fin 2) (Fin 2) ℂ => fderiv ℝ φ y (y * X)) := by
    filter_upwards [hO.mem_nhds hg] with y hy
    exact matrixRightDerivative_eq_fderiv X φ y
      ((hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hy))
  have hh := hd.hasFDerivAt.clm_apply hmul
  rw [matrixRightDerivative_eq_fderiv Y _ g
    (hh.differentiableAt.congr_of_eventuallyEq he), he.fderiv_eq]
  have hf := congrArg (fun D : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ => D (g * Y)) hh.fderiv
  change (fderiv ℝ (fun y => fderiv ℝ φ y (y * X)) g) (g * Y) = _
  apply hf.trans
  change fderiv ℝ φ g ((g * Y) * X) + fderiv ℝ (fderiv ℝ φ) g (g * Y) (g * X) = _
  rw [Matrix.mul_assoc, add_comm]

open scoped Matrix.Norms.Operator in
private theorem exp_left_path_hasDeriv_components (g X : Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X) * g) i j) ((X * g) i j) 0 := by
  have he := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    (f := fun t : ℝ => (t : ℂ)) 0 Complex.ofRealCLM.hasDerivAt
  have hh := he.mul_const g
  have hi := (ContinuousLinearMap.proj i : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hh
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hi
  change HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X) * g) i j)
    (((ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.toSpanSingleton ℂ (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X))) 1 * g) i j) 0 at hj
  simpa using hj

private theorem exp_left_path_hasDeriv (g X : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => exp_left_path_hasDeriv_components g X i j

 def matrixLeftDerivative (X : Matrix (Fin 2) (Fin 2) ℂ)
    (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  deriv (fun t : ℝ => φ (NormedSpace.exp ((t : ℂ) • X) * g)) 0

private theorem matrixLeftDerivative_eq_fderiv
    (X : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (hφ : DifferentiableAt ℝ φ g) :
    matrixLeftDerivative X φ g = fderiv ℝ φ g (X * g) := by
  exact (hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (exp_left_path_hasDeriv g X) (by simp)).deriv

private theorem matrixLeftDerivative_twice
    (X Y : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ O) :
    matrixLeftDerivative Y (matrixLeftDerivative X φ) g =
      fderiv ℝ (fderiv ℝ φ) g (Y * g) (X * g) +
        fderiv ℝ φ g ((X * Y) * g) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) g :=
    ((hφ.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).differentiableOn
      (by simp)).differentiableAt (hO.mem_nhds hg)
  let L : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => X * y
        map_add' := fun y z => Matrix.mul_add X y z
        map_smul' := fun a y => Matrix.mul_smul X a y }
  have hmul : HasFDerivAt (fun y : Matrix (Fin 2) (Fin 2) ℂ => X * y) L g := L.hasFDerivAt
  have he : matrixLeftDerivative X φ =ᶠ[nhds g]
      (fun y : Matrix (Fin 2) (Fin 2) ℂ => fderiv ℝ φ y (X * y)) := by
    filter_upwards [hO.mem_nhds hg] with y hy
    exact matrixLeftDerivative_eq_fderiv X φ y
      ((hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hy))
  have hh := hd.hasFDerivAt.clm_apply hmul
  rw [matrixLeftDerivative_eq_fderiv Y _ g
    (hh.differentiableAt.congr_of_eventuallyEq he), he.fderiv_eq]
  have hf := congrArg (fun D : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ => D (Y * g)) hh.fderiv
  change (fderiv ℝ (fun y => fderiv ℝ φ y (X * y)) g) (Y * g) = _
  apply hf.trans
  change fderiv ℝ φ g (X * (Y * g)) + fderiv ℝ (fderiv ℝ φ) g (Y * g) (X * g) = _
  rw [← Matrix.mul_assoc, add_comm]

 theorem matrixRightDerivative_smooth
    (X : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (matrixRightDerivative X φ) O := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Matrix (Fin 2) (Fin 2) ℂ => y * X) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y : Matrix (Fin 2) (Fin 2) ℂ => fun i j => ∑ k, y i k * X k j)
    fun_prop
  apply ((hφ.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).clm_apply hm.contDiffOn).congr
  intro g hg
  exact matrixRightDerivative_eq_fderiv X φ g
    ((hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hg))

private theorem matrixLeftDerivative_smooth
    (X : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (matrixLeftDerivative X φ) O := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Matrix (Fin 2) (Fin 2) ℂ => X * y) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y : Matrix (Fin 2) (Fin 2) ℂ => fun i j => ∑ k, X i k * y k j)
    fun_prop
  apply ((hφ.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).clm_apply hm.contDiffOn).congr
  intro g hg
  exact matrixLeftDerivative_eq_fderiv X φ g
    ((hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hg))

private theorem matrix_mixed_left_right
    (X Y : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ O) :
    matrixLeftDerivative X (matrixRightDerivative Y φ) g =
      matrixRightDerivative Y (matrixLeftDerivative X φ) g := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) g :=
    ((hφ.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).differentiableOn
      (by simp)).differentiableAt (hO.mem_nhds hg)
  let R : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => y * Y
        map_add' := fun y z => Matrix.add_mul y z Y
        map_smul' := fun a y => Matrix.smul_mul a y Y }
  let L : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => X * y
        map_add' := fun y z => Matrix.mul_add X y z
        map_smul' := fun a y => Matrix.mul_smul X a y }
  have heR : matrixRightDerivative Y φ =ᶠ[nhds g]
      (fun y : Matrix (Fin 2) (Fin 2) ℂ => fderiv ℝ φ y (y * Y)) := by
    filter_upwards [hO.mem_nhds hg] with y hy
    exact matrixRightDerivative_eq_fderiv Y φ y
      ((hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hy))
  have heL : matrixLeftDerivative X φ =ᶠ[nhds g]
      (fun y : Matrix (Fin 2) (Fin 2) ℂ => fderiv ℝ φ y (X * y)) := by
    filter_upwards [hO.mem_nhds hg] with y hy
    exact matrixLeftDerivative_eq_fderiv X φ y
      ((hφ.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hy))
  have hR := hd.hasFDerivAt.clm_apply R.hasFDerivAt
  have hL := hd.hasFDerivAt.clm_apply L.hasFDerivAt
  change HasFDerivAt (fun y : Matrix (Fin 2) (Fin 2) ℂ => fderiv ℝ φ y (y * Y))
    (fderiv ℝ φ g ∘L R + (fderiv ℝ (fderiv ℝ φ) g).flip (g*Y)) g at hR
  change HasFDerivAt (fun y : Matrix (Fin 2) (Fin 2) ℂ => fderiv ℝ φ y (X * y))
    (fderiv ℝ φ g ∘L L + (fderiv ℝ (fderiv ℝ φ) g).flip (X*g)) g at hL
  rw [matrixLeftDerivative_eq_fderiv X _ g
      ((matrixRightDerivative_smooth Y φ hO hφ).differentiableOn (by simp) |>.differentiableAt (hO.mem_nhds hg)),
    matrixRightDerivative_eq_fderiv Y _ g
      ((matrixLeftDerivative_smooth X φ hO hφ).differentiableOn (by simp) |>.differentiableAt (hO.mem_nhds hg)),
    heR.fderiv_eq, heL.fderiv_eq, hR.fderiv, hL.fderiv]
  change fderiv ℝ φ g ((X*g)*Y) + fderiv ℝ (fderiv ℝ φ) g (X*g) (g*Y) =
    fderiv ℝ φ g (X*(g*Y)) + fderiv ℝ (fderiv ℝ φ) g (g*Y) (X*g)
  rw [Matrix.mul_assoc, (hφ.contDiffAt (hO.mem_nhds hg)).isSymmSndFDerivAt (by simp)]

private theorem native_acceleration :
    basisMatrix 0 * basisMatrix 0 - basisMatrix 1 * basisMatrix 1 +
      (2 : ℝ) • (basisMatrix 4 * basisMatrix 2 + basisMatrix 2 * basisMatrix 4 -
        basisMatrix 5 * basisMatrix 3 - basisMatrix 3 * basisMatrix 5) =
          (6 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMatrix, sl2Matrix, Complex.real_smul] <;> ring

private theorem acceleration_contraction
    (L : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ j : Fin 3, L (g * (noncompactMatrix j * noncompactMatrix j))) -
      (∑ j : Fin 3, L (g * (compactMatrix j * compactMatrix j))) =
    (1 / 2 : ℂ) *
      (L (g * (basisMatrix 0 * basisMatrix 0)) - L (g * (basisMatrix 1 * basisMatrix 1)) +
       2 * (L (g * (basisMatrix 4 * basisMatrix 2)) + L (g * (basisMatrix 2 * basisMatrix 4)) -
         L (g * (basisMatrix 5 * basisMatrix 3)) - L (g * (basisMatrix 3 * basisMatrix 5)))) := by
  have hp := RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.pauli_square_sum
  have hh := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => L (g * m)) hp
  have hn := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => L (g * m)) native_acceleration
  simp only [Matrix.mul_sub, Matrix.mul_sum, Matrix.mul_add, Matrix.mul_smul, map_sub, map_add,
    map_sum, map_smul, Complex.real_smul, mul_one] at hh hn
  rw [hh]
  have he : L ((3 : ℂ) • g) = (3 : ℂ) * L g := by
    change L ((3 : ℝ) • g) = _
    simp [Complex.real_smul]
  rw [he]
  norm_num only [Complex.ofReal_ofNat] at hn
  linear_combination -((1 / 2 : ℂ) * hn)

 theorem six_flow_pauli_normalization
    (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ O) :
    -((1 : ℂ) / 4) *
      (matrixRightDerivative (basisMatrix 0) (matrixRightDerivative (basisMatrix 0) φ) g -
       matrixRightDerivative (basisMatrix 1) (matrixRightDerivative (basisMatrix 1) φ) g +
       2 * (matrixRightDerivative (basisMatrix 2) (matrixRightDerivative (basisMatrix 4) φ) g +
         matrixRightDerivative (basisMatrix 4) (matrixRightDerivative (basisMatrix 2) φ) g -
         matrixRightDerivative (basisMatrix 3) (matrixRightDerivative (basisMatrix 5) φ) g -
         matrixRightDerivative (basisMatrix 5) (matrixRightDerivative (basisMatrix 3) φ) g)) =
    -((1 : ℂ) / 2) *
      ((∑ j : Fin 3, matrixRightDerivative (noncompactMatrix j)
        (matrixRightDerivative (noncompactMatrix j) φ) g) -
      (∑ j : Fin 3, matrixRightDerivative (compactMatrix j)
        (matrixRightDerivative (compactMatrix j) φ) g)) := by
  simp_rw [matrixRightDerivative_twice _ _ φ hO hφ g hg]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [show (∑ j : Fin 3, fderiv ℝ (fderiv ℝ φ) g (g * noncompactMatrix j) (g * noncompactMatrix j)) +
      (∑ j : Fin 3, fderiv ℝ φ g (g * (noncompactMatrix j * noncompactMatrix j))) -
      ((∑ j : Fin 3, fderiv ℝ (fderiv ℝ φ) g (g * compactMatrix j) (g * compactMatrix j)) +
        ∑ j : Fin 3, fderiv ℝ φ g (g * (compactMatrix j * compactMatrix j))) =
      ((∑ j : Fin 3, fderiv ℝ (fderiv ℝ φ) g (g * noncompactMatrix j) (g * noncompactMatrix j)) -
        ∑ j : Fin 3, fderiv ℝ (fderiv ℝ φ) g (g * compactMatrix j) (g * compactMatrix j)) +
      ((∑ j : Fin 3, fderiv ℝ φ g (g * (noncompactMatrix j * noncompactMatrix j))) -
        ∑ j : Fin 3, fderiv ℝ φ g (g * (compactMatrix j * compactMatrix j))) by ring]
  rw [quadratic_contraction, acceleration_contraction]
  ring

private theorem native_normalized_induction_casimir
    (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    let φ := KPCplxPrincipalSeriesCharts.matrixFunction f.val;
    -((1 : ℂ) / 4) *
      (matrixRightDerivative (basisMatrix 0) (matrixRightDerivative (basisMatrix 0) φ) g.val -
       matrixRightDerivative (basisMatrix 1) (matrixRightDerivative (basisMatrix 1) φ) g.val +
       2 * (matrixRightDerivative (basisMatrix 2) (matrixRightDerivative (basisMatrix 4) φ) g.val +
         matrixRightDerivative (basisMatrix 4) (matrixRightDerivative (basisMatrix 2) φ) g.val -
         matrixRightDerivative (basisMatrix 3) (matrixRightDerivative (basisMatrix 5) φ) g.val -
         matrixRightDerivative (basisMatrix 5) (matrixRightDerivative (basisMatrix 3) φ) g.val)) =
    ((1 - 4 * s^2 : ℝ) : ℂ) * f g := by
  dsimp only
  let O := {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0}
  have hO : IsOpen O := by
    apply isOpen_ne.preimage
    fun_prop
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff s f.val).mp f.property).2
  have hg : g.val ∈ O := Matrix.GeneralLinearGroup.det_ne_zero g
  rw [six_flow_pauli_normalization _ hO hf _ hg]
  have hn (j : Fin 3) :
      matrixRightDerivative (noncompactMatrix j)
        (matrixRightDerivative (noncompactMatrix j) (KPCplxPrincipalSeriesCharts.matrixFunction f.val)) g.val =
      localDerivative s (false,j) (localDerivative s (false,j) f) g := by
    rw [matrixRightDerivative_twice _ _ _ hO hf _ hg]
    exact (RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.localDerivative_twice_fderiv s (false,j) f g).symm
  have hc (j : Fin 3) :
      matrixRightDerivative (compactMatrix j)
        (matrixRightDerivative (compactMatrix j) (KPCplxPrincipalSeriesCharts.matrixFunction f.val)) g.val =
      localDerivative s (true,j) (localDerivative s (true,j) f) g := by
    rw [matrixRightDerivative_twice _ _ _ hO hf _ hg]
    exact (RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.localDerivative_twice_fderiv s (true,j) f g).symm
  simp_rw [hn, hc]
  have he := congrArg (fun v : KPCplxPrincipalSeriesCharts.PrincipalSeries s => v g)
    (RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.normalized_casimir s f)
  simp only [Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply,
    SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at he
  rw [he]
  push_cast
  ring

private theorem native_induction_spectral_coordinate
    (x : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries (1/6+x))
    (g : KPCplxCharacterHaar.ComplexGL2) :
    let φ := KPCplxPrincipalSeriesCharts.matrixFunction f.val;
    -((1 : ℂ) / 4) *
      (matrixRightDerivative (basisMatrix 0) (matrixRightDerivative (basisMatrix 0) φ) g.val -
       matrixRightDerivative (basisMatrix 1) (matrixRightDerivative (basisMatrix 1) φ) g.val +
       2 * (matrixRightDerivative (basisMatrix 2) (matrixRightDerivative (basisMatrix 4) φ) g.val +
         matrixRightDerivative (basisMatrix 4) (matrixRightDerivative (basisMatrix 2) φ) g.val -
         matrixRightDerivative (basisMatrix 3) (matrixRightDerivative (basisMatrix 5) φ) g.val -
         matrixRightDerivative (basisMatrix 5) (matrixRightDerivative (basisMatrix 3) φ) g.val)) =
    KPContinuation.spectralCoordinate 1 (x : ℂ) * f g := by
  dsimp only
  rw [native_normalized_induction_casimir]
  unfold KPContinuation.spectralCoordinate
  push_cast
  ring

 def rightOmega (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) : Matrix (Fin 2) (Fin 2) ℂ → ℂ :=
  fun g => (∑ j : Fin 3, matrixRightDerivative (noncompactMatrix j)
    (matrixRightDerivative (noncompactMatrix j) φ) g) -
    ∑ j : Fin 3, matrixRightDerivative (compactMatrix j)
      (matrixRightDerivative (compactMatrix j) φ) g
 def leftOmega (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) : Matrix (Fin 2) (Fin 2) ℂ → ℂ :=
  fun g => (∑ j : Fin 3, matrixLeftDerivative (noncompactMatrix j)
    (matrixLeftDerivative (noncompactMatrix j) φ) g) -
    ∑ j : Fin 3, matrixLeftDerivative (compactMatrix j)
      (matrixLeftDerivative (compactMatrix j) φ) g

 theorem matrix_omega_left_right
    (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : KPCplxCharacterHaar.ComplexGL2) (hg : g.val ∈ O) :
    rightOmega φ g.val = leftOmega φ g.val := by
  unfold rightOmega leftOmega
  simp_rw [matrixRightDerivative_twice _ _ φ hO hφ g.val hg,
    matrixLeftDerivative_twice _ _ φ hO hφ g.val hg]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hp := RepresentationTheory.KPSmoothCoreCasimirEnergyHessianCovariance.PauliContraction.pauli_contraction_left_right
    (fderiv ℝ (fderiv ℝ φ) g.val) g
  have haccR : (∑ j : Fin 3, fderiv ℝ φ g.val (g.val * (noncompactMatrix j * noncompactMatrix j))) -
      (∑ j : Fin 3, fderiv ℝ φ g.val (g.val * (compactMatrix j * compactMatrix j))) =
      fderiv ℝ φ g.val ((3 : ℝ) • g.val) := by
    rw [← map_sum, ← map_sum, ← map_sub, ← Matrix.mul_sum, ← Matrix.mul_sum,
      ← Matrix.mul_sub, RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.pauli_square_sum,
      Matrix.mul_smul, mul_one]
    rfl
  have haccL : (∑ j : Fin 3, fderiv ℝ φ g.val ((noncompactMatrix j * noncompactMatrix j) * g.val)) -
      (∑ j : Fin 3, fderiv ℝ φ g.val ((compactMatrix j * compactMatrix j) * g.val)) =
      fderiv ℝ φ g.val ((3 : ℝ) • g.val) := by
    rw [← map_sum, ← map_sum, ← map_sub, ← Matrix.sum_mul, ← Matrix.sum_mul,
      ← Matrix.sub_mul, RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.pauli_square_sum,
      Matrix.smul_mul, one_mul]
    rfl
  linear_combination hp + haccR - haccL

private theorem matrixRightDerivative_leftOmega
    (X : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ O) :
    matrixRightDerivative X (leftOmega φ) g =
      (∑ j : Fin 3, matrixRightDerivative X (matrixLeftDerivative (noncompactMatrix j)
        (matrixLeftDerivative (noncompactMatrix j) φ)) g) -
      ∑ j : Fin 3, matrixRightDerivative X (matrixLeftDerivative (compactMatrix j)
        (matrixLeftDerivative (compactMatrix j) φ)) g := by
  have hd (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      HasDerivAt (fun t : ℝ => matrixLeftDerivative Y (matrixLeftDerivative Y φ)
        (g * NormedSpace.exp ((t:ℂ) • X)))
          (matrixRightDerivative X (matrixLeftDerivative Y (matrixLeftDerivative Y φ)) g) 0 := by
    have hs := matrixLeftDerivative_smooth Y _ hO (matrixLeftDerivative_smooth Y φ hO hφ)
    have hdiff := (hs.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hg)
    rw [matrixRightDerivative_eq_fderiv X _ g hdiff]
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 (exp_path_hasDeriv g X) (by simp)
  have he := (HasDerivAt.fun_sum (fun j (_hj : j ∈ Finset.univ) => hd (noncompactMatrix j))).sub
    (HasDerivAt.fun_sum (fun j (_hj : j ∈ Finset.univ) => hd (compactMatrix j)))
  exact he.deriv

private theorem matrix_leftOmega_right_commutes
    (X : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ O) :
    leftOmega (matrixRightDerivative X φ) g = matrixRightDerivative X (leftOmega φ) g := by
  rw [matrixRightDerivative_leftOmega X φ hO hφ g hg]
  unfold leftOmega
  have he (Y : Matrix (Fin 2) (Fin 2) ℂ) :
      matrixLeftDerivative Y (matrixLeftDerivative Y (matrixRightDerivative X φ)) g =
      matrixRightDerivative X (matrixLeftDerivative Y (matrixLeftDerivative Y φ)) g := by
    have heq : matrixLeftDerivative Y (matrixRightDerivative X φ) =ᶠ[nhds g]
        matrixRightDerivative X (matrixLeftDerivative Y φ) := by
      filter_upwards [hO.mem_nhds hg] with a ha
      exact matrix_mixed_left_right Y X φ hO hφ a ha
    have hds := matrixRightDerivative_smooth X _ hO (matrixLeftDerivative_smooth Y φ hO hφ)
    have hdiff := (hds.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hg)
    have hds' := matrixLeftDerivative_smooth Y _ hO (matrixRightDerivative_smooth X φ hO hφ)
    have hdiff' := (hds'.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hg)
    rw [matrixLeftDerivative_eq_fderiv Y _ g hdiff', heq.fderiv_eq,
      ← matrixLeftDerivative_eq_fderiv Y _ g hdiff]
    exact matrix_mixed_left_right Y X (matrixLeftDerivative Y φ) hO
      (matrixLeftDerivative_smooth Y φ hO hφ) g hg
  simp_rw [he]

private theorem matrix_omega_germ_left_right
    (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : KPCplxCharacterHaar.ComplexGL2) (hg : g.val ∈ O) :
    rightOmega φ =ᶠ[nhds g.val] leftOmega φ := by
  have hGL : ∀ᶠ a : Matrix (Fin 2) (Fin 2) ℂ in nhds g.val, a.det ≠ 0 := by
    apply (isOpen_ne.preimage (by fun_prop : Continuous (fun a : Matrix (Fin 2) (Fin 2) ℂ => a.det))).mem_nhds
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  filter_upwards [hO.mem_nhds hg, hGL] with a ha hdet
  exact matrix_omega_left_right φ hO hφ (Matrix.GeneralLinearGroup.mkOfDetNeZero a hdet) ha

 theorem matrix_omega_smooth
    (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) : ContDiffOn ℝ (⊤ : ℕ∞) (rightOmega φ) O := by
  apply ContDiffOn.sub <;> apply ContDiffOn.sum <;> intro j hj
  · exact matrixRightDerivative_smooth _ _ hO (matrixRightDerivative_smooth _ φ hO hφ)
  · exact matrixRightDerivative_smooth _ _ hO (matrixRightDerivative_smooth _ φ hO hφ)

private theorem matrix_leftOmega_smooth
    (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) : ContDiffOn ℝ (⊤ : ℕ∞) (leftOmega φ) O := by
  apply ContDiffOn.sub <;> apply ContDiffOn.sum <;> intro j hj
  · exact matrixLeftDerivative_smooth _ _ hO (matrixLeftDerivative_smooth _ φ hO hφ)
  · exact matrixLeftDerivative_smooth _ _ hO (matrixLeftDerivative_smooth _ φ hO hφ)

 theorem matrix_omega_right_commutes
    (X : Matrix (Fin 2) (Fin 2) ℂ) (φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ O) (g : KPCplxCharacterHaar.ComplexGL2) (hg : g.val ∈ O) :
    rightOmega (matrixRightDerivative X φ) g.val = matrixRightDerivative X (rightOmega φ) g.val := by
  rw [matrix_omega_left_right _ hO (matrixRightDerivative_smooth X φ hO hφ) g hg,
    matrix_leftOmega_right_commutes X φ hO hφ g.val hg,
    matrixRightDerivative_eq_fderiv X _ g.val
      ((matrix_leftOmega_smooth φ hO hφ).differentiableOn (by simp) |>.differentiableAt (hO.mem_nhds hg)),
    matrixRightDerivative_eq_fderiv X _ g.val
      ((matrix_omega_smooth φ hO hφ).differentiableOn (by simp) |>.differentiableAt (hO.mem_nhds hg)),
    (matrix_omega_germ_left_right φ hO hφ g hg).fderiv_eq]

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
open KPReferenceChange.StandardComplexImage.FamilyCorrect
private theorem matrix_function_at_GL (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f g.val = f g := by
  simp only [matrixFunction]
  rw [dite_eq_left (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  exact Units.ext rfl

private theorem matrix_function_derivative (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixRightDerivative X (matrixFunction f) g.val =
      deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 := by
  unfold matrixRightDerivative
  congr 1
  funext t
  exact matrix_function_at_GL f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))

private theorem matrix_function_derivative_twice (X Y : Matrix (Fin 2) (Fin 2) ℂ)
    (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixRightDerivative X (matrixRightDerivative Y (matrixFunction f)) g.val =
      deriv (fun t : ℝ => deriv (fun u : ℝ => f
        ((g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X)) *
          KPSmoothActualFlowData.matrixExponential ((u : ℂ) • Y))) 0) 0 := by
  unfold matrixRightDerivative
  congr 1
  funext t
  exact matrix_function_derivative Y f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))

 def nativeMatrixCasimir (f : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  -((1 : ℂ) / 4) *
    (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 0)
      (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 0) f) g -
     matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 1)
      (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 1) f) g +
     2 * (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 2)
      (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 4) f) g +
      matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 4)
      (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 2) f) g -
      matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 3)
      (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 5) f) g -
      matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 5)
      (matrixRightDerivative (KPSmoothActualFlowData.basisMatrix 3) f) g))

private theorem real_twisted_casimir (f : PrincipalSeries positiveParameter)
    (r : ℝ) (g : ComplexGL2) :
    nativeMatrixCasimir (matrixFunction (plusValue f r)) g.val =
      KPContinuation.spectralCoordinate 1 r * plusValue f r g := by
  exact native_induction_spectral_coordinate r
    (show PrincipalSeries (1/6+r) from realTwisted f r) g

open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming invDomain → invDomain
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming inv_open → inv_open
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming phase → phase
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming phase_smooth → phase_smooth
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming exponent → exponent
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming atom → KPContHolomorphicKGeneration.atom
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming Separated → Separated
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming separated_smooth → separated_smooth
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming separated_analytic → separated_analytic
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming separated_derivative → separated_derivative
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming direction → direction
open _root_.DedekindZetaZeroFree.KPContHolomorphicKGeneration renaming matrix_eventually_eq → matrix_eventually_eq

private theorem plusValue_separated (f : PrincipalSeries positiveParameter) :
    ∃ H : ℂ → Matrix (Fin 2) (Fin 2) ℂ → ℂ,
      Separated H ∧ ∀ s g, plusValue f s g = H s g.val := by
  let B := matrixFunction (sphericalSection positiveParameter)
  let A := matrixFunction f
  let b := fun m => A m / B m
  have hA := ((principalSeries_mem_iff _ _).mp f.property).2
  have hB := ((principalSeries_mem_iff _ _).mp (sphericalSection positiveParameter).property).2
  have hn : ∀ m ∈ invDomain, B m ≠ 0 := by
    intro m hm
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero m hm
    change matrixFunction (sphericalSection positiveParameter) g.val ≠ 0
    rw [matrix_function_at_GL, ← KPContHolomorphicKGeneration.complexSpherical_zero]
    exact Complex.exp_ne_zero _
  have hb : ContDiffOn ℝ ∞ b invDomain := by
    dsimp only [b]
    simp only [div_eq_mul_inv]
    exact hA.mul (hB.inv hn)
  refine ⟨KPContHolomorphicKGeneration.atom (fun _ => 1) b,
    Separated.atom _ _ analyticOnNhd_const hb, ?_⟩
  intro s g
  have hlog : (Real.log (height g) : ℂ) = 2 * phase g.val := by
    unfold height phase
    rw [Real.log_pow]
    push_cast
    rfl
  have hbase : B g.val = Complex.exp (exponent 0 * phase g.val) := by
    dsimp only [B]
    rw [matrix_function_at_GL, ← KPContHolomorphicKGeneration.complexSpherical_zero]
    rfl
  have hcoeff : exponent s = s * 2 + exponent 0 := by
    unfold exponent
    ring
  dsimp only [KPContHolomorphicKGeneration.atom, b]
  rw [hcoeff, add_mul, Complex.exp_add, ← hbase]
  dsimp only [A]
  rw [matrix_function_at_GL]
  have hg : B g.val ≠ 0 := hn g.val (Matrix.GeneralLinearGroup.det_ne_zero g)
  unfold plusValue twist
  rw [hlog]
  field_simp

private theorem separated_matrix_derivative {φ : ℂ → Matrix (Fin 2) (Fin 2) ℂ → ℂ}
    {H : ℂ → Matrix (Fin 2) (Fin 2) ℂ → ℂ} (hH : Separated H)
    (he : ∀ s m, m ∈ invDomain → φ s m = H s m) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ H', Separated H' ∧ ∀ s m, m ∈ invDomain →
      matrixRightDerivative X (φ s) m = H' s m := by
  obtain ⟨H',hH',hd⟩ := separated_derivative hH X
  refine ⟨H',hH',?_⟩
  intro s m hm
  have hgerm : φ s =ᶠ[nhds m] H s :=
    Filter.Eventually.mono (inv_open.mem_nhds hm) (fun a ha => he s a ha)
  have hdiff := ((separated_smooth hH s).contDiffAt (inv_open.mem_nhds hm)).differentiableAt (by simp)
  rw [matrixRightDerivative_eq_fderiv X _ m (hdiff.congr_of_eventuallyEq hgerm),
    hgerm.fderiv_eq]
  exact (hd s m hm).symm

private theorem plusValue_matrix_word_separated (f : PrincipalSeries positiveParameter)
    (w : List (Matrix (Fin 2) (Fin 2) ℂ)) :
    ∃ H : ℂ → Matrix (Fin 2) (Fin 2) ℂ → ℂ, Separated H ∧
      ∀ s m, m ∈ invDomain →
        w.foldr matrixRightDerivative (matrixFunction (plusValue f s)) m = H s m := by
  induction w with
  | nil =>
    obtain ⟨H,hH,he⟩ := plusValue_separated f
    refine ⟨H,hH,?_⟩
    intro s m hm
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero m hm
    exact (matrix_function_at_GL (plusValue f s) g).trans (he s g)
  | cons X w ih =>
    obtain ⟨H,hH,he⟩ := ih
    exact separated_matrix_derivative hH he X

private theorem plusValue_matrix_word_analytic (f : PrincipalSeries positiveParameter)
    (w : List (Matrix (Fin 2) (Fin 2) ℂ)) (g : ComplexGL2) :
    AnalyticOnNhd ℂ (fun s => w.foldr matrixRightDerivative
      (matrixFunction (plusValue f s)) g.val) Set.univ := by
  obtain ⟨H,hH,he⟩ := plusValue_matrix_word_separated f w
  simp_rw [he _ _ (Matrix.GeneralLinearGroup.det_ne_zero g)]
  exact separated_analytic hH _

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming entire_of_real → entire_of_real

private theorem complex_twisted_casimir (f : PrincipalSeries positiveParameter)
    (s : ℂ) (g : ComplexGL2) :
    nativeMatrixCasimir (matrixFunction (plusValue f s)) g.val =
      KPContinuation.spectralCoordinate 1 s * plusValue f s g := by
  have hL : AnalyticOnNhd ℂ (fun s => nativeMatrixCasimir (matrixFunction (plusValue f s)) g.val) Set.univ := by
    unfold nativeMatrixCasimir
    have hw (i j : Fin 6) := plusValue_matrix_word_analytic f
      [KPSmoothActualFlowData.basisMatrix i,KPSmoothActualFlowData.basisMatrix j] g
    simp only [List.foldr_cons, List.foldr_nil] at hw
    fun_prop
  have hR : AnalyticOnNhd ℂ (fun s => KPContinuation.spectralCoordinate 1 s * plusValue f s g) Set.univ := by
    have hspec : AnalyticOnNhd ℂ (KPContinuation.spectralCoordinate 1) Set.univ := by
      unfold KPContinuation.spectralCoordinate
      fun_prop
    have hp : AnalyticOnNhd ℂ (fun s => plusValue f s g) Set.univ := by
      unfold plusValue twist
      exact ((analyticOnNhd_id.mul analyticOnNhd_const).cexp).mul analyticOnNhd_const
    exact hspec.mul hp
  exact congrFun (entire_of_real hL hR (fun r => real_twisted_casimir f r g)) s

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry renaming insertion_commutes_finite → insertion_commutes_finite
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry renaming update_mul_single → update_mul_single
open KPSmoothActualFlowData

 theorem native_flow_single (F : Type) [Field F] [NumberField F]
    (w : NumberField.InfinitePlace F) (j : Fin 6) (t : ℝ) :
    flow F (w,j) t = Function.update (fun _ => (1 : Matrix.ProjGenLinGroup (Fin 2) ℂ)) w
      (Matrix.ProjGenLinGroup.mk (matrixExponential ((t : ℂ) • basisMatrix j))) := by
  funext v
  unfold flow exponential
  have hM : sl2Matrix (fun k => if (v,k) = (w,j) then t else 0) =
      if v = w then (t : ℂ) • basisMatrix j else 0 := by
    by_cases hv : v = w
    · subst v
      fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [sl2Matrix, basisMatrix, mul_comm]
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Matrix, hv]
  rw [hM]
  by_cases hv : v = w
  · subst v; simp
  · simp [hv, matrixExponential]

private theorem native_slice_derivative
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : NumberField.InfinitePlace F) (j : Fin 6) (a : GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ) (f : ComplexGL2 → ℂ)
    (hf : ∀ g, h (archimedeanInsertion F ζ hζ
      (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) = f g)
    (g : ComplexGL2) :
    KPMsGreenFlux.rightDerivative F ζ hζ w j h
      (archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) =
      matrixRightDerivative (basisMatrix j) (matrixFunction f) g.val := by
  rw [matrix_function_derivative]
  unfold KPMsGreenFlux.rightDerivative
  congr 1
  funext t
  rw [native_flow_single]
  let e := Matrix.ProjGenLinGroup.mk (matrixExponential ((t : ℂ) • basisMatrix j))
  have hc := insertion_commutes_finite F ζ hζ (Function.update (fun _ => 1) w e) c
  have hm := (archimedean_insertion_properties F ζ hζ).2.1
  rw [mul_assoc, hc.eq.symm, ← mul_assoc, ← hm, update_mul_single, ← map_mul]
  exact hf _

private theorem native_slice_twice
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : NumberField.InfinitePlace F) (i j : Fin 6) (a : GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ) (f : ComplexGL2 → ℂ)
    (hf : ∀ g, h (archimedeanInsertion F ζ hζ
      (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) = f g)
    (g : ComplexGL2) :
    KPMsGreenFlux.rightDerivative F ζ hζ w i
      (KPMsGreenFlux.rightDerivative F ζ hζ w j h)
      (archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val) =
      matrixRightDerivative (basisMatrix i)
        (matrixRightDerivative (basisMatrix j) (matrixFunction f)) g.val := by
  rw [matrix_function_derivative_twice]
  unfold KPMsGreenFlux.rightDerivative
  congr 1
  funext t
  rw [native_flow_single]
  let e := Matrix.ProjGenLinGroup.mk (matrixExponential ((t : ℂ) • basisMatrix i))
  have hc := insertion_commutes_finite F ζ hζ (Function.update (fun _ => 1) w e) c
  have hm := (archimedean_insertion_properties F ζ hζ).2.1
  rw [mul_assoc, hc.eq.symm, ← mul_assoc, ← hm, update_mul_single, ← map_mul]
  exact (native_slice_derivative F ζ hζ w j a c h f hf
    (g * matrixExponential ((t : ℂ) • basisMatrix i))).trans
      (matrix_function_derivative _ f _)

private theorem matrix_derivative_sum {ι : Type*} [Fintype ι]
    (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : ι → Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) O)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ O) :
    matrixRightDerivative X (fun a => ∑ i, f i a) g =
      ∑ i, matrixRightDerivative X (f i) g := by
  rw [matrixRightDerivative_eq_fderiv X _ g
    (((ContDiffOn.sum (fun i _ => hf i)).contDiffAt (hO.mem_nhds hg)).differentiableAt (by simp))]
  have hd (i : ι) := ((hf i).contDiffAt (hO.mem_nhds hg)).differentiableAt (by simp)
  have hs : HasFDerivAt (fun a => ∑ i, f i a) (∑ i, fderiv ℝ (f i) g) g :=
    HasFDerivAt.fun_sum (fun i _ => (hd i).hasFDerivAt)
  rw [hs.fderiv]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (matrixRightDerivative_eq_fderiv X _ g (hd i)).symm

private theorem matrix_derivative_const_mul (X : Matrix (Fin 2) (Fin 2) ℂ)
    (c : ℂ) (f : Matrix (Fin 2) (Fin 2) ℂ → ℂ) :
    matrixRightDerivative X (fun a => c * f a) = fun a => c * matrixRightDerivative X f a := by
  funext a
  exact deriv_const_mul_field c

private theorem matrix_casimir_sum {ι : Type*} [Fintype ι]
    (f : ι → Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {O : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hO : IsOpen O)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) O)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g ∈ O) :
    nativeMatrixCasimir (fun a => ∑ i, f i a) g = ∑ i, nativeMatrixCasimir (f i) g := by
  have hh (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
      matrixRightDerivative X (matrixRightDerivative Y (fun a => ∑ i, f i a)) g =
        ∑ i, matrixRightDerivative X (matrixRightDerivative Y (f i)) g := by
    have hs : matrixRightDerivative Y (fun a => ∑ i, f i a) =ᶠ[nhds g]
        (fun a => ∑ i, matrixRightDerivative Y (f i) a) := by
      filter_upwards [hO.mem_nhds hg] with a ha
      exact matrix_derivative_sum Y f hO hf a ha
    have hsum : ContDiffOn ℝ ∞ (fun a => ∑ i, f i a) O := ContDiffOn.sum (fun i _ => hf i)
    have hA := matrixRightDerivative_smooth Y _ hO hsum
    have hB : ContDiffOn ℝ ∞ (fun a => ∑ i, matrixRightDerivative Y (f i) a) O :=
      ContDiffOn.sum (fun i _ => matrixRightDerivative_smooth Y _ hO (hf i))
    rw [matrixRightDerivative_eq_fderiv X _ g
      ((hA.contDiffAt (hO.mem_nhds hg)).differentiableAt (by simp)), hs.fderiv_eq,
      ← matrixRightDerivative_eq_fderiv X _ g
        ((hB.contDiffAt (hO.mem_nhds hg)).differentiableAt (by simp))]
    exact matrix_derivative_sum X _ hO
      (fun i => matrixRightDerivative_smooth Y _ hO (hf i)) g hg
  unfold nativeMatrixCasimir
  simp only [hh]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.mul_sum]

private theorem matrix_casimir_const_mul (c : ℂ) (f : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    nativeMatrixCasimir (fun a => c * f a) g = c * nativeMatrixCasimir f g := by
  unfold nativeMatrixCasimir
  simp_rw [matrix_derivative_const_mul]
  ring

private theorem matrixFunction_sum {ι : Type*} [Fintype ι] (f : ι → ComplexGL2 → ℂ) :
    matrixFunction (fun g => ∑ i, f i g) = fun m => ∑ i, matrixFunction (f i) m := by
  funext m
  unfold matrixFunction
  split_ifs <;> simp

private theorem matrixFunction_const_mul (c : ℂ) (f : ComplexGL2 → ℂ) :
    matrixFunction (fun g => c * f g) = fun m => c * matrixFunction f m := by
  funext m
  unfold matrixFunction
  split_ifs <;> simp

private theorem plusValue_matrix_smooth (f : PrincipalSeries positiveParameter) (s : ℂ) :
    ContDiffOn ℝ ∞ (matrixFunction (plusValue f s)) invDomain := by
  obtain ⟨H,hH,he⟩ := plusValue_separated f
  apply (separated_smooth hH s).congr
  intro m hm
  let g := Matrix.GeneralLinearGroup.mkOfDetNeZero m hm
  exact (matrix_function_at_GL (plusValue f s) g).trans (he s g)

private theorem native_flat_slot_casimir
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (s : ℂ) (w : NumberField.InfinitePlace F)
    (a : NumberField.InfinitePlace F → ComplexGL2)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    let h := (KPContFlatSourceRecipe.flatR F ζ hζ s t).val;
    let g := archimedeanInsertion F ζ hζ (fun v => Matrix.ProjGenLinGroup.mk (a v)) * c.val;
    -((1 : ℂ) / 4) *
      (KPMsGreenFlux.rightDerivative F ζ hζ w 0 (KPMsGreenFlux.rightDerivative F ζ hζ w 0 h) g -
       KPMsGreenFlux.rightDerivative F ζ hζ w 1 (KPMsGreenFlux.rightDerivative F ζ hζ w 1 h) g +
       2 * (KPMsGreenFlux.rightDerivative F ζ hζ w 2 (KPMsGreenFlux.rightDerivative F ζ hζ w 4 h) g +
        KPMsGreenFlux.rightDerivative F ζ hζ w 4 (KPMsGreenFlux.rightDerivative F ζ hζ w 2 h) g -
        KPMsGreenFlux.rightDerivative F ζ hζ w 3 (KPMsGreenFlux.rightDerivative F ζ hζ w 5 h) g -
        KPMsGreenFlux.rightDerivative F ζ hζ w 5 (KPMsGreenFlux.rightDerivative F ζ hζ w 3 h) g)) =
      KPContinuation.spectralCoordinate 1 s * h g := by
  obtain ⟨U,n,v,f,_,_,he⟩ := KPGlobalResidualConstruction.ActualRaisingGeometry.actual_source_flat_finite_pure_core F ζ hζ t
  let h := (KPContFlatSourceRecipe.flatR F ζ hζ s t).val
  let A : GInfinity F := fun u => Matrix.ProjGenLinGroup.mk (a u)
  let d : Fin n → ℂ := fun j => (KPContFlatSourceRecipe.flatR F ζ hζ s (v j).val).val c.val *
    ∏ u ∈ Finset.univ.erase w, plusValue (f j u) s (a u)
  let ψ : ComplexGL2 → ℂ := fun g => ∑ j, d j * plusValue (f j w) s g
  have hs : ∀ g : ComplexGL2,
      h (archimedeanInsertion F ζ hζ (Function.update A w (Matrix.ProjGenLinGroup.mk g)) * c.val) = ψ g := by
    intro g
    have hupdate : Function.update A w (Matrix.ProjGenLinGroup.mk g) =
        fun u => Matrix.ProjGenLinGroup.mk ((Function.update a w g) u) := by
      funext u
      by_cases hu : u = w <;> simp [A,hu]
    rw [hupdate]
    change (KPContFlatSourceRecipe.flatR F ζ hζ s t).val _ = _
    rw [he]
    apply Finset.sum_congr rfl
    intro j _
    have htw (u : NumberField.InfinitePlace F) (g : ComplexGL2) :
        Complex.exp (s * (KPContFlatLogNormSmooth.complexMatrixLogNorm g.val : ℂ)) * f j u g =
          plusValue (f j u) s g := rfl
    simp_rw [htw]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
    simp only [Function.update_self]
    have herase : (∏ u ∈ Finset.univ.erase w, plusValue (f j u) s ((Function.update a w g) u)) =
        ∏ u ∈ Finset.univ.erase w, plusValue (f j u) s (a u) := by
      apply Finset.prod_congr rfl
      intro u hu
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
    rw [herase]
    dsimp only [ψ,d]
    ring
  have hA : Function.update A w (Matrix.ProjGenLinGroup.mk (a w)) = A := by
    exact Function.update_eq_self w A
  have hh (i j : Fin 6) : KPMsGreenFlux.rightDerivative F ζ hζ w i
      (KPMsGreenFlux.rightDerivative F ζ hζ w j h)
      (archimedeanInsertion F ζ hζ A * c.val) =
      matrixRightDerivative (basisMatrix i) (matrixRightDerivative (basisMatrix j) (matrixFunction ψ)) (a w).val := by
    simpa only [hA] using native_slice_twice F ζ hζ w i j A c h ψ hs (a w)
  dsimp only
  change -((1 : ℂ)/4) *
    (KPMsGreenFlux.rightDerivative F ζ hζ w 0 (KPMsGreenFlux.rightDerivative F ζ hζ w 0 h) (archimedeanInsertion F ζ hζ A * c.val) -
     KPMsGreenFlux.rightDerivative F ζ hζ w 1 (KPMsGreenFlux.rightDerivative F ζ hζ w 1 h) (archimedeanInsertion F ζ hζ A * c.val) +
     2 * (KPMsGreenFlux.rightDerivative F ζ hζ w 2 (KPMsGreenFlux.rightDerivative F ζ hζ w 4 h) (archimedeanInsertion F ζ hζ A * c.val) +
      KPMsGreenFlux.rightDerivative F ζ hζ w 4 (KPMsGreenFlux.rightDerivative F ζ hζ w 2 h) (archimedeanInsertion F ζ hζ A * c.val) -
      KPMsGreenFlux.rightDerivative F ζ hζ w 3 (KPMsGreenFlux.rightDerivative F ζ hζ w 5 h) (archimedeanInsertion F ζ hζ A * c.val) -
      KPMsGreenFlux.rightDerivative F ζ hζ w 5 (KPMsGreenFlux.rightDerivative F ζ hζ w 3 h) (archimedeanInsertion F ζ hζ A * c.val))) = _
  simp_rw [hh]
  change nativeMatrixCasimir (matrixFunction ψ) (a w).val = _
  have hψ : matrixFunction ψ = fun m => ∑ j, d j * matrixFunction (plusValue (f j w) s) m := by
    dsimp only [ψ]
    rw [matrixFunction_sum]
    simp_rw [matrixFunction_const_mul]
  rw [hψ, matrix_casimir_sum _ inv_open
    (fun j => contDiffOn_const.mul (plusValue_matrix_smooth (f j w) s)) _
      (Matrix.GeneralLinearGroup.det_ne_zero (a w))]
  simp_rw [matrix_casimir_const_mul, complex_twisted_casimir]
  have hval := hs (a w)
  rw [hA] at hval
  change _ = KPContinuation.spectralCoordinate 1 s * h (archimedeanInsertion F ζ hζ A * c.val)
  rw [hval]
  dsimp only [ψ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem actual_finite_pgl_factorization
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ∃ (a : NumberField.InfinitePlace F → ComplexGL2)
      (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
      g = archimedeanInsertion F ζ hζ (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val := by
  obtain ⟨e,he,_⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  let p := e.symm g
  let a : NumberField.InfinitePlace F → ComplexGL2 := fun w => (p.1 w).out
  have hc : p.2.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
    obtain ⟨x,hx,hxe⟩ := p.2.property
    refine Subgroup.mem_map.mpr ⟨x,?_,hxe⟩
    apply Subgroup.mem_iInf.mpr
    intro w
    exact hx w
  refine ⟨a,⟨p.2.val,hc⟩,?_⟩
  have ha : (fun w => Matrix.ProjGenLinGroup.mk (a w)) = p.1 := by
    funext w
    exact Quotient.out_eq _
  rw [ha]
  exact (e.apply_symm_apply g).symm.trans (he p.1 p.2)

 theorem native_flat_casimir
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    KPMsGreenFlux.casimir F ζ hζ (KPContFlatSourceRecipe.flatR F ζ hζ s t).val g =
      KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) s *
        (KPContFlatSourceRecipe.flatR F ζ hζ s t).val g := by
  obtain ⟨a,c,rfl⟩ := actual_finite_pgl_factorization F ζ hζ g
  unfold KPMsGreenFlux.casimir
  simp_rw [native_flat_slot_casimir F ζ hζ t s _ a c]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hd : KPCuspLogShape.dimension F = Fintype.card (NumberField.InfinitePlace F) := by
    change NumberField.InfinitePlace.nrComplexPlaces F = Fintype.card (NumberField.InfinitePlace F)
    exact (KPContFlatArchDiagonalMultiplier.complexDimension_eq F ζ hζ).symm.trans
      (KPContFlatArchDiagonalMultiplier.complexDimension_eq_card F ζ hζ)
  unfold KPContinuation.spectralCoordinate
  rw [hd]
  simp only [Finset.card_univ]
  push_cast
  ring

open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open RightFrame.PullbackWords
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualWordSeminorm renaming list_expansion → list_expansion
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualWordSeminorm renaming constant_word_iterated → constant_word_iterated
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualWordSeminorm renaming directional_map → directional_map

 theorem native_word_chart_jets
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : List (Fin (groupDimension F))) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (j : Fin m → Jet F),
      ∀ u : KPGlobalResidualConstruction.G F ζ hζ → ℂ,
        (∀ g, ContDiffOn ℝ ∞ (fun x => u (g * archChart F ζ hζ x)) (archDomain F)) →
        ∀ g, actualRightWord F ζ hζ w u g =
          ∑ k, c k * iteratedFDeriv ℝ (j k).1
            (fun x => u (g * archChart F ζ hζ x)) (archBase F) (j k).2 := by
  obtain ⟨O,fields,hO,hb,hOD,hfields,hreal⟩ := NativePositiveChart.actual_rightWord_chart_realization F ζ hζ
  obtain ⟨ts,_,hexp⟩ := list_expansion O hO fields hfields w
  let e := Module.finBasis ℝ (ArchCoordinates F)
  let j : Fin ts.length → Jet F := fun k => ⟨(ts.get k).2.length, fun i => e ((ts.get k).2.get i)⟩
  refine ⟨ts.length,fun k => ((ts.get k).1 (archBase F) : ℂ),j,?_⟩
  intro u hu g
  have hf : ContDiffOn ℝ ∞ (fun x => u (g * archChart F ζ hζ x)) O := (hu g).mono hOD
  have hbase : archChart F ζ hζ (archBase F) = 1 := by
    exact KPInterface.ResidueConstruction.Raw.archChart_base F ζ hζ
  have hr := hreal u hu w g (archBase F) hb
  rw [hbase,mul_one] at hr
  rw [hr, hexp _ hf _ hb]
  conv_lhs => rw [← List.ofFn_get ts, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  have hlist : directionalWord (fun b _ => e b) (ts.get k).2 =
      constantDirectionWord (List.ofFn (fun i => e ((ts.get k).2.get i))) := by
    rw [show List.ofFn (fun i => e ((ts.get k).2.get i)) = ((ts.get k).2).map e by
      change List.ofFn (e ∘ (ts.get k).2.get) = _
      rw [← List.map_ofFn,List.ofFn_get]]
    unfold constantDirectionWord
    funext u x
    rw [directional_map]
  change ((ts.get k).1 (archBase F)) • _ = _
  rw [hlist, constant_word_iterated O hO _ hf _ _ _ hb]
  rfl

open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart renaming word_reindex → word_reindex
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart renaming rightDerivative → rightDerivative
 def nativeIndex (F : Type) [Field F] [NumberField F] (b : KPSmoothActualFlowData.B F) : Fin (groupDimension F) :=
  (lieEnumeration F).symm ((actualBasisReindex F).symm b)

 theorem native_second_word
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : NumberField.InfinitePlace F) (i j : Fin 6)
    (u : KPGlobalResidualConstruction.G F ζ hζ → ℂ) (g : KPGlobalResidualConstruction.G F ζ hζ) :
    actualRightWord F ζ hζ [nativeIndex F (w,i), nativeIndex F (w,j)] u g =
      KPMsGreenFlux.rightDerivative F ζ hζ w i
        (KPMsGreenFlux.rightDerivative F ζ hζ w j u) g := by
  rw [word_reindex]
  simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,nativeIndex,
    Equiv.apply_symm_apply]
  rfl

open KPGlobalResidualConstruction

end DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir

end
