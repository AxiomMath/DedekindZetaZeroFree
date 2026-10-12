module

public import DedekindZetaZeroFree.Geometry.HyperbolicActionMetricAndVolume
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.ChartGreenIdentities

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPLocalizedFormGraph

namespace ChartEnergyGeometry
open HyperbolicChart Matrix
open scoped Matrix
 def arch (d : ℕ) (p : Space d) : KPArch.Space d :=
  fun i => (⟨p (i,0), p (i,1)⟩, p (i,2))
 def real (d : ℕ) (p : KPArch.Space d) : Space d :=
  WithLp.toLp 2 (fun ik => ![(p ik.1).1.re, (p ik.1).1.im, (p ik.1).2] ik.2)
 def archL (d : ℕ) : Space d →L[ℝ] KPArch.Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := arch d
    map_add' := by intro x y; ext i <;> simp [arch, Complex.add_re, Complex.add_im]; rfl
    map_smul' := by intro a x; ext i : 1; apply Prod.ext <;> simp [arch, Complex.real_smul]; apply Complex.ext <;> simp }
 def realL (d : ℕ) : KPArch.Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := real d
    map_add' := by
      intro x y; ext ⟨i,k⟩; fin_cases k <;> simp [real]
    map_smul' := by
      intro a x; ext ⟨i,k⟩; fin_cases k <;> simp [real, Complex.real_smul] }

private lemma arch_real' (d : ℕ) (x : KPArch.Space d) : arch d (real d x) = x := by
  ext i <;> simp [real, arch]
 def scaleL (d : ℕ) (w : Fin d × Fin 3 → ℝ) : Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun j => w j * x j)
    map_add' := by intro x y; ext j; simp [mul_add]
    map_smul' := by intro a x; ext j; simp; ring }
private lemma scaleL_apply (d : ℕ) (w : Fin d × Fin 3 → ℝ) (z : Space d) (j) :
    scaleL d w z j = w j * z j := rfl
 def frame (d : ℕ) (x : Space d) : Space d →L[ℝ] Space d :=
  scaleL d (fun j => if j.2 = 2 then 1 else Real.exp (x (j.1, 2)))
 def unframe (d : ℕ) (x : Space d) : Space d →L[ℝ] Space d :=
  scaleL d (fun j => if j.2 = 2 then 1 else (Real.exp (x (j.1, 2)))⁻¹)
private lemma frame_unframe (d : ℕ) (x z : Space d) : frame d x (unframe d x z) = z := by
  ext j
  simp only [frame, unframe, scaleL_apply]
  split_ifs <;> simp [Real.exp_ne_zero, ← mul_assoc]
private lemma metric_frame (d : ℕ) (x z : Space d) :
    KPArch.metric d (arch d x) (arch d (frame d x z)) = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  simp only [KPArch.metric, KPArch.height, arch, frame, scaleL_apply,
    Fin.sum_univ_three, Fin.reduceEq, ite_true, ite_false, one_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  field_simp
private lemma sum_norm_basis (d : ℕ) (L : Space d →L[ℝ] ℂ)
    (e : Space d ≃ₗᵢ[ℝ] Space d) :
    (∑ j, ‖L (e (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j))‖ ^ 2) =
    ∑ j, ‖L (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j)‖ ^ 2 := by
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hr := ((EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).map e).norm_dual
    (Complex.reCLM.comp L)
  have hi := ((EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).map e).norm_dual
    (Complex.imCLM.comp L)
  rw [(EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).norm_dual (Complex.reCLM.comp L)] at hr
  rw [(EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).norm_dual (Complex.imCLM.comp L)] at hi
  simpa only [OrthonormalBasis.map_apply, ContinuousLinearMap.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, pow_two] using congrArg₂ (· + ·) hr.symm hi.symm
private lemma metric_unframe (d : ℕ) (x z : Space d) :
    ‖unframe d x z‖ ^ 2 = KPArch.metric d (arch d x) (arch d z) := by
  rw [← metric_frame d x (unframe d x z), frame_unframe]
theorem transport_sum (d : ℕ) (x y : Space d) (J : Space d →L[ℝ] Space d)
    (hm : ∀ z, KPArch.metric d (arch d y) (arch d (J z)) =
      KPArch.metric d (arch d x) (arch d z)) (L : Space d →L[ℝ] ℂ) :
    (∑ j, ‖L (J (frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j)))‖ ^ 2) =
      ∑ j, ‖L (frame d y (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j))‖ ^ 2 := by
  let E : Space d →ₗᵢ[ℝ] Space d := {
    toLinearMap := ((unframe d y).comp (J.comp (frame d x))).toLinearMap
    norm_map' := by
      intro z
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖unframe d y (J (frame d x z))‖ ^ 2 = ‖z‖ ^ 2
      rw [metric_unframe, hm, metric_frame] }
  have hh := sum_norm_basis d (L.comp (frame d y)) (E.toLinearIsometryEquiv rfl)
  simpa only [LinearIsometry.toLinearIsometryEquiv_apply, ContinuousLinearMap.comp_apply,
    E, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, frame_unframe] using hh
private lemma frame_basis (d : ℕ) (x : Space d) (i : Fin d) (k : Fin 3) :
    frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ (i,k)) =
      (if k = 2 then 1 else Real.exp (x (i,2))) • coordinateVector d i k := by
  ext j
  simp only [frame, scaleL_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single_apply, coordinateVector, PiLp.smul_apply,
    WithLp.ofLp_toLp, smul_eq_mul]
  by_cases h : j = (i,k)
  · subst j; simp
  · simp [h, Ne.symm h]
theorem differential_sum (d : ℕ) (g : Space d → ℂ) (x : Space d) :
    (∑ i, ∑ k, ‖differential d g x i k‖ ^ 2) =
      ∑ j, ‖fderiv ℝ g x (frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j))‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.sum_univ_three, differential, frame_basis, Fin.reduceEq,
    ite_true, ite_false, one_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, coordinateDerivative, map_smul,
    Complex.real_smul, Complex.ofReal_one, one_mul]
  simp
  ring
 def realAction (d : ℕ) (a : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x : Space d) : Space d := real d (KPArch.productAction d a (arch d x))
private lemma realAction_deriv (d : ℕ) (a : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x : Space d) :
    HasFDerivAt (realAction d a)
      ((realL d).comp ((fderiv ℝ (KPArch.productAction d a) (arch d x)).comp (archL d))) x := by
  exact (realL d).hasFDerivAt.comp x
    (((KPArch.productAction_contDiff d a).differentiable (by simp) (arch d x)).hasFDerivAt.comp x
      (archL d).hasFDerivAt)
private lemma realAction_metric (d : ℕ) (a : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x z : Space d) :
    KPArch.metric d (arch d (realAction d a x)) (arch d (fderiv ℝ (realAction d a) x z)) =
      KPArch.metric d (arch d x) (arch d z) := by
  rw [(realAction_deriv d a x).fderiv]
  change KPArch.metric d (arch d (real d _)) (arch d (real d _)) = _
  rw [arch_real', arch_real']
  exact KPArch.metric_invariant d a (arch d x) (arch d z)
theorem differential_invariant (d : ℕ) (a : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (g : Space d → ℂ) (x : Space d) (c : ℂ)
    (hg : DifferentiableAt ℝ g x) (hy : DifferentiableAt ℝ g (realAction d a x))
    (heq : (g ∘ realAction d a) =ᶠ[nhds x] fun z => c * g z) (hc : ‖c‖ = 1) :
    (∑ i, ∑ k, ‖differential d g (realAction d a x) i k‖ ^ 2) =
      ∑ i, ∑ k, ‖differential d g x i k‖ ^ 2 := by
  have hd : (fderiv ℝ g (realAction d a x)).comp (fderiv ℝ (realAction d a) x) =
      c • fderiv ℝ g x := by
    rw [← fderiv_comp x hy (realAction_deriv d a x).differentiableAt]
    rw [Filter.EventuallyEq.fderiv_eq heq]
    exact (hg.hasFDerivAt.const_smul c).fderiv
  rw [differential_sum, differential_sum]
  rw [← transport_sum d x (realAction d a x) (fderiv ℝ (realAction d a) x)
    (realAction_metric d a x) (fderiv ℝ g (realAction d a x))]
  apply Finset.sum_congr rfl
  intro j hj
  have hh := congrArg (fun L : Space d →L[ℝ] ℂ => L
    (frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j))) hd
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, norm_mul, hc, one_mul] using congrArg (fun z : ℂ => ‖z‖ ^ 2) hh
theorem gram_inv_bound {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m n ℝ) (hB : Function.Injective B.mulVec) (L : m → ℝ) :
    let G := B.transpose * B
    let η := B.transpose *ᵥ L
    η ⬝ᵥ (G⁻¹ *ᵥ η) ≤ L ⬝ᵥ L := by
  dsimp
  have hp : (B.transpose * B).PosDef := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨by simpa using Matrix.isHermitian_conjTranspose_mul_self B, ?_⟩
    intro x hx
    have hBx : B *ᵥ x ≠ 0 := by
      intro hh
      exact hx (hB (by simpa using hh))
    have hn : 0 ≤ (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
      simpa using dotProduct_self_star_nonneg (B *ᵥ x)
    have hp : 0 < (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := lt_of_le_of_ne hn
      (Ne.symm (dotProduct_self_eq_zero.not.mpr hBx))
    simpa only [star_trivial, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose] using hp
  let q := (B.transpose * B)⁻¹ *ᵥ (B.transpose *ᵥ L)
  have hq : (B.transpose * B) *ᵥ q = B.transpose *ᵥ L := by
    dsimp [q]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit), one_mulVec]
  have he : (B.transpose *ᵥ L) ⬝ᵥ q = (B *ᵥ q) ⬝ᵥ (B *ᵥ q) := by
    rw [← hq, ← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec,
      vecMul_transpose]
  have hl : (B.transpose *ᵥ L) ⬝ᵥ q = L ⬝ᵥ (B *ᵥ q) := by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hn : 0 ≤ (L - B *ᵥ q) ⬝ᵥ (L - B *ᵥ q) := by
    simpa using dotProduct_self_star_nonneg (L - B *ᵥ q)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm (B *ᵥ q) L] at hn
  change (B.transpose *ᵥ L) ⬝ᵥ q ≤ _
  linarith

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
private theorem expand (L : EuclideanSpace ℝ m →L[ℝ] ℝ) (z : EuclideanSpace ℝ m) :
    L z = ∑ k, L (EuclideanSpace.basisFun m ℝ k) * z k := by
  conv_lhs => rw [← (EuclideanSpace.basisFun m ℝ).sum_repr z]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, smul_eq_mul]
  congr 1
  funext k
  ring
 theorem jacobian_bound (J : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m)
    (hJ : Function.Injective J) (L : EuclideanSpace ℝ m →L[ℝ] ℝ) :
    let B : Matrix m n ℝ := fun k r => J (EuclideanSpace.basisFun n ℝ r) k
    let η := fun r => L (J (EuclideanSpace.basisFun n ℝ r))
    η ⬝ᵥ ((B.transpose * B)⁻¹ *ᵥ η) ≤ ∑ k, (L (EuclideanSpace.basisFun m ℝ k)) ^ 2 := by
  dsimp
  let B : Matrix m n ℝ := fun k r => J (EuclideanSpace.basisFun n ℝ r) k
  have hB (z : n → ℝ) : B *ᵥ z = ⇑(J (WithLp.toLp 2 z)) := by
    ext k
    conv_rhs => rw [← (EuclideanSpace.basisFun n ℝ).sum_repr (WithLp.toLp 2 z)]
    simp [B, mulVec, dotProduct, map_sum, map_smul, mul_comm]
  have hinj : Function.Injective B.mulVec := by
    intro a b hab
    simp only [hB] at hab
    have hh := hJ (WithLp.ofLp_injective 2 hab)
    exact WithLp.toLp_injective 2 hh
  have he : (fun r => L (J (EuclideanSpace.basisFun n ℝ r))) =
      B.transpose *ᵥ (fun k => L (EuclideanSpace.basisFun m ℝ k)) := by
    ext r
    rw [expand L]
    simp only [mulVec, dotProduct, transpose_apply, B]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  rw [he]
  simpa only [dotProduct, sq, B] using gram_inv_bound B hinj
    (fun k => L (EuclideanSpace.basisFun m ℝ k))

 theorem pullback_metric (d n : ℕ) (y : Space d)
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] KPArch.Space d) :
    let T := (unframe d y).comp ((realL d).comp J)
    let B : Matrix (Fin d × Fin 3) (Fin n) ℝ :=
      fun k r => T (EuclideanSpace.basisFun (Fin n) ℝ r) k
    (fun j k => (KPArch.metric d (arch d y) (J (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)) -
      KPArch.metric d (arch d y) (J (EuclideanSpace.single j 1)) -
      KPArch.metric d (arch d y) (J (EuclideanSpace.single k 1))) / 2) = B.transpose * B := by
  dsimp
  ext j k
  have hm (z : KPArch.Space d) : KPArch.metric d (arch d y) z =
      ‖unframe d y (real d z)‖ ^ 2 := by
    rw [metric_unframe, arch_real']
  simp only [hm]
  change (‖(unframe d y) ((realL d) (J (_ + _)))‖ ^ 2 -
    ‖(unframe d y) ((realL d) (J _))‖ ^ 2 -
    ‖(unframe d y) ((realL d) (J _))‖ ^ 2) / 2 = _
  simp only [map_add]
  rw [norm_add_sq_real]
  simp only [mul_apply, transpose_apply, ContinuousLinearMap.comp_apply,
    EuclideanSpace.basisFun_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  change (_ + 2 * (∑ z : Fin d × Fin 3,
    ((unframe d y) ((realL d) (J (EuclideanSpace.single k 1)))) z *
    ((unframe d y) ((realL d) (J (EuclideanSpace.single j 1)))) z) + _ - _ - _) / 2 =
    ∑ z : Fin d × Fin 3,
    ((unframe d y) ((realL d) (J (EuclideanSpace.single j 1)))) z *
    ((unframe d y) ((realL d) (J (EuclideanSpace.single k 1)))) z
  rw [show (∑ z, ((unframe d y) ((realL d) (J (EuclideanSpace.single k 1)))) z *
    ((unframe d y) ((realL d) (J (EuclideanSpace.single j 1)))) z) =
    ∑ z, ((unframe d y) ((realL d) (J (EuclideanSpace.single j 1)))) z *
    ((unframe d y) ((realL d) (J (EuclideanSpace.single k 1)))) z by
      apply Finset.sum_congr rfl; intro z hz; ring]
  ring

end ChartEnergyGeometry

end DedekindZetaZeroFree.KPLocalizedFormGraph

end
