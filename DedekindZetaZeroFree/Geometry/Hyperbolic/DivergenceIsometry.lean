module

public import DedekindZetaZeroFree.Geometry.Hyperbolic.Cotangent.LogarithmicCoframe

@[expose] public section

noncomputable section
open scoped ContDiff BigOperators
open Filter Topology

namespace DedekindZetaZeroFree.HyperbolicChart

private theorem metric_derivative_injective (d : ℕ) (ψ : Space d → Space d) (x : Space d)
    (hm : ∀ u v : Space d, metric d (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = metric d x u v) :
    Function.Injective (fderiv ℝ ψ x) := by
  intro u v huv
  have hw := hm (u-v) (u-v)
  have hz : fderiv ℝ ψ x (u-v) = 0 := by rw [map_sub, huv, sub_self]
  rw [hz, ← CotangentLogCoframe.inner_C, ← CotangentLogCoframe.inner_C] at hw
  have he : CotangentLogCoframe.C d x (u-v) = 0 := by simpa only [map_zero, inner_zero_left, inner_self_eq_zero] using hw.symm
  have he' : u-v = 0 := (CotangentLogCoframe.C d x).injective (he.trans (map_zero _).symm)
  exact sub_eq_zero.mp he'
private theorem derivative_equiv (d : ℕ) (ψ : Space d → Space d) (x : Space d)
    (hm : ∀ u v : Space d, metric d (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = metric d x u v) :
    ∃ J : Space d ≃L[ℝ] Space d, J.toContinuousLinearMap = fderiv ℝ ψ x := by
  have hi := metric_derivative_injective d ψ x hm
  have hs : Function.Surjective (fderiv ℝ ψ x) := LinearMap.injective_iff_surjective.mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (fderiv ℝ ψ x) (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩
private theorem coordinate_trace (d : ℕ) (A : Space d → Space d) (x : Space d)
    (hA : DifferentiableAt ℝ A x) :
    (∑ i : Fin d, ∑ k : Fin 3,
      fderiv ℝ (fun y => A y (i,k)) x (coordinateVector d i k)) =
      LinearMap.trace ℝ (Space d) (fderiv ℝ A x).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr,
    EuclideanSpace.basisFun_repr, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have hp := ((EuclideanSpace.proj (𝕜 := ℝ) (i,k)).hasFDerivAt (x := A x)).comp x hA.hasFDerivAt
  rw [show (fun y => A y (i,k)) = (EuclideanSpace.proj (𝕜 := ℝ) (i,k)) ∘ A from rfl,
    hp.fderiv]
  apply congrArg (fun u : Space d => fderiv ℝ A x u (i,k))
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  ext j
  simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply, eq_comm]
private theorem trace_pushforward (d : ℕ) (ψ A B : Space d → Space d) (x : Space d)
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B (ψ x))
    (J : Space d ≃L[ℝ] Space d) (hJ : J.toContinuousLinearMap = fderiv ℝ ψ x)
    (hpush : (B ∘ ψ) =ᶠ[𝓝 x] fun y => fderiv ℝ ψ y (A y)) :
    LinearMap.trace ℝ (Space d) (fderiv ℝ B (ψ x)).toLinearMap =
      LinearMap.trace ℝ (Space d) (fderiv ℝ A x).toLinearMap +
      LinearMap.trace ℝ (Space d)
        (J.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ ψ) x (A x))).toLinearMap := by
  have hψd : DifferentiableAt ℝ ψ x := hψ.differentiableAt (by norm_num)
  have hψ2 : DifferentiableAt ℝ (fderiv ℝ ψ) x := (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf := hψ2.hasFDerivAt.clm_apply hA.hasFDerivAt
  have he : (fderiv ℝ B (ψ x)).comp (fderiv ℝ ψ x) =
      (fderiv ℝ ψ x).comp (fderiv ℝ A x) +
        (fderiv ℝ (fderiv ℝ ψ) x).flip (A x) := by
    rw [← fderiv_comp x hB hψd, hpush.fderiv_eq, hf.fderiv]
  have hs (u : Space d) : fderiv ℝ (fderiv ℝ ψ) x u (A x) =
      fderiv ℝ (fderiv ℝ ψ) x (A x) u :=
    (hψ.isSymmSndFDerivAt (by norm_num)).eq u (A x)
  have he' : (fderiv ℝ B (ψ x)).comp J.toContinuousLinearMap =
      J.toContinuousLinearMap.comp (fderiv ℝ A x) + fderiv ℝ (fderiv ℝ ψ) x (A x) := by
    rw [hJ, he]
    congr 1
    apply ContinuousLinearMap.ext
    intro u
    exact hs u
  have hc : fderiv ℝ B (ψ x) =
      (J.toContinuousLinearMap.comp (fderiv ℝ A x)).comp J.symm.toContinuousLinearMap +
      (fderiv ℝ (fderiv ℝ ψ) x (A x)).comp J.symm.toContinuousLinearMap := by
    have hec := congrArg (fun M : Space d →L[ℝ] Space d => M.comp J.symm.toContinuousLinearMap) he'
    simpa [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc,
      ContinuousLinearEquiv.comp_coe] using hec
  rw [hc, ContinuousLinearMap.toLinearMap_add, map_add]
  have hconj : LinearMap.trace ℝ (Space d)
      ((J.toContinuousLinearMap.comp (fderiv ℝ A x)).comp J.symm.toContinuousLinearMap).toLinearMap =
        LinearMap.trace ℝ (Space d) (fderiv ℝ A x).toLinearMap := by
    simp only [ContinuousLinearMap.toLinearMap_comp]
    rw [LinearMap.trace_comp_comm']
    simp
  rw [hconj]
  congr 1
  exact LinearMap.trace_comp_comm' _ _

private theorem metric_fderiv (d : ℕ) (p u v a : Space d) :
    fderiv ℝ (fun y => metric d y u v) p a =
      ∑ i : Fin d, -2 * a (i,2) * Real.exp (-2 * p (i,2)) *
        (u (i,0) * v (i,0) + u (i,1) * v (i,1)) := by
  have hf (i : Fin d) : HasFDerivAt (fun y : Space d =>
      u (i,2) * v (i,2) + Real.exp (-2 * y (i,2)) *
        (u (i,0) * v (i,0) + u (i,1) * v (i,1)))
      ((Real.exp (-2 * p (i,2)) * (-2) * (u (i,0) * v (i,0) + u (i,1) * v (i,1))) •
        (EuclideanSpace.proj (𝕜 := ℝ) (i,2))) p := by
    convert (((EuclideanSpace.proj (𝕜 := ℝ) (i,2)).hasFDerivAt (x := p)).const_mul (-2)).exp.mul_const
      (u (i,0) * v (i,0) + u (i,1) * v (i,1)) |>.const_add (u (i,2) * v (i,2)) using 1 <;>
      simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]

  have hs := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hf i)
  have hs' : HasFDerivAt (fun y : Space d => metric d y u v)
      (∑ i : Fin d, (Real.exp (-2 * p (i,2)) * (-2) * (u (i,0) * v (i,0) + u (i,1) * v (i,1))) •
        (EuclideanSpace.proj (𝕜 := ℝ) (i,2))) p := by
    convert hs using 1
    funext y
    simp only [Finset.sum_apply, metric]
  rw [hs'.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.exp (-2 * p (i,2)) * (-2) * (u (i,0) * v (i,0) + u (i,1) * v (i,1))) * a (i,2) = _
  ring

private theorem metric_variable_derivative (d : ℕ) (z u v : Space d → Space d) (x a : Space d)
    (hz : DifferentiableAt ℝ z x) (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    fderiv ℝ (fun y => metric d (z y) (u y) (v y)) x a =
      fderiv ℝ (fun y => metric d y (u x) (v x)) (z x) (fderiv ℝ z x a) +
      metric d (z x) (fderiv ℝ u x a) (v x) + metric d (z x) (u x) (fderiv ℝ v x a) := by
  have hc (f : Space d → Space d) (hf : DifferentiableAt ℝ f x) (k : Fin d × Fin 3) :
      DifferentiableAt ℝ (fun y => f y k) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).differentiableAt.comp x hf
  have hd (f : Space d → Space d) (hf : DifferentiableAt ℝ f x) (k : Fin d × Fin 3) :
      fderiv ℝ (fun y => f y k) x a = fderiv ℝ f x a k := by
    rw [show (fun y => f y k) = (EuclideanSpace.proj (𝕜 := ℝ) k) ∘ f from rfl,
      fderiv_comp x (EuclideanSpace.proj (𝕜 := ℝ) k).differentiableAt hf,
      ContinuousLinearMap.fderiv]
    rfl
  have he (i : Fin d) : DifferentiableAt ℝ (fun y => Real.exp (-2 * z y (i,2))) x :=
    ((hc z hz (i,2)).const_mul (-2)).exp
  have hed (i : Fin d) : fderiv ℝ (fun y => Real.exp (-2 * z y (i,2))) x a =
      Real.exp (-2 * z x (i,2)) * (-2 * fderiv ℝ z x a (i,2)) := by
    rw [fderiv_exp ((hc z hz (i,2)).const_mul (-2)), fderiv_const_mul (hc z hz (i,2)) (-2)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hd z hz]
  have hf (i : Fin d) : DifferentiableAt ℝ (fun y : Space d =>
      u y (i,2) * v y (i,2) + Real.exp (-2 * z y (i,2)) *
        (u y (i,0) * v y (i,0) + u y (i,1) * v y (i,1))) x :=
    ((hc u hu (i,2)).mul (hc v hv (i,2))).add
      ((he i).mul (((hc u hu (i,0)).mul (hc v hv (i,0))).add ((hc u hu (i,1)).mul (hc v hv (i,1)))))
  rw [metric_fderiv]
  unfold metric
  rw [show (fun y => ∑ i : Fin d, (u y (i,2) * v y (i,2) + Real.exp (-2 * z y (i,2)) *
      (u y (i,0) * v y (i,0) + u y (i,1) * v y (i,1)))) =
      ∑ i : Fin d, fun y => u y (i,2) * v y (i,2) + Real.exp (-2 * z y (i,2)) *
      (u y (i,0) * v y (i,0) + u y (i,1) * v y (i,1)) from by funext y; simp only [Finset.sum_apply]]
  rw [fderiv_sum (fun i _ => hf i)]
  simp only [ContinuousLinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hvd (f : Space d → Space d) (hf : DifferentiableAt ℝ f x) (k : Fin d × Fin 3) :
      HasFDerivAt (fun y => f y k) ((EuclideanSpace.proj (𝕜 := ℝ) k).comp (fderiv ℝ f x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x hf.hasFDerivAt
  have hder := ((hvd u hu (i,2)).mul (hvd v hv (i,2))).add
    (((((hvd z hz (i,2)).const_mul (-2)).exp)).mul
      (((hvd u hu (i,0)).mul (hvd v hv (i,0))).add ((hvd u hu (i,1)).mul (hvd v hv (i,1)))))
  dsimp only [Pi.add_def, Pi.mul_def] at hder
  rw [hder.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply]
  simp only [EuclideanSpace.proj, PiLp.proj_apply, WithLp.ofLp_toLp]
  ring

private theorem differentiated_metric (d : ℕ) (ψ : Space d → Space d) (x a u v : Space d)
    (hψ : ContDiffAt ℝ 2 ψ x)
    (hm : ∀ᶠ y in nhds x, ∀ u v : Space d,
      metric d (ψ y) (fderiv ℝ ψ y u) (fderiv ℝ ψ y v) = metric d y u v) :
    (∑ i : Fin d, -2 * (fderiv ℝ ψ x a) (i,2) * Real.exp (-2 * ψ x (i,2)) *
        ((fderiv ℝ ψ x u) (i,0) * (fderiv ℝ ψ x v) (i,0) +
          (fderiv ℝ ψ x u) (i,1) * (fderiv ℝ ψ x v) (i,1))) +
      metric d (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a u) (fderiv ℝ ψ x v) +
      metric d (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ (fderiv ℝ ψ) x a v) =
    ∑ i : Fin d, -2 * a (i,2) * Real.exp (-2 * x (i,2)) *
      (u (i,0) * v (i,0) + u (i,1) * v (i,1)) := by
  have hψd := hψ.differentiableAt (by norm_num)
  have hψ2 := (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y u) x := hψ2.clm_apply (differentiableAt_const _)
  have hv : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y v) x := hψ2.clm_apply (differentiableAt_const _)
  have hdu : fderiv ℝ (fun y => fderiv ℝ ψ y u) x a = fderiv ℝ (fderiv ℝ ψ) x a u := by
    rw [(hψ2.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).fderiv]
    simp
  have hdv : fderiv ℝ (fun y => fderiv ℝ ψ y v) x a = fderiv ℝ (fderiv ℝ ψ) x a v := by
    rw [(hψ2.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
    simp
  have hg : (fun y => metric d (ψ y) (fderiv ℝ ψ y u) (fderiv ℝ ψ y v)) =ᶠ[nhds x]
      fun y => metric d y u v := hm.mono (fun y hy => hy u v)
  have he := congrArg (fun D : Space d →L[ℝ] ℝ => D a) (hg.fderiv_eq (𝕜 := ℝ))
  rw [metric_variable_derivative d ψ (fun y => fderiv ℝ ψ y u) (fun y => fderiv ℝ ψ y v)
    x a hψd hu hv, metric_fderiv, metric_fderiv, hdu, hdv] at he
  exact he

private theorem basis_coord_square (d : ℕ) (q : Space d ≃ₗᵢ[ℝ] Space d) (j : Fin d × Fin 3) :
    (∑ k : Fin d × Fin 3, (q (EuclideanSpace.basisFun _ ℝ k) j)^2) = 1 := by
  let b := (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).map q
  have h := b.sum_sq_inner_right (EuclideanSpace.single j 1)
  have hi (k : Fin d × Fin 3) : inner ℝ (b k) (EuclideanSpace.single j 1) = q (EuclideanSpace.basisFun _ ℝ k) j := by
    simp [b, EuclideanSpace.inner_single_right]
  simpa only [hi, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_one, one_pow] using h
private theorem sum_metric_variation (d : ℕ) (p a : Space d) (q : Space d ≃ₗᵢ[ℝ] Space d) :
    (∑ k : Fin d × Fin 3, ∑ i : Fin d, -2 * a (i,2) * Real.exp (-2 * p (i,2)) *
      ((CotangentLogCoframe.H d p (q (EuclideanSpace.basisFun _ ℝ k))) (i,0)^2 +
        (CotangentLogCoframe.H d p (q (EuclideanSpace.basisFun _ ℝ k))) (i,1)^2)) =
      -4 * ∑ i : Fin d, a (i,2) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [(CotangentLogCoframe.H_apply d p _ i).1, (CotangentLogCoframe.H_apply d p _ i).2.1, mul_pow,
    Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [basis_coord_square d q (i,1), basis_coord_square d q (i,2)]
  have he : Real.exp (-2 * p (i,2)) * Real.exp (p (i,2)) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  calc _ = -4 * a (i,2) * (Real.exp (-2 * p (i,2)) * Real.exp (p (i,2)) ^ 2) := by ring
       _ = _ := by rw [he, mul_one]
private theorem sum_metric_trace (d : ℕ) (p : Space d) (L : Space d →L[ℝ] Space d)
    (q : Space d ≃ₗᵢ[ℝ] Space d) :
    (∑ k : Fin d × Fin 3, metric d p
      (L (CotangentLogCoframe.H d p (q (EuclideanSpace.basisFun _ ℝ k))))
      (CotangentLogCoframe.H d p (q (EuclideanSpace.basisFun _ ℝ k)))) =
        LinearMap.trace ℝ (Space d) L.toLinearMap := by
  let e := q.toContinuousLinearEquiv.trans (CotangentLogCoframe.H d p)
  let N := e.symm.toContinuousLinearMap.comp (L.comp e.toContinuousLinearMap)
  have ht : LinearMap.trace ℝ (Space d) N.toLinearMap = LinearMap.trace ℝ (Space d) L.toLinearMap := by
    dsimp only [N]
    simp only [ContinuousLinearMap.toLinearMap_comp]
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    simp
  rw [← ht, LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr,
    EuclideanSpace.basisFun_repr]
  apply Finset.sum_congr rfl
  intro k _
  rw [← CotangentLogCoframe.inner_C]
  simp only [CotangentLogCoframe.H, ContinuousLinearEquiv.apply_symm_apply]
  have he : (N (EuclideanSpace.basisFun _ ℝ k)) k =
      inner ℝ (q (EuclideanSpace.basisFun _ ℝ k))
        (CotangentLogCoframe.C d p (L (CotangentLogCoframe.H d p (q (EuclideanSpace.basisFun _ ℝ k))))) := by
    rw [← EuclideanSpace.basisFun_repr, OrthonormalBasis.repr_apply_apply]
    dsimp [N, e]
    rw [← q.inner_map_map]
    simp [CotangentLogCoframe.H]
  change inner ℝ _ _ = N (EuclideanSpace.basisFun _ ℝ k) k
  rw [he, real_inner_comm]
  rfl

set_option maxHeartbeats 1000000 in
private theorem metric_hessian_trace (d : ℕ) (ψ : Space d → Space d) (x a : Space d)
    (hψ : ContDiffAt ℝ 2 ψ x)
    (hm : ∀ᶠ y in nhds x, ∀ u v : Space d,
      metric d (ψ y) (fderiv ℝ ψ y u) (fderiv ℝ ψ y v) = metric d y u v)
    (J : Space d ≃L[ℝ] Space d) (hJ : J.toContinuousLinearMap = fderiv ℝ ψ x) :
    LinearMap.trace ℝ (Space d) (J.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ ψ) x a)).toLinearMap =
      2 * (∑ i : Fin d, fderiv ℝ ψ x a (i,2)) - 2 * ∑ i : Fin d, a (i,2) := by
  let Q : Space d →L[ℝ] Space d := (CotangentLogCoframe.C d (ψ x)).toContinuousLinearMap.comp
    (J.toContinuousLinearMap.comp (CotangentLogCoframe.H d x).toContinuousLinearMap)
  have hqi (u v : Space d) : inner ℝ (Q u) (Q v) = inner ℝ u v := by
    change inner ℝ (CotangentLogCoframe.C d (ψ x) (J (CotangentLogCoframe.H d x u)))
      (CotangentLogCoframe.C d (ψ x) (J (CotangentLogCoframe.H d x v))) = _
    rw [CotangentLogCoframe.inner_C]
    change metric d (ψ x) (J.toContinuousLinearMap (CotangentLogCoframe.H d x u))
      (J.toContinuousLinearMap (CotangentLogCoframe.H d x v)) = _
    rw [hJ, (hm.self_of_nhds) _ _, ← CotangentLogCoframe.inner_C]
    simp [CotangentLogCoframe.H]
  let q : Space d ≃ₗᵢ[ℝ] Space d := LinearIsometryEquiv.ofSurjective
    { toLinearMap := Q.toLinearMap
      norm_map' := (LinearMap.norm_map_iff_inner_map_map Q).2 hqi }
    (by
      apply LinearMap.surjective_of_injective
      intro u v huv
      change Q u = Q v at huv
      have h := hqi (u-v) (u-v)
      rw [map_sub, huv, sub_self, inner_zero_left] at h
      exact sub_eq_zero.mp (inner_self_eq_zero.mp h.symm))
  have hq (u : Space d) : q u = Q u := rfl
  let basis := EuclideanSpace.basisFun (Fin d × Fin 3) ℝ
  let E := fun k => CotangentLogCoframe.H d x (basis k)
  let L := J.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ ψ) x a)
  have he (k : Fin d × Fin 3) : fderiv ℝ ψ x (E k) = CotangentLogCoframe.H d (ψ x) (q (basis k)) := by
    rw [hq]
    simp [Q, E, CotangentLogCoframe.H, hJ]
  have hL (k : Fin d × Fin 3) : fderiv ℝ (fderiv ℝ ψ) x a (E k) = fderiv ℝ ψ x (L (E k)) := by
    dsimp only [L, ContinuousLinearMap.comp_apply]
    rw [← hJ]
    simp
  have hterm (k : Fin d × Fin 3) :
      (∑ i : Fin d, -2 * (fderiv ℝ ψ x a) (i,2) * Real.exp (-2 * ψ x (i,2)) *
        ((CotangentLogCoframe.H d (ψ x) (q (basis k))) (i,0)^2 +
          (CotangentLogCoframe.H d (ψ x) (q (basis k))) (i,1)^2)) +
        2 * metric d x (L (E k)) (E k) =
      ∑ i : Fin d, -2 * a (i,2) * Real.exp (-2 * x (i,2)) * ((E k) (i,0)^2 + (E k) (i,1)^2) := by
    have ht := differentiated_metric d ψ x a (E k) (E k) hψ hm
    rw [hL, he] at ht
    have he' := he k
    rw [← he'] at ht
    rw [(hm.self_of_nhds) _ _, (hm.self_of_nhds) _ _] at ht
    have hcomm : metric d x (E k) (L (E k)) = metric d x (L (E k)) (E k) := by
      rw [← CotangentLogCoframe.inner_C, ← CotangentLogCoframe.inner_C, real_inner_comm]
    rw [hcomm] at ht
    rw [he] at ht
    have hsum : ∀ r m : ℝ, r + m + m = r + 2 * m := by intros; ring
    simpa only [pow_two, hsum] using ht
  have hs := congrArg (fun f : (Fin d × Fin 3) → ℝ => ∑ k, f k) (funext hterm)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [sum_metric_variation] at hs
  have htrace : (∑ k : Fin d × Fin 3, metric d x (L (E k)) (E k)) =
      LinearMap.trace ℝ (Space d) L.toLinearMap :=
    sum_metric_trace d x L (LinearIsometryEquiv.refl ℝ (Space d))
  rw [htrace] at hs
  have hsource : (∑ k : Fin d × Fin 3, ∑ i : Fin d,
      -2 * a (i,2) * Real.exp (-2 * x (i,2)) * ((E k) (i,0)^2 + (E k) (i,1)^2)) =
      -4 * ∑ i : Fin d, a (i,2) := by
    exact sum_metric_variation d x a (LinearIsometryEquiv.refl ℝ (Space d))
  rw [hsource] at hs
  dsimp only [L] at hs
  linarith

theorem real_divergence_isometry (d : ℕ) (ψ A B : Space d → Space d) (x : Space d)
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 1 A x) (hB : ContDiffAt ℝ 1 B (ψ x))
    (hmetric : ∀ᶠ y in nhds x, ∀ u v : Space d,
      metric d (ψ y) (fderiv ℝ ψ y u) (fderiv ℝ ψ y v) = metric d y u v)
    (hpush : (B ∘ ψ) =ᶠ[nhds x] (fun y => fderiv ℝ ψ y (A y))) :
    (∑ i : Fin d, (-(fderiv ℝ (fun y : Space d => B y (i, 2)) (ψ x) (coordinateVector d i 2)) +
      2 * B (ψ x) (i, 2) - fderiv ℝ (fun y : Space d => B y (i, 0)) (ψ x) (coordinateVector d i 0) -
      fderiv ℝ (fun y : Space d => B y (i, 1)) (ψ x) (coordinateVector d i 1))) =
    ∑ i : Fin d, (-(fderiv ℝ (fun y : Space d => A y (i, 2)) x (coordinateVector d i 2)) +
      2 * A x (i, 2) - fderiv ℝ (fun y : Space d => A y (i, 0)) x (coordinateVector d i 0) -
      fderiv ℝ (fun y : Space d => A y (i, 1)) x (coordinateVector d i 1)) := by
  have hAd := hA.differentiableAt (by norm_num)
  have hBd := hB.differentiableAt (by norm_num)
  obtain ⟨J,hJ⟩ := derivative_equiv d ψ x hmetric.self_of_nhds
  have ht := trace_pushforward d ψ A B x hψ hAd hBd J hJ hpush
  rw [metric_hessian_trace d ψ x (A x) hψ hmetric J hJ] at ht
  have hp : B (ψ x) = fderiv ℝ ψ x (A x) := hpush.self_of_nhds
  rw [← hp] at ht
  have hdiv (f : Space d → Space d) (p : Space d) (hf : DifferentiableAt ℝ f p) :
      (∑ i : Fin d, (-(fderiv ℝ (fun y : Space d => f y (i,2)) p (coordinateVector d i 2)) +
        2 * f p (i,2) - fderiv ℝ (fun y : Space d => f y (i,0)) p (coordinateVector d i 0) -
        fderiv ℝ (fun y : Space d => f y (i,1)) p (coordinateVector d i 1))) =
      -LinearMap.trace ℝ (Space d) (fderiv ℝ f p).toLinearMap + 2 * ∑ i : Fin d, f p (i,2) := by
    rw [← coordinate_trace d f p hf, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_three]
    ring
  rw [hdiv B (ψ x) hBd, hdiv A x hAd]
  linarith

end DedekindZetaZeroFree.HyperbolicChart

end
