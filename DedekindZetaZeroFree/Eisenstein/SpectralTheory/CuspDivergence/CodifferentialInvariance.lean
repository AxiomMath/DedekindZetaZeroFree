module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSections.ChartEllipticity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.CutoffScalarFlux

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem smooth_arch (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem smooth_mean (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

theorem codifferential_star_mul (d : ℕ) (f : Space d → ℂ)
    (W : Space d → Cotangent d) (x : Space d)
    (hf : DifferentiableAt ℝ f x)
    (hW : ∀ i k, DifferentiableAt ℝ (fun q => W q i k) x) :
    codifferential d (fun q i k => star (f q) * W q i k) x =
      star (f x) * codifferential d W x - pairing d (differential d f x) (W x) := by
  have hm (i : Fin d) (j k : Fin 3) :
      coordinateDerivative d i j (fun q => star (f q) * W q i k) x =
        star (coordinateDerivative d i j f x) * W x i k +
          star (f x) * coordinateDerivative d i j (fun q => W q i k) x := by
    simpa [coordinateDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Pi.mul_def, mul_comm, mul_left_comm, add_comm] using
      congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i j))
        ((hf.hasFDerivAt.star).mul (hW i k).hasFDerivAt).fderiv
  simp only [codifferential, pairing, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hm, differential, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_def, Fin.succ_zero_eq_one, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

private theorem derivative_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

private theorem exp_mul_derivative (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : DifferentiableAt ℝ g x) (i : Fin d) (k : Fin 3) (hk : k ≠ 2) :
    coordinateDerivative d i k (fun q => (Real.exp (q (i,2)) : ℂ) * g q) x =
      (Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i k g x := by
  have he := Complex.ofRealCLM.hasFDerivAt.comp x
    ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).hasFDerivAt.exp)
  have hh := congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k))
    (he.mul hg.hasFDerivAt).fderiv
  simpa [coordinateDerivative, coordinateVector, hk, Ne.symm hk, Pi.mul_def] using hh

theorem codifferential_differential_at (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    codifferential d (differential d g) x = laplacian d g x := by
  unfold codifferential laplacian
  apply Finset.sum_congr rfl
  intro i hi
  simp only [differential, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_def,
    Fin.succ_zero_eq_one]
  rw [exp_mul_derivative d _ x ((derivative_smoothAt d g x hg i 0).differentiableAt (by simp)) i 0 (by decide),
      exp_mul_derivative d _ x ((derivative_smoothAt d g x hg i 1).differentiableAt (by simp)) i 1 (by decide)]
  rw [show (Real.exp (2 * x (i, 2)) : ℂ) =
      (Real.exp (x (i, 2)) : ℂ) * (Real.exp (x (i, 2)) : ℂ) by
    rw [two_mul, Real.exp_add, Complex.ofReal_mul]]
  ring

private theorem differential_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => differential d g q i k) x := by
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (q (i,2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt.exp)
  fin_cases k
  · simpa [differential] using derivative_smoothAt d g x hg i 2
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 0)
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 1)

open HyperbolicChart
 def second (d : ℕ) (h : Space d → ℂ) (x v w : Space d) : ℂ :=
  fderiv ℝ (fderiv ℝ h) x v w
private theorem cd_second (d : ℕ) (h : Space d → ℂ) (x : Space d)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) h x) (i : Fin d) (k : Fin 3) :
    coordinateDerivative d i k (coordinateDerivative d i k h) x =
      second d h x (coordinateVector d i k) (coordinateVector d i k) := by
  unfold coordinateDerivative second
  simpa using congrArg (fun L : Space d →L[ℝ] ℂ => L (coordinateVector d i k))
    (((hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (coordinateVector d i k) x)).fderiv
private theorem affine_first (d : ℕ) (L : Space d →L[ℝ] Space d) (b : Space d)
    (h : Space d → ℂ) (x : Space d) (v : Space d)
    (hh : DifferentiableAt ℝ h (L x + b)) :
    fderiv ℝ (fun y => h (L y + b)) x v = fderiv ℝ h (L x + b) (L v) := by
  simpa [Function.comp_def] using congrArg (fun A : Space d →L[ℝ] ℂ => A v)
    (hh.hasFDerivAt.comp x (L.hasFDerivAt.add_const b)).fderiv
private theorem affine_second (d : ℕ) (L : Space d →L[ℝ] Space d) (b : Space d)
    (h : Space d → ℂ) (x : Space d) (i : Fin d) (k : Fin 3)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) h (L x + b)) :
    coordinateDerivative d i k (coordinateDerivative d i k (fun y => h (L y + b))) x =
      second d h (L x + b) (L (coordinateVector d i k)) (L (coordinateVector d i k)) := by
  have hs : ∀ᶠ y in nhds x, DifferentiableAt ℝ h (L y + b) := by
    have ht := ((hh.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)).mono
      (fun y hy => hy.differentiableAt (by simp))
    exact (L.continuous.add continuous_const).continuousAt.eventually ht
  have he : coordinateDerivative d i k (fun y => h (L y + b)) =ᶠ[nhds x]
      (fun y => fderiv ℝ h (L y + b) (L (coordinateVector d i k))) :=
    hs.mono fun y hy => affine_first d L b h y _ hy
  change fderiv ℝ (coordinateDerivative d i k (fun y => h (L y + b))) x _ = _
  rw [he.fderiv_eq]
  have hd := ((hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hcomp := (hd.comp x (L.hasFDerivAt.add_const b)).clm_apply
    (hasFDerivAt_const (c := L (coordinateVector d i k)) x)
  simpa [second] using congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k))
    hcomp.fderiv
 def lin (d : ℕ) (u : Fin d → ℂ) : Space d →L[ℝ] Space d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d × Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j =>
      ![(u j.1).re • EuclideanSpace.proj (j.1, (0 : Fin 3)) -
          (u j.1).im • EuclideanSpace.proj (j.1, (1 : Fin 3)),
        (u j.1).im • EuclideanSpace.proj (j.1, (0 : Fin 3)) +
          (u j.1).re • EuclideanSpace.proj (j.1, (1 : Fin 3)),
        EuclideanSpace.proj (j.1, (2 : Fin 3))] j.2))
private theorem lin_apply (d : ℕ) (u : Fin d → ℂ) (x : Space d) (i : Fin d) (k : Fin 3) :
    lin d u x (i,k) =
      ![(u i).re * x (i,0) - (u i).im * x (i,1),
        (u i).im * x (i,0) + (u i).re * x (i,1), x (i,2)] k := by
  fin_cases k <;> rfl
private theorem lin_zero (d : ℕ) (u : Fin d → ℂ) (i : Fin d) :
    lin d u (coordinateVector d i 0) =
      (u i).re • coordinateVector d i 0 + (u i).im • coordinateVector d i 1 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [lin_apply, coordinateVector]
  all_goals split_ifs <;> simp_all
private theorem lin_one (d : ℕ) (u : Fin d → ℂ) (i : Fin d) :
    lin d u (coordinateVector d i 1) =
      -(u i).im • coordinateVector d i 0 + (u i).re • coordinateVector d i 1 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [lin_apply, coordinateVector]
  all_goals split_ifs <;> simp_all
private theorem lin_two (d : ℕ) (u : Fin d → ℂ) (i : Fin d) :
    lin d u (coordinateVector d i 2) = coordinateVector d i 2 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [lin_apply, coordinateVector]
private theorem second_horizontal (d : ℕ) (u : Fin d → ℂ) (h : Space d → ℂ)
    (x : Space d) (i : Fin d) :
    second d h x (lin d u (coordinateVector d i 0)) (lin d u (coordinateVector d i 0)) +
      second d h x (lin d u (coordinateVector d i 1)) (lin d u (coordinateVector d i 1)) =
      (‖u i‖ ^ 2 : ℝ) •
        (second d h x (coordinateVector d i 0) (coordinateVector d i 0) +
         second d h x (coordinateVector d i 1) (coordinateVector d i 1)) := by
  rw [lin_zero, lin_one]
  simp only [second, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_add, smul_smul, Complex.real_smul]
  rw [Complex.sq_norm, Complex.normSq_apply]
  push_cast
  ring
private theorem affine_laplacian (d : ℕ) (u : Fin d → ℂ) (b : Space d)
    (hb : ∀ i, b (i,2) = Real.log ‖u i‖) (hu : ∀ i, u i ≠ 0)
    (h : Space d → ℂ) (x : Space d)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) h (lin d u x + b)) :
    laplacian d (fun y => h (lin d u y + b)) x = laplacian d h (lin d u x + b) := by
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i hi
  rw [affine_second d _ _ _ _ _ _ hh, affine_second d _ _ _ _ _ _ hh,
    affine_second d _ _ _ _ _ _ hh]
  have hfirst := affine_first d (lin d u) b h x (coordinateVector d i 2)
    (hh.differentiableAt (by simp))
  change _ = _ at hfirst
  rw [show coordinateDerivative d i 2 (fun y => h (lin d u y + b)) x =
    coordinateDerivative d i 2 h (lin d u x + b) by
      simpa only [coordinateDerivative, lin_two] using hfirst]
  rw [lin_two, second_horizontal, ← cd_second d h _ hh i 2,
    ← cd_second d h _ hh i 0, ← cd_second d h _ hh i 1]
  have ht : (lin d u x + b) (i,2) = x (i,2) + Real.log ‖u i‖ := by
    simp [PiLp.add_apply, lin_apply, hb]
  have he : Real.exp (2 * (x (i,2) + Real.log ‖u i‖)) =
      Real.exp (2 * x (i,2)) * ‖u i‖ ^ 2 := by
    rw [mul_add, Real.exp_add]
    congr 1
    simpa using Real.exp_nat_mul (Real.log ‖u i‖) 2 |>.trans
      (congrArg (fun t : ℝ => t ^ 2) (Real.exp_log (norm_pos_iff.mpr (hu i))))
  rw [ht, he]
  simp only [Complex.real_smul]
  push_cast
  ring
private theorem laplacian_congr (d : ℕ) (h f : Space d → ℂ) (x : Space d)
    (he : h =ᶠ[nhds x] f) : laplacian d h x = laplacian d f x := by
  have hd (i : Fin d) (k : Fin 3) : coordinateDerivative d i k h =ᶠ[nhds x]
      coordinateDerivative d i k f := (he.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k)) hy
  have hdd (i : Fin d) (k : Fin 3) := congrArg (fun A => A (coordinateVector d i k))
    ((hd i k).fderiv_eq (𝕜 := ℝ))
  have hd0 (i : Fin d) (k : Fin 3) := (hd i k).eq_of_nhds
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coordinateDerivative] at hd0 hdd ⊢
  rw [hdd, hdd, hdd, hd0]
private theorem laplacian_mul (d : ℕ) (h : Space d → ℂ) (x : Space d) (c : ℂ)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) h x) :
    laplacian d (fun y => c * h y) x = c * laplacian d h x := by
  have ht : ∀ᶠ y in nhds x, DifferentiableAt ℝ h y :=
    ((hh.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)).mono
      (fun y hy => hy.differentiableAt (by simp))
  have he (i : Fin d) (k : Fin 3) : coordinateDerivative d i k (fun y => c * h y) =ᶠ[nhds x]
      (fun y => c * coordinateDerivative d i k h y) := by
    filter_upwards [ht] with y hy
    simpa [coordinateDerivative] using congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k))
      (hy.hasFDerivAt.const_mul c).fderiv
  have hd (i : Fin d) (k : Fin 3) :
      coordinateDerivative d i k (coordinateDerivative d i k (fun y => c * h y)) x =
      c * coordinateDerivative d i k (coordinateDerivative d i k h) x := by
    change fderiv ℝ (coordinateDerivative d i k (fun y => c * h y)) x _ = _
    rw [(he i k).fderiv_eq]
    have hs : ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k h) x :=
      (hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
    simpa [coordinateDerivative] using congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k))
      ((hs.differentiableAt (by simp)).hasFDerivAt.const_mul c).fderiv
  unfold laplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hd, hd, hd, (he i 2).eq_of_nhds]
  ring
private theorem upper_fst (A : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (ha : A 1 0 = 0) (u : ℂ) (hr : A 0 0 = u * A 1 1) (z : KPArch.H3) :
    (KPArch.action A z).1 = u * z.1 + A 0 1 / A 1 1 := by
  have hd : A 1 1 ≠ 0 := by
    intro hz
    exact A.det_ne_zero (by simp [Matrix.det_fin_two, ha, hz])
  have hn : (‖A 1 1‖ ^ 2 : ℂ) = A 1 1 * star (A 1 1) := by
    simp [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change _ / _ = _
  simp only [KPArch.actionDenominator, ha, zero_mul, zero_add, norm_zero, zero_pow,
    add_zero, hr, star_zero, mul_zero, zero_mul]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero, Complex.ofReal_pow]
  rw [hn]
  have hs : star (A 1 1) ≠ 0 := star_ne_zero.mpr hd
  field_simp
  <;> ring
 def shift (d : ℕ) (u b : Fin d → ℂ) : Space d :=
  WithLp.toLp 2 (fun j => ![(b j.1).re, (b j.1).im, Real.log ‖u j.1‖] j.2)
private theorem upper_real (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (u : Fin d → ℂ) (hu : ∀ i, u i ≠ 0)
    (hz : ∀ i, g i 1 0 = 0) (hr : ∀ i, g i 0 0 = u i * g i 1 1)
    (x : Space d) : real d (KPArch.productAction d g (arch d x)) =
      lin d u x + shift d u (fun i => g i 0 1 / g i 1 1) := by
  ext ⟨i,k⟩
  fin_cases k
  · simp [real, KPArch.productAction, upper_fst _ (hz i) _ (hr i),
      lin_apply, shift, arch, Complex.mul_re]
  · simp [real, KPArch.productAction, upper_fst _ (hz i) _ (hr i),
      lin_apply, shift, arch, Complex.mul_im, add_comm]
  · simp [real, KPArch.productAction, KPCuspLogShape.upper_action_snd _ (hz i) _ (hu i) (hr i),
      lin_apply, shift, arch]
private theorem upper_equivariant_laplacian (d : ℕ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) (u : Fin d → ℂ)
    (hu : ∀ i, u i ≠ 0) (hz : ∀ i, g i 1 0 = 0) (hr : ∀ i, g i 0 0 = u i * g i 1 1)
    (h : Space d → ℂ) (x : Space d) (c : ℂ)
    (hc : (fun y => h (real d (KPArch.productAction d g (arch d y)))) =ᶠ[nhds x]
      (fun y => c * h y))
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) h x)
    (hy : ContDiffAt ℝ (⊤ : ℕ∞) h (real d (KPArch.productAction d g (arch d x)))) :
    laplacian d h (real d (KPArch.productAction d g (arch d x))) = c * laplacian d h x := by
  simp only [upper_real d g u hu hz hr] at hc hy ⊢
  rw [← affine_laplacian d u _ (fun i => rfl) hu h x hy,
    laplacian_congr d _ _ x hc, laplacian_mul d h x c hx]

private lemma differential_add (d : ℕ) (f g : Space d → ℂ) (x : Space d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    differential d (fun y => f y + g y) x = differential d f x + differential d g x := by
  have hfd : fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x + fderiv ℝ g x :=
    fderiv_add hf hg
  ext i k
  fin_cases k <;>
    (simp [differential, coordinateDerivative, hfd, Pi.add_apply, ContinuousLinearMap.add_apply]
     ; try ring)

private lemma two_mul_re_pairing (d : ℕ) (U W : Cotangent d) :
    2 * (pairing d U W).re =
      (∑ i, ∑ k, ‖(U + W) i k‖ ^ 2) - (∑ i, ∑ k, ‖U i k‖ ^ 2) -
        (∑ i, ∑ k, ‖W i k‖ ^ 2) := by
  have hterm : ∀ (i : Fin d) (k : Fin 3),
      2 * (star (U i k) * W i k).re =
        ‖(U + W) i k‖ ^ 2 - ‖U i k‖ ^ 2 - ‖W i k‖ ^ 2 := by
    intro i k
    have h1 : (star (U i k) * W i k).re =
        (U i k).re * (W i k).re + (U i k).im * (W i k).im := by
      simp [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have h2 : ‖(U + W) i k‖ ^ 2 =
        ‖U i k‖ ^ 2 + ‖W i k‖ ^ 2 +
          2 * ((U i k).re * (W i k).re + (U i k).im * (W i k).im) := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Pi.add_apply, Complex.add_re, Complex.add_im]
      ring
    rw [h1, h2]; ring
  have hre : (pairing d U W).re = ∑ i, ∑ k, (star (U i k) * W i k).re := by
    simp only [pairing]
    rw [← Complex.reCLM_apply]
    simp only [map_sum, Complex.reCLM_apply]
  calc 2 * (pairing d U W).re = 2 * (∑ i, ∑ k, (star (U i k) * W i k).re) := by rw [hre]
    _ = ∑ i, ∑ k, 2 * (star (U i k) * W i k).re := by
        simp only [Finset.mul_sum]
    _ = ∑ i, ∑ k, (‖(U + W) i k‖ ^ 2 - ‖U i k‖ ^ 2 - ‖W i k‖ ^ 2) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro k _
        exact hterm i k
    _ = (∑ i, ∑ k, ‖(U + W) i k‖ ^ 2) - (∑ i, ∑ k, ‖U i k‖ ^ 2) -
          (∑ i, ∑ k, ‖W i k‖ ^ 2) := by
        simp only [Finset.sum_sub_distrib]

 def toCoord {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) : KPCuspCharts.Coordinates F :=
  (((fun i => (z i).1),
    ⟨KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) z,
      KPCuspLogShape.shapeCoordinates_mem_hyperplane _
        (Nat.ne_of_gt hd) z⟩),
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z)

private theorem toArch_toCoord {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspCharts.toArch F (toCoord hd z) = z := by
  funext i
  simp [KPCuspCharts.toArch, toCoord, KPCuspLogShape.shapeCoordinates]

private theorem action_meanHeight
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (s : S) (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z) =
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z := by
  have hd := G.positive_dimension
  obtain ⟨A, hA, hA10⟩ := D.upper (s : KPCuspArithmetic.PGL2 F) s.2
  conv_lhs => rw [← toArch_toCoord hd z]
  rw [G.actual_action s A hA hA10 (toCoord hd z), KPCuspCharts.toArch_meanHeight F hd]
  rfl

private theorem u_action_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (s : S) (z : KPArch.Space (KPCuspLogShape.dimension F))
    (hz : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z) :
    u (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z) = u z := by
  have hd := G.positive_dimension
  set p' : {p : KPCuspCharts.Coordinates F // T < p.2} :=
    ⟨toCoord hd z, by
      change T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z
      exact hz⟩ with hp'def
  have hsz : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z) := by
    rw [action_meanHeight G s z]; exact hz
  set q' : {p : KPCuspCharts.Coordinates F // T < p.2} :=
    ⟨toCoord hd (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z), by
      change T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z)
      exact hsz⟩ with hq'def
  have hrel : KPCuspCharts.highRelation F S T p' q' := by
    refine ⟨s⁻¹, ?_⟩
    show s⁻¹ • KPCuspCharts.toArch F q'.val = KPCuspCharts.toArch F p'.val
    rw [hq'def, hp'def]
    simp only [toArch_toCoord hd]
    change s⁻¹ • (s • z) = z
    rw [← mul_smul, inv_mul_cancel, one_smul]
  have hfin := hinv p' q' hrel
  simp only [hp'def, hq'def, toArch_toCoord hd] at hfin
  exact hfin.symm

private theorem pairing_re_invariant
    (d : ℕ) (g0 : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (Ac U : Space d → ℂ) (x : Space d)
    (hAcX : ContDiffAt ℝ (⊤ : ℕ∞) Ac x)
    (hAcY : ContDiffAt ℝ (⊤ : ℕ∞) Ac (real d (KPArch.productAction d g0 (arch d x))))
    (hUX : ContDiffAt ℝ (⊤ : ℕ∞) U x)
    (hUY : ContDiffAt ℝ (⊤ : ℕ∞) U (real d (KPArch.productAction d g0 (arch d x))))
    (hAceq : (Ac ∘ fun z => real d (KPArch.productAction d g0 (arch d z)))
      =ᶠ[𝓝 x] fun z => (1 : ℂ) * Ac z)
    (hUeq : (U ∘ fun z => real d (KPArch.productAction d g0 (arch d z)))
      =ᶠ[𝓝 x] fun z => (1 : ℂ) * U z) :
    (pairing d (differential d Ac (real d (KPArch.productAction d g0 (arch d x))))
        (differential d U (real d (KPArch.productAction d g0 (arch d x))))).re =
      (pairing d (differential d Ac x) (differential d U x)).re := by
  have hAUeq : ((fun z => Ac z + U z) ∘ fun z => real d (KPArch.productAction d g0 (arch d z)))
      =ᶠ[𝓝 x] fun z => (1 : ℂ) * (Ac z + U z) := by
    filter_upwards [hAceq, hUeq] with z h1 h2
    simp only [Function.comp_apply] at h1 h2 ⊢
    rw [h1, h2]; ring
  have hAUX : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Ac z + U z) x := hAcX.add hUX
  have hAUY : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Ac z + U z)
      (real d (KPArch.productAction d g0 (arch d x))) := hAcY.add hUY
  have hSAU := KPLocalizedFormGraph.ChartEnergyGeometry.differential_invariant d g0 (fun z => Ac z + U z) x 1
    (hAUX.differentiableAt (by simp)) (hAUY.differentiableAt (by simp)) hAUeq (by norm_num)
  have hSA := KPLocalizedFormGraph.ChartEnergyGeometry.differential_invariant d g0 Ac x 1
    (hAcX.differentiableAt (by simp)) (hAcY.differentiableAt (by simp)) hAceq (by norm_num)
  have hSU := KPLocalizedFormGraph.ChartEnergyGeometry.differential_invariant d g0 U x 1
    (hUX.differentiableAt (by simp)) (hUY.differentiableAt (by simp)) hUeq (by norm_num)
  have hY := two_mul_re_pairing d
    (differential d Ac (real d (KPArch.productAction d g0 (arch d x))))
    (differential d U (real d (KPArch.productAction d g0 (arch d x))))
  have hXp := two_mul_re_pairing d (differential d Ac x) (differential d U x)
  have eY : differential d Ac (real d (KPArch.productAction d g0 (arch d x))) +
        differential d U (real d (KPArch.productAction d g0 (arch d x))) =
      differential d (fun z => Ac z + U z) (real d (KPArch.productAction d g0 (arch d x))) :=
    (differential_add d Ac U _ (hAcY.differentiableAt (by simp))
      (hUY.differentiableAt (by simp))).symm
  have eX : differential d Ac x + differential d U x =
      differential d (fun z => Ac z + U z) x :=
    (differential_add d Ac U _ (hAcX.differentiableAt (by simp))
      (hUX.differentiableAt (by simp))).symm
  rw [eY] at hY
  rw [eX] at hXp
  have h2 : 2 * (pairing d
        (differential d Ac (real d (KPArch.productAction d g0 (arch d x))))
        (differential d U (real d (KPArch.productAction d g0 (arch d x))))).re =
      2 * (pairing d (differential d Ac x) (differential d U x)).re := by
    have hSAU' : (∑ i, ∑ k, ‖differential d (fun z => Ac z + U z)
          (real d (KPArch.productAction d g0 (arch d x))) i k‖ ^ 2) =
        ∑ i, ∑ k, ‖differential d (fun z => Ac z + U z) x i k‖ ^ 2 := hSAU
    have hSA' : (∑ i, ∑ k, ‖differential d Ac
          (real d (KPArch.productAction d g0 (arch d x))) i k‖ ^ 2) =
        ∑ i, ∑ k, ‖differential d Ac x i k‖ ^ 2 := hSA
    have hSU' : (∑ i, ∑ k, ‖differential d U
          (real d (KPArch.productAction d g0 (arch d x))) i k‖ ^ 2) =
        ∑ i, ∑ k, ‖differential d U x i k‖ ^ 2 := hSU
    rw [hY, hXp, hSAU', hSA', hSU']
  exact mul_left_cancel₀ two_ne_zero h2

theorem cutoff_scalar_codifferential_high_orbit_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a)
    (p q : {p : KPCuspCharts.Coordinates F // T < p.2})
    (hrel : KPCuspCharts.highRelation F S T p q) :
    (codifferential (KPCuspLogShape.dimension F)
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p.val))).re =
    (codifferential (KPCuspLogShape.dimension F)
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val))).re := by
  have hd : 0 < KPCuspLogShape.dimension F := G.positive_dimension
  obtain ⟨s, hs⟩ := hrel
  obtain ⟨A, hA, hA10⟩ := D.upper (s : KPCuspArithmetic.PGL2 F) s.2
  let gC : Fin (KPCuspLogShape.dimension F) → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
    fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A
  let uvec : Fin (KPCuspLogShape.dimension F) → ℂ :=
    fun i => (KPCusp.complexPlace F i).embedding ((D.ratio s : Fˣ) : F)
  have hgz : ∀ i, gC i 1 0 = 0 := fun i => by
    simp only [gC, Matrix.GeneralLinearGroup.map_apply, hA10, map_zero]
  have hgr : ∀ i, gC i 0 0 = uvec i * gC i 1 1 := fun i => by
    simp only [gC, uvec, Matrix.GeneralLinearGroup.map_apply,
      D.ratioFormula s A hA hA10, map_mul]
  have hgu : ∀ i, uvec i ≠ 0 := fun i =>
    (map_ne_zero (KPCusp.complexPlace F i).embedding).mpr (Units.ne_zero _)
  have hact : ∀ z, KPArch.productAction (KPCuspLogShape.dimension F) gC z =
      KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z := by
    intro z
    have h1 : KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z =
        KPArch.productAction (KPCuspLogShape.dimension F) gC z := by
      rw [← hA, KPCuspSiegel.action_mk F A z]; rfl
    exact h1.symm
  set X : Space (KPCuspLogShape.dimension F) :=
    real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val) with hXdef
  set Y : Space (KPCuspLogShape.dimension F) :=
    real (KPCuspLogShape.dimension F)
      (KPArch.productAction (KPCuspLogShape.dimension F) gC
        (arch (KPCuspLogShape.dimension F) X)) with hYdef
  have hs' : KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) (KPCuspCharts.toArch F q.val) =
      KPCuspCharts.toArch F p.val := hs
  have hYX : Y = real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p.val) := by
    rw [hYdef, hXdef, arch_real, hact, hs']
  have harchX : arch (KPCuspLogShape.dimension F) X = KPCuspCharts.toArch F q.val := by
    rw [hXdef, arch_real]
  have harchY : arch (KPCuspLogShape.dimension F) Y = KPCuspCharts.toArch F p.val := by
    rw [hYX, arch_real]
  rw [← hYX]
  let U : Space (KPCuspLogShape.dimension F) → ℂ :=
    fun z => (u (arch (KPCuspLogShape.dimension F) z) : ℂ)
  let Ac : Space (KPCuspLogShape.dimension F) → ℂ :=
    fun z => (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) z)) : ℂ)
  have hflux : cutoffScalarFlux (KPCuspLogShape.dimension F) u a =
      fun q i k => star (Ac q) * differential (KPCuspLogShape.dimension F) U q i k := by
    funext q i k
    simp only [cutoffScalarFlux, scalarDifferential, U, Ac, Complex.star_def,
      Complex.conj_ofReal]
  have hXh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) X) := by
    rw [harchX, KPCuspCharts.toArch_meanHeight F hd]; exact q.2
  have hYh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) Y) := by
    rw [harchY, KPCuspCharts.toArch_meanHeight F hd]; exact p.2
  have hmeanOpen : IsOpen {z : Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) z)} :=
    isOpen_lt continuous_const ((smooth_mean _).continuous.comp (smooth_arch _).continuous)
  have hN : ∀ᶠ z in 𝓝 X, T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) z) := hmeanOpen.mem_nhds hXh
  have hU_at : ∀ z, T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) z) → ContDiffAt ℝ (⊤ : ℕ∞) U z := fun z hz => by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hu.contDiffAt ((isOpen_lt continuous_const (smooth_mean _).continuous).mem_nhds
        hz)).comp z (smooth_arch _).contDiffAt)
  have hAc_at : ∀ z, ContDiffAt ℝ (⊤ : ℕ∞) Ac z := fun z =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((ha.1.comp ((smooth_mean _).comp (smooth_arch _))).contDiffAt)
  have hUX := hU_at X hXh
  have hUY := hU_at Y hYh
  have hAcX := hAc_at X
  have hAcY := hAc_at Y
  have hAceq : (Ac ∘ fun z => real (KPCuspLogShape.dimension F)
      (KPArch.productAction (KPCuspLogShape.dimension F) gC
        (arch (KPCuspLogShape.dimension F) z)))
      =ᶠ[𝓝 X] fun z => (1 : ℂ) * Ac z := by
    filter_upwards with z
    dsimp only [Function.comp_apply, Ac]
    rw [one_mul, arch_real, hact, action_meanHeight G s]
  have hUeq : (U ∘ fun z => real (KPCuspLogShape.dimension F)
      (KPArch.productAction (KPCuspLogShape.dimension F) gC
        (arch (KPCuspLogShape.dimension F) z)))
      =ᶠ[𝓝 X] fun z => (1 : ℂ) * U z := by
    filter_upwards [hN] with z hz
    dsimp only [Function.comp_apply, U]
    rw [one_mul, arch_real, hact]
    exact congrArg (fun r : ℝ => (r : ℂ)) (u_action_invariant G u hinv s
      (arch (KPCuspLogShape.dimension F) z) hz)
  have hAcYX : Ac Y = Ac X := by
    rw [hYdef]
    dsimp only [Ac]
    rw [arch_real, hact, action_meanHeight G s]
  have hlap : laplacian (KPCuspLogShape.dimension F) U Y =
      laplacian (KPCuspLogShape.dimension F) U X := by
    have h := upper_equivariant_laplacian (KPCuspLogShape.dimension F) gC uvec hgu hgz hgr
      U X 1 hUeq hUX hUY
    rw [← hYdef] at h
    simpa using h
  have hpair := pairing_re_invariant (KPCuspLogShape.dimension F) gC Ac U X
    hAcX hAcY hUX hUY hAceq hUeq
  have hYc : (codifferential (KPCuspLogShape.dimension F)
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) Y).re =
      (star (Ac Y) * laplacian (KPCuspLogShape.dimension F) U Y -
        pairing (KPCuspLogShape.dimension F)
          (differential (KPCuspLogShape.dimension F) Ac Y)
          (differential (KPCuspLogShape.dimension F) U Y)).re := by
    rw [hflux, codifferential_star_mul (KPCuspLogShape.dimension F) Ac
      (differential (KPCuspLogShape.dimension F) U) Y
      (hAcY.differentiableAt (by simp))
      (fun i k => (differential_smoothAt _ U Y hUY i k).differentiableAt (by simp))]
    rw [codifferential_differential_at _ U Y hUY]
  have hXc : (codifferential (KPCuspLogShape.dimension F)
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) X).re =
      (star (Ac X) * laplacian (KPCuspLogShape.dimension F) U X -
        pairing (KPCuspLogShape.dimension F)
          (differential (KPCuspLogShape.dimension F) Ac X)
          (differential (KPCuspLogShape.dimension F) U X)).re := by
    rw [hflux, codifferential_star_mul (KPCuspLogShape.dimension F) Ac
      (differential (KPCuspLogShape.dimension F) U) X
      (hAcX.differentiableAt (by simp))
      (fun i k => (differential_smoothAt _ U X hUX i k).differentiableAt (by simp))]
    rw [codifferential_differential_at _ U X hUX]
  rw [hYc, hXc, hAcYX, hlap, Complex.sub_re, Complex.sub_re, hpair]

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration

end
