module

public import DedekindZetaZeroFree.Geometry.Hyperbolic.DivergenceIsometry

@[expose] public section

noncomputable section
open scoped ContDiff BigOperators
open Filter Topology
namespace DedekindZetaZeroFree.KPShift68LaplacianInvariant
open HyperbolicChart
 def realGrad (d : ℕ) (f : Space d → ℝ) (x : Space d) : Space d :=
  WithLp.toLp 2 (fun ik => (if ik.2 = 2 then 1 else Real.exp (2 * x (ik.1,2))) *
    fderiv ℝ f x (coordinateVector d ik.1 ik.2))
private theorem vector_expansion (d : ℕ) (u : Space d) :
    (∑ i : Fin d, ∑ k : Fin 3, u (i,k) • coordinateVector d i k) = u := by
  ext j
  simp [coordinateVector, WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single j.1]
  · rw [Finset.sum_eq_single j.2]
    · simp
    · intro k _ hk
      simp [hk, Ne.symm hk, Prod.ext_iff]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro k _
    simp [hi, Ne.symm hi, Prod.ext_iff]
  · simp
private theorem realGrad_duality (d : ℕ) (f : Space d → ℝ) (x u : Space d) :
    metric d x (realGrad d f x) u = fderiv ℝ f x u := by
  have he (i : Fin d) : Real.exp (-2 * x (i,2)) * Real.exp (2 * x (i,2)) = 1 := by
    rw [← Real.exp_add, show -2 * x (i,2) + 2 * x (i,2) = 0 by ring, Real.exp_zero]
  conv_rhs => rw [← vector_expansion d u]
  rw [map_sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  unfold metric realGrad
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_three]
  simp only [WithLp.ofLp_toLp, if_pos (show (2 : Fin 3) = 2 from rfl), ite_true,
    if_neg (by decide : ¬((0 : Fin 3) = 2)), if_neg (by decide : ¬((1 : Fin 3) = 2)), one_mul]
  calc _ = fderiv ℝ f x (coordinateVector d i 2) * u (i,2) +
      (Real.exp (-2 * x (i,2)) * Real.exp (2 * x (i,2))) *
        (fderiv ℝ f x (coordinateVector d i 0) * u (i,0) + fderiv ℝ f x (coordinateVector d i 1) * u (i,1)) := by ring
       _ = _ := by rw [he]; ring
private theorem realGrad_smoothAt (d : ℕ) (f : Space d → ℝ) (x : Space d)
    (hf : ContDiffAt ℝ 2 f x) : ContDiffAt ℝ 1 (realGrad d f) x := by
  apply (contDiffAt_piLp 2).mpr
  intro k
  dsimp only [realGrad, WithLp.ofLp_toLp]
  apply ContDiffAt.mul
  · split_ifs <;> fun_prop
  · exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
private theorem metric_separates (d : ℕ) (x v w : Space d)
    (h : ∀ u, metric d x v u = metric d x w u) : v = w := by
  have he : ∀ u, inner ℝ (CotangentLogCoframe.C d x v) (CotangentLogCoframe.C d x u) =
      inner ℝ (CotangentLogCoframe.C d x w) (CotangentLogCoframe.C d x u) := by
    intro u
    simpa only [CotangentLogCoframe.inner_C] using h u
  apply (CotangentLogCoframe.C d x).injective
  apply ext_inner_right ℝ
  intro u
  simpa [CotangentLogCoframe.H] using he (CotangentLogCoframe.H d x u)
private theorem realGrad_pushforward (d : ℕ) (ψ : Space d → Space d)
    (hψ : ContDiff ℝ ∞ ψ) (hm : ∀ x u v, metric d (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = metric d x u v)
    (f : Space d → ℝ) (x : Space d) (hf : DifferentiableAt ℝ f (ψ x)) :
    realGrad d f (ψ x) = fderiv ℝ ψ x (realGrad d (f ∘ ψ) x) := by
  have hi : Function.Injective (fderiv ℝ ψ x) := by
    intro u v huv
    apply metric_separates d x u v
    intro w
    rw [← hm x u w, ← hm x v w, huv]
  have hs : Function.Surjective (fderiv ℝ ψ x) := LinearMap.injective_iff_surjective.mp hi
  apply metric_separates d (ψ x)
  intro w
  obtain ⟨u,rfl⟩ := hs w
  rw [hm, realGrad_duality, realGrad_duality]
  rw [fderiv_comp x hf (hψ.differentiable (by simp) _)]
  rfl
private theorem projected_laplacian (d : ℕ) (f : Space d → ℂ) (L : ℂ →L[ℝ] ℝ) (x : Space d) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    L (laplacian d f x) =
      ∑ i : Fin d, (-(fderiv ℝ (fun y => realGrad d (L ∘ f) y (i,2)) x (coordinateVector d i 2)) +
        2 * realGrad d (L ∘ f) x (i,2) -
        fderiv ℝ (fun y => realGrad d (L ∘ f) y (i,0)) x (coordinateVector d i 0) -
        fderiv ℝ (fun y => realGrad d (L ∘ f) y (i,1)) x (coordinateVector d i 1)) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by simp)
  have hnear : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y :=
    ((hf.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)).mono
      (fun y hy => hy.differentiableAt (by simp))
  have hfirst (i : Fin d) (k : Fin 3) (y : Space d) (hy : DifferentiableAt ℝ f y) :
      fderiv ℝ (L ∘ f) y (coordinateVector d i k) = L (fderiv ℝ f y (coordinateVector d i k)) := by
    rw [fderiv_comp y L.differentiableAt hy, L.fderiv]
    rfl
  have hs (i : Fin d) (k : Fin 3) : DifferentiableAt ℝ (fun y => fderiv ℝ f y (coordinateVector d i k)) x := by
    exact ((hf.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hsecond (i : Fin d) (k : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ (L ∘ f) y (coordinateVector d i k)) x (coordinateVector d i k) =
        L (fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector d i k)) x (coordinateVector d i k)) := by
    have he : (fun y => fderiv ℝ (L ∘ f) y (coordinateVector d i k)) =ᶠ[nhds x]
        (fun y => L (fderiv ℝ f y (coordinateVector d i k))) :=
      hnear.mono (fun y hy => hfirst i k y hy)
    rw [he.fderiv_eq]
    rw [show (fun y => L (fderiv ℝ f y (coordinateVector d i k))) =
      L ∘ (fun y => fderiv ℝ f y (coordinateVector d i k)) from rfl,
      fderiv_comp x L.differentiableAt (hs i k), L.fderiv]
    rfl
  have hL : ContDiffAt ℝ (⊤ : ℕ∞) (L ∘ f) x := L.contDiff.contDiffAt.comp x hf
  have hLf (i : Fin d) (k : Fin 3) : DifferentiableAt ℝ
      (fun y => fderiv ℝ (L ∘ f) y (coordinateVector d i k)) x :=
    ((hL.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hprod (i : Fin d) (k : Fin 3) (hk : k ≠ 2) :
      fderiv ℝ (fun y => Real.exp (2*y (i,2)) * fderiv ℝ (L ∘ f) y (coordinateVector d i k)) x (coordinateVector d i k) =
        Real.exp (2*x (i,2)) * L (fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector d i k)) x (coordinateVector d i k)) := by
    have hE : DifferentiableAt ℝ (fun y : Space d => Real.exp (2*y (i,2))) x := by fun_prop
    have he : fderiv ℝ (fun y : Space d => Real.exp (2*y (i,2))) x (coordinateVector d i k) = 0 := by
      have hc := ((EuclideanSpace.proj (𝕜 := ℝ) (i,2)).hasFDerivAt (x := x)).const_mul 2
      have hc' : HasFDerivAt (fun y : Space d => 2*y (i,2)) ((2 : ℝ) • EuclideanSpace.proj (𝕜 := ℝ) (i,2)) x := hc
      rw [hc'.exp.fderiv]
      simp [coordinateVector, hk, Ne.symm hk]
    rw [fderiv_fun_mul hE (hLf i k)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      he, mul_zero, add_zero, hsecond]
  unfold laplacian coordinateDerivative
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h0 : (fun y => realGrad d (L ∘ f) y (i,0)) =
      fun y => Real.exp (2*y (i,2)) * fderiv ℝ (L ∘ f) y (coordinateVector d i 0) := by funext y; simp [realGrad]
  have h1 : (fun y => realGrad d (L ∘ f) y (i,1)) =
      fun y => Real.exp (2*y (i,2)) * fderiv ℝ (L ∘ f) y (coordinateVector d i 1) := by funext y; simp [realGrad]
  have h2 : (fun y => realGrad d (L ∘ f) y (i,2)) =
      fun y => fderiv ℝ (L ∘ f) y (coordinateVector d i 2) := by funext y; simp [realGrad]
  rw [h0, h1, h2, hprod i 0 (by decide), hprod i 1 (by decide), hsecond]
  have hm (a : ℝ) (z : ℂ) : L ((a : ℂ) * z) = a * L z := by
    rw [show (a : ℂ) * z = a • z by simp [Complex.real_smul], map_smul]; rfl
  simp only [map_sub, map_neg, hm, realGrad, WithLp.ofLp_toLp, ite_true, one_mul, hfirst _ _ x hfd]
  simp only [map_add, map_neg, hm]
  have h2mul (z : ℂ) : L (2 * z) = 2 * L z := hm 2 z
  rw [h2mul]
  ring

theorem isometry_pullback_at (d : ℕ) (ψ : Space d → Space d)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hm : ∀ y u v, metric d (ψ y) (fderiv ℝ ψ y u) (fderiv ℝ ψ y v) = metric d y u v)
    (f : Space d → ℂ) (x : Space d) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (ψ x)) :
    laplacian d (f ∘ ψ) x = laplacian d f (ψ x) := by
  have hcomp := hf.comp x hψ.contDiffAt
  have hnear : ∀ᶠ y in nhds (ψ x), DifferentiableAt ℝ f y :=
    ((hf.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)).mono
      (fun y hy => hy.differentiableAt (by simp))
  have hproj (L : ℂ →L[ℝ] ℝ) :
      L (laplacian d (f ∘ ψ) x) = L (laplacian d f (ψ x)) := by
    rw [projected_laplacian d (f ∘ ψ) L x hcomp, projected_laplacian d f L (ψ x) hf]
    apply Eq.symm
    apply real_divergence_isometry d ψ (realGrad d (L ∘ (f ∘ ψ))) (realGrad d (L ∘ f)) x
      (hψ.contDiffAt.of_le (by simp))
      (realGrad_smoothAt d _ x ((L.contDiff.contDiffAt.comp x hcomp).of_le (by simp)))
      (realGrad_smoothAt d _ (ψ x) ((L.contDiff.contDiffAt.comp (ψ x) hf).of_le (by simp)))
      (Filter.Eventually.of_forall (fun y => hm y))
    filter_upwards [hψ.continuous.continuousAt.eventually hnear] with y hy
    exact realGrad_pushforward d ψ hψ hm (L ∘ f) y (L.differentiableAt.comp (ψ y) hy)
  exact Complex.ext (hproj Complex.reCLM) (hproj Complex.imCLM)

 def act (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) : Space d → Space d :=
    fun x => (CotangentLogCoframe.A d).symm (KPArch.productAction d g (CotangentLogCoframe.A d x))
private theorem act_smooth (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) : ContDiff ℝ ∞ (act d g) := by
  exact (CotangentLogCoframe.A d).symm.contDiff.comp
    (((KPArch.productAction_contDiff d g).of_le (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top)).comp
      (CotangentLogCoframe.A d).contDiff)
private theorem act_metric (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x u v : Space d) : metric d (act d g x) (fderiv ℝ (act d g) x u) (fderiv ℝ (act d g) x v) = metric d x u v := by
  have hquad (w : Space d) : metric d (act d g x) (fderiv ℝ (act d g) x w) (fderiv ℝ (act d g) x w) = metric d x w w := by
    have hder := (CotangentLogCoframe.A d).symm.hasFDerivAt.comp x
      (((KPArch.productAction_contDiff d g).differentiable (by simp) (CotangentLogCoframe.A d x)).hasFDerivAt.comp x
        (CotangentLogCoframe.A d).hasFDerivAt)
    change HasFDerivAt (act d g) _ x at hder
    rw [← CotangentLogCoframe.metric_A, hder.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      act, ContinuousLinearEquiv.apply_symm_apply]
    exact (KPArch.metric_invariant d g (CotangentLogCoframe.A d x)
      (CotangentLogCoframe.A d w)).trans (CotangentLogCoframe.metric_A d x w)
  have hpol (y a b : Space d) : metric d y (a+b) (a+b) = metric d y a a + 2*metric d y a b + metric d y b b := by
    unfold metric
    simp only [PiLp.add_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he := hquad (u+v)
  rw [map_add, hpol, hpol, hquad, hquad] at he
  linarith

theorem productAction_pullback_at (d : ℕ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (f : Space d → ℂ) (x : Space d)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f
      ((CotangentLogCoframe.A d).symm (KPArch.productAction d g (CotangentLogCoframe.A d x)))) :
    laplacian d (fun y => f
      ((CotangentLogCoframe.A d).symm (KPArch.productAction d g (CotangentLogCoframe.A d y)))) x =
    laplacian d f
      ((CotangentLogCoframe.A d).symm (KPArch.productAction d g (CotangentLogCoframe.A d x))) :=
  isometry_pullback_at d (act d g) (act_smooth d g) (act_metric d g) f x hf

end DedekindZetaZeroFree.KPShift68LaplacianInvariant

end
