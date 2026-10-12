module

public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.LogarithmicCoordinates

@[expose] public section

noncomputable section
open scoped ContDiff BigOperators
open Filter Topology
namespace DedekindZetaZeroFree.KPContArchLaplacianNaturality
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
    rw [← Real.exp_add]; convert Real.exp_zero using 1 <;> ring
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
private theorem realGrad_smooth (d : ℕ) (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 1 (realGrad d f) := by
  apply (contDiff_piLp 2).mpr
  intro k
  dsimp only [realGrad, WithLp.ofLp_toLp]
  apply ContDiff.mul
  · split_ifs <;> fun_prop
  · exact (hf.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const
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
    (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f) (x : Space d) :
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
  rw [fderiv_comp x (hf.differentiable (by simp) _) (hψ.differentiable (by simp) _)]
  rfl
private theorem projected_laplacian (d : ℕ) (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f)
    (L : ℂ →L[ℝ] ℝ) (x : Space d) :
    L (laplacian d f x) =
      ∑ i : Fin d, (-(fderiv ℝ (fun y => realGrad d (L ∘ f) y (i,2)) x (coordinateVector d i 2)) +
        2 * realGrad d (L ∘ f) x (i,2) -
        fderiv ℝ (fun y => realGrad d (L ∘ f) y (i,0)) x (coordinateVector d i 0) -
        fderiv ℝ (fun y => realGrad d (L ∘ f) y (i,1)) x (coordinateVector d i 1)) := by
  have hfd (y : Space d) : DifferentiableAt ℝ f y := hf.differentiable (by simp) y
  have hfirst (i : Fin d) (k : Fin 3) (y : Space d) :
      fderiv ℝ (L ∘ f) y (coordinateVector d i k) = L (fderiv ℝ f y (coordinateVector d i k)) := by
    rw [fderiv_comp y L.differentiableAt (hfd y), L.fderiv]
    rfl
  have hs (i : Fin d) (k : Fin 3) : DifferentiableAt ℝ (fun y => fderiv ℝ f y (coordinateVector d i k)) x := by
    exact ((hf.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by norm_num) x
  have hsecond (i : Fin d) (k : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ (L ∘ f) y (coordinateVector d i k)) x (coordinateVector d i k) =
        L (fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector d i k)) x (coordinateVector d i k)) := by
    simp_rw [hfirst]
    rw [show (fun y => L (fderiv ℝ f y (coordinateVector d i k))) =
      L ∘ (fun y => fderiv ℝ f y (coordinateVector d i k)) from rfl,
      fderiv_comp x L.differentiableAt (hs i k), L.fderiv]
    rfl
  have hL : ContDiff ℝ ∞ (L ∘ f) := L.contDiff.comp hf
  have hLf (i : Fin d) (k : Fin 3) : DifferentiableAt ℝ
      (fun y => fderiv ℝ (L ∘ f) y (coordinateVector d i k)) x :=
    ((hL.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by norm_num) x
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
  simp only [map_sub, map_neg, hm, realGrad, WithLp.ofLp_toLp, ite_true, one_mul, hfirst]
  simp only [map_add, map_neg, hm]
  have h2mul (z : ℂ) : L (2 * z) = 2 * L z := hm 2 z
  rw [h2mul]
  ring
private theorem real_isometry_laplacian (d : ℕ) (ψ : Space d → Space d) (hψ : ContDiff ℝ ∞ ψ)
    (hm : ∀ x u v, metric d (ψ x) (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = metric d x u v)
    (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f) (x : Space d) :
    laplacian d (f ∘ ψ) x = laplacian d f (ψ x) := by
  have hproj (L : ℂ →L[ℝ] ℝ) : L (laplacian d (f ∘ ψ) x) = L (laplacian d f (ψ x)) := by
    rw [projected_laplacian d (f ∘ ψ) (hf.comp hψ) L x, projected_laplacian d f hf L (ψ x)]
    apply Eq.symm
    apply real_divergence_isometry d ψ (realGrad d (L ∘ (f ∘ ψ))) (realGrad d (L ∘ f)) x
      (hψ.contDiffAt.of_le (by simp))
      ((realGrad_smooth d _ (L.contDiff.comp (hf.comp hψ))).contDiffAt)
      ((realGrad_smooth d _ (L.contDiff.comp hf)).contDiffAt)
      (Filter.Eventually.of_forall (fun y => hm y))
    exact Filter.Eventually.of_forall (fun y => realGrad_pushforward d ψ hψ hm (L ∘ f) (L.contDiff.comp hf) y)
  exact Complex.ext (hproj Complex.reCLM) (hproj Complex.imCLM)
 def act (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) : Space d → Space d :=
    fun x => (CotangentLogCoframe.A d).symm (KPArch.productAction d g (CotangentLogCoframe.A d x))
 theorem act_smooth (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) : ContDiff ℝ ∞ (act d g) := by
  exact (CotangentLogCoframe.A d).symm.contDiff.comp
    (((KPArch.productAction_contDiff d g).of_le (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top)).comp
      (CotangentLogCoframe.A d).contDiff)
 theorem act_metric (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
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
private theorem local_bridge (d : ℕ) (f : KPArch.Space d → ℂ) (hf : ContDiff ℝ ∞ f) (x : Space d) :
    KPContActualSphericalFlatStage.localLaplacian d f (CotangentLogCoframe.A d x) =
      laplacian d (f ∘ CotangentLogCoframe.A d) x := by
  have h := KPContArchLaplacianCoordinateBridge.bridge_equiv d d (Equiv.refl _) f hf x
  have ha : (fun k => CotangentLogCoframe.A d x k) = CotangentLogCoframe.A d x := funext (fun _ => rfl)
  have hf' : (fun y => f (fun k => CotangentLogCoframe.A d y k)) = f ∘ CotangentLogCoframe.A d := by
    funext y
    congr 1
  simp only [Equiv.refl_symm, Equiv.refl_apply] at h
  rw [ha, hf'] at h
  exact h

open DedekindZetaZeroFree

theorem localLaplacian_congr {d : ℕ} {f g : KPArch.Space d → ℂ}
    {x : KPArch.Space d} (h : f =ᶠ[nhds x] g) :
    KPContActualSphericalFlatStage.localLaplacian d f x =
      KPContActualSphericalFlatStage.localLaplacian d g x := by
  unfold KPContActualSphericalFlatStage.localLaplacian
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hd : (fun y => ((KPArch.volumeDensity d y * KPContActualSphericalFlatStage.inverseMetricWeight d y i j : ℝ) : ℂ) *
      fderiv ℝ f y (KPContActualSphericalFlatStage.coordinateDirection d i j)) =ᶠ[nhds x]
      (fun y => ((KPArch.volumeDensity d y * KPContActualSphericalFlatStage.inverseMetricWeight d y i j : ℝ) : ℂ) *
      fderiv ℝ g y (KPContActualSphericalFlatStage.coordinateDirection d i j)) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
  rw [hd.fderiv_eq]

theorem localLaplacian_const_mul (d : ℕ) (f : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : KPArch.Space d) (c : ℂ) :
    KPContActualSphericalFlatStage.localLaplacian d (fun y => c * f y) x =
      c * KPContActualSphericalFlatStage.localLaplacian d f x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hcf2 : ContDiff ℝ 2 (fun y => c * f y) := contDiff_const.mul hf2
  have he (h : KPArch.Space d → ℂ) (hh : ContDiff ℝ 2 h) :=
    KPContFlatCuspCasimirSpecialization.Δloc_coordinate_expression d h hh x
  change KPContFlatCuspCasimirSpecialization.Δloc d (fun y => c * f y) x = c * KPContFlatCuspCasimirSpecialization.Δloc d f x
  rw [he _ hcf2, he _ hf2, Finset.mul_sum]
  have hd (y : KPArch.Space d) : DifferentiableAt ℝ f y := hf2.differentiable (by norm_num) y
  have hfirst (y : KPArch.Space d) (u : KPArch.Space d) :
      fderiv ℝ (fun y => c * f y) y u = c * fderiv ℝ f y u := by
    rw [fderiv_const_mul (hd y) c]
    rfl
  have hsecond (u : KPArch.Space d) :
      fderiv ℝ (fun y => fderiv ℝ (fun y => c * f y) y u) x u =
        c * fderiv ℝ (fun y => fderiv ℝ f y u) x u := by
    simp_rw [hfirst]
    have hs : DifferentiableAt ℝ (fun y => fderiv ℝ f y u) x := by fun_prop
    rw [fderiv_const_mul hs c]
    rfl
  apply Finset.sum_congr rfl
  intro i _
  simp only [hsecond]
  simp only [hfirst, smul_eq_mul]
  ring

theorem pullback (d : ℕ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (f : KPArch.Space d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : KPArch.Space d) :
    KPContActualSphericalFlatStage.localLaplacian d
      (fun y => f (KPArch.productAction d g y)) x =
        KPContActualSphericalFlatStage.localLaplacian d f
          (KPArch.productAction d g x) := by
  let y := (CotangentLogCoframe.A d).symm x
  have ha : CotangentLogCoframe.A d y = x := (CotangentLogCoframe.A d).apply_symm_apply x
  have hb : CotangentLogCoframe.A d (act d g y) = KPArch.productAction d g x := by simp [act,ha]
  have hfg : ContDiff ℝ ∞ (fun y => f (KPArch.productAction d g y)) :=
    hf.comp ((KPArch.productAction_contDiff d g).of_le (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top))
  rw [← ha]
  rw [local_bridge d (fun y => f (KPArch.productAction d g y)) hfg]
  rw [ha, ← hb, local_bridge d f hf]
  have he : ((fun y => f (KPArch.productAction d g y)) ∘ CotangentLogCoframe.A d) =
      (f ∘ CotangentLogCoframe.A d) ∘ act d g := by funext z; simp [act,Function.comp_def]
  rw [he]
  exact real_isometry_laplacian d (act d g) (act_smooth d g) (act_metric d g)
    (f ∘ CotangentLogCoframe.A d) (hf.comp (CotangentLogCoframe.A d).contDiff) y

theorem equivariant (d : ℕ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (f : KPArch.Space d → ℂ) (x : KPArch.Space d) (c : ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : (fun y => f (KPArch.productAction d g y)) =ᶠ[nhds x]
      fun y => c * f y) :
    KPContActualSphericalFlatStage.localLaplacian d f (KPArch.productAction d g x) =
      c * KPContActualSphericalFlatStage.localLaplacian d f x := by
  have h1 : KPContActualSphericalFlatStage.localLaplacian d
        (fun y => f (KPArch.productAction d g y)) x =
      KPContActualSphericalFlatStage.localLaplacian d f
        (KPArch.productAction d g x) :=
    pullback d g f hf x
  rw [← h1]
  exact (localLaplacian_congr hc).trans (localLaplacian_const_mul d f hf x c)

end DedekindZetaZeroFree.KPContArchLaplacianNaturality

end
