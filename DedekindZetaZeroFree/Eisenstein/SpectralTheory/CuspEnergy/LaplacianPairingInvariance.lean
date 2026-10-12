module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialTests
public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.QuaternionicMobius.LaplacianNaturality

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactGreenRadialIntegrability
open KPMeanZeroWeightedEnergy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

private theorem smooth_arch (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem smooth_real (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (real d) := by
  apply (contDiff_piLp 2).mpr
  intro j
  rcases j with ⟨i, k⟩
  fin_cases k
  · simpa [real, Function.comp_def] using
      Complex.reCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using
      Complex.imCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using
      contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem smooth_mean (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem derivative_smoothAt (d : ℕ) (g : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (HyperbolicChart.coordinateDerivative d i k g) x :=
  (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

private theorem laplacian_smoothAt (d : ℕ) (g : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (HyperbolicChart.laplacian d g) x := by
  unfold HyperbolicChart.laplacian
  apply ContDiffAt.sum
  intro i hi
  have h (k : Fin 3) := derivative_smoothAt d g x hg i k
  have hh (k : Fin 3) := derivative_smoothAt d _ x (h k) i k
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : HyperbolicChart.Space d =>
      (Real.exp (2 * q (i, 2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((contDiffAt_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt).exp)
  exact ((hh 2).neg.add (contDiffAt_const.mul (h 2))).sub
    (he.mul ((hh 0).add (hh 1)))

private theorem representative_smoothAt (v : Representative ζ hζ S ρ V T)
    (x : HyperbolicChart.Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (v.val ∘ arch (KPCuspLogShape.dimension F)) x := by
  have hopen : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
    isOpen_lt continuous_const (smooth_mean _).continuous
  exact (v.smooth.contDiffAt (hopen.mem_nhds hx)).comp x (smooth_arch _).contDiffAt

private theorem chart_smooth : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : KPCuspCharts.Coordinates F =>
      real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)) :=
  (smooth_real _).comp ((KPCuspCharts.toArch_contDiff F).of_le (by simp))

private theorem character_norm (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by decide, ?_⟩
  have hp : ε ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp ε.property
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)) hp

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

theorem laplacian_action_invariant (d : ℕ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (h : HyperbolicChart.Space d → ℂ) (x : HyperbolicChart.Space d) (c : ℂ)
    (hc : (fun y => h (real d (KPArch.productAction d g (arch d y)))) =ᶠ[nhds x]
      (fun y => c * h y))
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) h x)
    (hy : ContDiffAt ℝ (⊤ : ℕ∞) h (real d (KPArch.productAction d g (arch d x)))) :
    HyperbolicChart.laplacian d h (real d (KPArch.productAction d g (arch d x))) =
      c * HyperbolicChart.laplacian d h x := by
  have hA : (CotangentLogCoframe.A d : Space d → KPArch.Space d) = arch d := by
    funext y
    ext i
    · apply Complex.ext <;> simp [CotangentLogCoframe.A_apply, arch]
    · rfl
  have hR : ((CotangentLogCoframe.A d).symm : KPArch.Space d → Space d) = real d := rfl
  have hp := KPShift68LaplacianInvariant.productAction_pullback_at d g h x
    (by simpa only [hA, hR] using hy)
  simp only [hA, hR] at hp
  rw [← hp, laplacian_congr d _ _ x hc, laplacian_mul d h x c hx]

theorem scalar_laplacian_continuousOn_and_invariant
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) :
    ContinuousOn (fun p => (star (v.scalar p) * v.laplacian p).re) {p | T < p.2} ∧
      ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
        KPCuspCharts.highRelation F S T p q →
          (star (v.scalar p.val) * v.laplacian p.val).re =
            (star (v.scalar q.val) * v.laplacian q.val).re := by
  constructor
  · apply continuousOn_of_forall_continuousAt
    intro p hp
    have hp' : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F)
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) := by
      rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
      exact hp
    have hv := representative_smoothAt v _ hp'
    have hlap : ContinuousAt
        (fun q : KPCuspCharts.Coordinates F =>
          HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
            (v.val ∘ arch (KPCuspLogShape.dimension F))
            (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q))) p :=
      (laplacian_smoothAt _ _ _ hv).continuousAt.comp
        (f := fun q : KPCuspCharts.Coordinates F =>
          real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q))
        chart_smooth.continuous.continuousAt
    have hsc : ContinuousAt v.scalar p := by
      have hopen : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
          T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
        isOpen_lt continuous_const (smooth_mean _).continuous
      have h1 : ContinuousAt v.val (KPCuspCharts.toArch F p) :=
        v.smooth.continuousOn.continuousAt (hopen.mem_nhds (by
          show T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
            (KPCuspCharts.toArch F p)
          rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
          exact hp))
      exact h1.comp (KPCuspCharts.toArch_contDiff F).continuous.continuousAt
    exact Complex.continuous_re.continuousAt.comp (hsc.star.mul hlap)
  · intro p q hrel
    change MulAction.orbitRel S (KPArch.Space (KPCuspLogShape.dimension F))
      (KPCuspCharts.toArch F p.val) (KPCuspCharts.toArch F q.val) at hrel
    obtain ⟨s, hs⟩ := hrel
    change KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F)
      (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val at hs
    obtain ⟨A, hA, hAz⟩ := D.upper s.val s.property
    set g : Fin (KPCuspLogShape.dimension F) → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
      fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A with hg
    have hs' : KPArch.productAction (KPCuspLogShape.dimension F) g
        (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val := by
      have h1 := hs
      rw [← hA, KPCuspSiegel.action_mk] at h1
      simp only [KPCuspSiegel.glAction, hg] at h1
      exact h1
    have hcont_p : ContDiffAt ℝ (⊤ : ℕ∞)
        (v.val ∘ arch (KPCuspLogShape.dimension F))
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p.val)) :=
      representative_smoothAt v _ (by
        rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact p.property)
    have hcont_q : ContDiffAt ℝ (⊤ : ℕ∞)
        (v.val ∘ arch (KPCuspLogShape.dimension F))
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val)) :=
      representative_smoothAt v _ (by
        rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact q.property)
    have hc : (fun y : HyperbolicChart.Space (KPCuspLogShape.dimension F) =>
        (v.val ∘ arch (KPCuspLogShape.dimension F))
          (real (KPCuspLogShape.dimension F)
            (KPArch.productAction (KPCuspLogShape.dimension F) g
              (arch (KPCuspLogShape.dimension F) y)))) =ᶠ[nhds
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val))]
        (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
          (v.val ∘ arch (KPCuspLogShape.dimension F)) y) := by
      have harch : ContinuousAt (arch (KPCuspLogShape.dimension F))
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val)) :=
        (smooth_arch _).continuous.continuousAt
      have hopen : {z : KPArch.Space (KPCuspLogShape.dimension F) |
          T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} ∈
          nhds (KPCuspCharts.toArch F q.val) :=
        (isOpen_lt continuous_const (smooth_mean _).continuous).mem_nhds (by
          show T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
            (KPCuspCharts.toArch F q.val)
          rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
          exact q.property)
      filter_upwards [harch.eventually hopen] with y hy
      have hys : KPArch.productAction (KPCuspLogShape.dimension F) g
          (arch (KPCuspLogShape.dimension F) y) =
          KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F)
            (arch (KPCuspLogShape.dimension F) y) := by
        rw [← hA, KPCuspSiegel.action_mk]
        rfl
      simp only [Function.comp_apply, arch_real]
      rw [hys]
      exact v.equivariant s (arch (KPCuspLogShape.dimension F) y) hy
    let u : Fin (KPCuspLogShape.dimension F) → ℂ :=
      fun i => (KPCusp.complexPlace F i).embedding ((D.ratio s : Fˣ) : F)
    have hu : ∀ i, u i ≠ 0 := fun i =>
      (map_ne_zero (KPCusp.complexPlace F i).embedding).mpr (Units.ne_zero _)
    have hz : ∀ i, g i 1 0 = 0 := by
      intro i
      change (KPCusp.complexPlace F i).embedding (A 1 0) = 0
      simp [hAz]
    have hr : ∀ i, g i 0 0 = u i * g i 1 1 := by
      intro i
      change (KPCusp.complexPlace F i).embedding (A 0 0) = _
      rw [D.ratioFormula s A hA hAz, map_mul]
      rfl
    have hkey := upper_equivariant_laplacian (KPCuspLogShape.dimension F) g u hu hz hr
      (v.val ∘ arch (KPCuspLogShape.dimension F))
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val))
      (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) hc hcont_q
      (by rw [arch_real, hs']; exact hcont_p)
    have hlap : v.laplacian p.val =
        (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.laplacian q.val := by
      have h := hkey
      rw [arch_real, hs'] at h
      simpa only [Representative.laplacian] using h
    have hsc : v.scalar p.val =
        (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar q.val := by
      have hq : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
          (KPCuspCharts.toArch F q.val) := by
        rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact q.property
      have he := v.equivariant s (KPCuspCharts.toArch F q.val) hq
      rw [hs] at he
      simpa only [Representative.scalar] using he
    have hcc : star (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
        (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', character_norm (ζ := ζ) (hζ := hζ) (ρ s)]
      norm_num
    calc (star (v.scalar p.val) * v.laplacian p.val).re
        = (star ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar q.val) *
            ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.laplacian q.val)).re := by
          rw [hsc, hlap]
      _ = (star (v.scalar q.val) * v.laplacian q.val).re := by
          congr 1
          calc star ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar q.val) *
                ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.laplacian q.val)
              = (star (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
                  (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ)) *
                  (star (v.scalar q.val) * v.laplacian q.val) := by
                rw [star_mul]
                ring
            _ = star (v.scalar q.val) * v.laplacian q.val := by rw [hcc, one_mul]

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end
