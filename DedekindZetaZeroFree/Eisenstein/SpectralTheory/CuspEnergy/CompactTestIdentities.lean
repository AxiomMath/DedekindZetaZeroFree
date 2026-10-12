module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialGreenIdentity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.MeanZeroCoercivity

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal
open Filter

namespace DedekindZetaZeroFree.KPCompactGreen
open KPMeanZeroWeightedEnergy

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
 def heightCLM (d : ℕ) : HyperbolicChart.Space d →L[ℝ] ℝ :=
  (d : ℝ)⁻¹ • ∑ i : Fin d, EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))
private theorem height_eq (d : ℕ) (x : HyperbolicChart.Space d) :
    KPCuspLogShape.meanHeight d (arch d x) = heightCLM d x := by
  simp [KPCuspLogShape.meanHeight, arch, heightCLM, Finset.sum_apply, div_eq_mul_inv, mul_comm]
private theorem height_vector (d : ℕ) (i : Fin d) (k : Fin 3) :
    heightCLM d (HyperbolicChart.coordinateVector d i k) =
      if k = 2 then (d : ℝ)⁻¹ else 0 := by
  by_cases hk : k = 2
  · subst k
    simp [heightCLM, HyperbolicChart.coordinateVector, Finset.sum_apply]
  · simp [heightCLM, HyperbolicChart.coordinateVector, Finset.sum_apply, hk, Ne.symm hk]
private theorem radial_derivative (d : ℕ) (η : ℝ → ℝ) (hη : Differentiable ℝ η)
    (x : HyperbolicChart.Space d) (i : Fin d) (k : Fin 3) :
    HyperbolicChart.coordinateDerivative d i k
      (fun q => (η (heightCLM d q) : ℂ)) x =
      ((deriv η (heightCLM d x) * (if k = 2 then (d : ℝ)⁻¹ else 0) : ℝ) : ℂ) := by
  have hh := Complex.ofRealCLM.hasFDerivAt.comp x
    ((hη (heightCLM d x)).hasDerivAt.comp_hasFDerivAt x (heightCLM d).hasFDerivAt)
  simpa [HyperbolicChart.coordinateDerivative, height_vector, ContinuousLinearMap.smul_apply,
    Function.comp_def, ← Complex.ofReal_mul]
    using congrArg (fun A : HyperbolicChart.Space d →L[ℝ] ℂ =>
      A (HyperbolicChart.coordinateVector d i k)) hh.fderiv
private theorem differential_mul_radial (d : ℕ) (η : ℝ → ℝ) (hη : Differentiable ℝ η)
    (f : HyperbolicChart.Space d → ℂ) (x : HyperbolicChart.Space d)
    (hf : DifferentiableAt ℝ f x) (i : Fin d) (k : Fin 3) :
    HyperbolicChart.differential d (fun q => (η (heightCLM d q) : ℂ) * f q) x i k =
      (η (heightCLM d x) : ℂ) * HyperbolicChart.differential d f x i k +
        (if k = 0 then ((deriv η (heightCLM d x) * (d : ℝ)⁻¹ : ℝ) : ℂ) * f x else 0) := by
  have hr : DifferentiableAt ℝ (fun q => (η (heightCLM d q) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x ((hη _).comp x (heightCLM d).differentiableAt)
  have hm (j : Fin 3) : HyperbolicChart.coordinateDerivative d i j
      (fun q => (η (heightCLM d q) : ℂ) * f q) x =
      (η (heightCLM d x) : ℂ) * HyperbolicChart.coordinateDerivative d i j f x +
      f x * HyperbolicChart.coordinateDerivative d i j (fun q => (η (heightCLM d q) : ℂ)) x := by
    simpa [HyperbolicChart.coordinateDerivative, Pi.mul_def] using
      congrArg (fun A : HyperbolicChart.Space d →L[ℝ] ℂ =>
        A (HyperbolicChart.coordinateVector d i j)) (hr.hasFDerivAt.mul hf.hasFDerivAt).fderiv
  fin_cases k <;> simp [HyperbolicChart.differential, hm, radial_derivative d η hη] <;> ring
private theorem ims_scalar (a b : ℝ) (u z : ℂ) :
    ‖(a : ℂ) * u + (b : ℂ) * z‖ ^ 2 =
      (star (((a^2 : ℝ) : ℂ) * u + ((2*a*b : ℝ) : ℂ) * z) * u).re +
        b^2 * ‖z‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring
private theorem ims_upstairs (d : ℕ) (hd : 0 < d) (η : ℝ → ℝ)
    (hη : Differentiable ℝ η) (f : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) (hf : DifferentiableAt ℝ f x) :
    (∑ i, ∑ k, ‖HyperbolicChart.differential d
      (fun q => (η (heightCLM d q) : ℂ) * f q) x i k‖^2) =
    (HyperbolicChart.pairing d
      (HyperbolicChart.differential d (fun q => ((η (heightCLM d q)^2 : ℝ) : ℂ) * f q) x)
      (HyperbolicChart.differential d f x)).re +
    (d : ℝ)⁻¹ * (deriv η (heightCLM d x)^2 * ‖f x‖^2) := by
  have hη2 : Differentiable ℝ (fun t => η t ^ 2) := hη.pow 2
  have hd2 (t : ℝ) : deriv (fun t => η t ^ 2) t = 2 * η t * deriv η t := by
    convert ((hη t).hasDerivAt.pow 2).deriv using 1 <;> simp [pow_succ, pow_zero, mul_assoc]
  have hi (i : Fin d) :
      (∑ k, ‖HyperbolicChart.differential d
        (fun q => (η (heightCLM d q) : ℂ) * f q) x i k‖^2) =
      (∑ k, (star (HyperbolicChart.differential d
        (fun q => ((η (heightCLM d q)^2 : ℝ) : ℂ) * f q) x i k) *
        HyperbolicChart.differential d f x i k).re) +
      (deriv η (heightCLM d x) * (d : ℝ)⁻¹)^2 * ‖f x‖^2 := by
    simp only [Fin.sum_univ_three, differential_mul_radial d η hη f x hf,
      differential_mul_radial d (fun t => η t^2) hη2 f x hf, hd2]
    simp only [Fin.reduceEq, ↓reduceIte, add_zero]
    have h0 := ims_scalar (η (heightCLM d x))
      (deriv η (heightCLM d x) * (d : ℝ)⁻¹) (HyperbolicChart.differential d f x i 0) (f x)
    have h1 := ims_scalar (η (heightCLM d x)) 0 (HyperbolicChart.differential d f x i 1) (f x)
    have h2 := ims_scalar (η (heightCLM d x)) 0 (HyperbolicChart.differential d f x i 2) (f x)
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, add_zero, zero_pow (by decide : 2 ≠ 0)] at h1 h2
    rw [h1, h2]
    have he : 2 * η (heightCLM d x) * deriv η (heightCLM d x) * (d : ℝ)⁻¹ =
        2 * η (heightCLM d x) * (deriv η (heightCLM d x) * (d : ℝ)⁻¹) := by ring
    rw [he, h0]
    ring
  unfold HyperbolicChart.pairing
  simp only [Complex.re_sum]
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  congr 1
  field_simp
private theorem continuous_height (d : ℕ) : Continuous (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  exact (continuous_finset_sum _ (fun i _ => (continuous_apply i).snd)).div_const _
private theorem cutoff_zero (d : ℕ) (η : ℝ → ℝ) (f : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) (hx : heightCLM d x ∉ tsupport η) :
    HyperbolicChart.differential d (fun q => (η (heightCLM d q) : ℂ) * f q) x = 0 := by
  have hz : (fun q => (η (heightCLM d q) : ℂ) * f q) =ᶠ[nhds x] 0 := by
    have hh := ((notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
      (heightCLM d).continuous.continuousAt)
    filter_upwards [hh] with q hq
    change η (heightCLM d q) = 0 at hq
    simp [hq]
  have hd := hz.fderiv_eq (𝕜 := ℝ)
  have hd0 : fderiv ℝ (0 : HyperbolicChart.Space d → ℂ) x = 0 :=
    congrFun fderiv_zero x
  rw [hd0] at hd
  funext i k
  fin_cases k <;> simp [HyperbolicChart.differential, HyperbolicChart.coordinateDerivative, hd]

theorem mean_height_cutoff_ims
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ}
    (hd : 0 < KPCuspLogShape.dimension F)
    {T : ℝ} (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) (p : KPCuspCharts.Coordinates F) :
    cutoffGradientSq v η p = weightedGreenDensity v η p +
      (KPCuspLogShape.dimension F : ℝ)⁻¹ *
        (deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) := by
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F p)
  have hx : arch d x = KPCuspCharts.toArch F p := arch_real d _
  have ht : heightCLM d x = p.2 := by
    rw [← height_eq, hx, KPCuspCharts.toArch_meanHeight F hd]
  have hu : cutoffUpstairs v η = fun q => (η (heightCLM d q) : ℂ) * (v.val ∘ arch d) q := by
    funext q
    simp [cutoffUpstairs, height_eq, d]
  have hu2 : cutoffUpstairs v (fun t => η t^2) =
      fun q => ((η (heightCLM d q)^2 : ℝ) : ℂ) * (v.val ∘ arch d) q := by
    funext q
    simp [cutoffUpstairs, height_eq, d]
  by_cases hp : p.2 ∈ tsupport η
  · have htx : T < KPCuspLogShape.meanHeight d (arch d x) := by
      rw [hx, KPCuspCharts.toArch_meanHeight F hd]
      exact hη.2.2 hp
    have hopen : IsOpen {z : KPArch.Space d | T < KPCuspLogShape.meanHeight d z} :=
      isOpen_lt continuous_const (continuous_height d)
    have hv : DifferentiableAt ℝ v.val (arch d x) :=
      (v.smooth.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds htx)
    have hf : DifferentiableAt ℝ (v.val ∘ arch d) x :=
      hv.comp x ((smooth_arch d).differentiable (by simp) x)
    have hi := ims_upstairs d hd η (hη.1.differentiable (by simp)) (v.val ∘ arch d) x hf
    simpa only [cutoffGradientSq, weightedGreenDensity, hu, hu2, ht,
      Representative.scalar, Function.comp_apply, hx] using hi
  · have hnx : heightCLM d x ∉ tsupport η := by simpa only [ht] using hp
    have hnx2 : heightCLM d x ∉ tsupport (fun t => η t^2) := by
      intro hh
      exact hnx ((tsupport_comp_subset (f := η) (g := fun t : ℝ => t^2) (by simp)) hh)
    have hz := cutoff_zero d η (v.val ∘ arch d) x hnx
    have hz2 := cutoff_zero d (fun t => η t^2) (v.val ∘ arch d) x hnx2
    simp only [cutoffGradientSq, weightedGreenDensity, hu, hu2]
    change (∑ i, ∑ k, ‖HyperbolicChart.differential d
      (fun q => (η (heightCLM d q) : ℂ) * (v.val ∘ arch d) q) x i k‖ ^ 2) = _
    rw [hz, hz2]
    simp [HyperbolicChart.pairing, deriv_of_notMem_tsupport hp]

end DedekindZetaZeroFree.KPCompactGreen

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPCompactGreen
open KPMeanZeroWeightedEnergy

private theorem arch_real_for_compactEnergy (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  funext i
  apply Prod.ext
  · apply Complex.ext <;> simp [arch, real]
  · simp [arch, real]
private theorem contDiff_arch_for_compactEnergy (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff (n := (⊤ : ℕ∞))
    have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff (n := (⊤ : ℕ∞))
    have hh := (Complex.ofRealCLM.contDiff.comp h0).add
      ((Complex.ofRealCLM.contDiff.comp h1).mul contDiff_const (g := fun _ => Complex.I))
    convert hh using 1
    funext x
    apply Complex.ext <;> simp [arch, PiLp.proj_apply]
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff
private theorem smooth_mean (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact (contDiff_snd.comp (contDiff_apply ℝ _ i))
private theorem mean_deriv (d : ℕ) (x : HyperbolicChart.Space d) :
    HasFDerivAt (fun q : HyperbolicChart.Space d => KPCuspLogShape.meanHeight d (arch d q))
      ((d : ℝ)⁻¹ • ∑ i : Fin d, EuclideanSpace.proj (𝕜 := ℝ) (i,(2 : Fin 3))) x := by
  have hs : HasFDerivAt (fun q : HyperbolicChart.Space d => ∑ i : Fin d, q (i,2))
      (∑ i : Fin d, EuclideanSpace.proj (𝕜 := ℝ) (i,(2 : Fin 3))) x := by
    apply HasFDerivAt.fun_sum
    intro j hj
    exact (EuclideanSpace.proj (𝕜 := ℝ) (j,(2 : Fin 3))).hasFDerivAt
  simpa [KPCuspLogShape.meanHeight, arch, div_eq_mul_inv, mul_comm] using hs.const_mul (d : ℝ)⁻¹
private theorem cutoff_deriv (d : ℕ) (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : HyperbolicChart.Space d) (i : Fin d) (k : Fin 3) :
    HyperbolicChart.coordinateDerivative d i k
      (fun q => (η (KPCuspLogShape.meanHeight d (arch d q)) : ℂ)) x =
        if k = 2 then (deriv η (KPCuspLogShape.meanHeight d (arch d x)) / d : ℝ) else 0 := by
  have hh := Complex.ofRealCLM.hasFDerivAt.comp x
    (((hη.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x (mean_deriv d x))
  have he := congrArg (fun A : HyperbolicChart.Space d →L[ℝ] ℂ =>
    A (HyperbolicChart.coordinateVector d i k)) hh.fderiv
  by_cases hk : k = 2
  · subst k
    simpa [HyperbolicChart.coordinateDerivative, HyperbolicChart.coordinateVector,
      PiLp.proj_apply, Function.comp_def, Finset.sum_apply, Finset.sum_ite,
      div_eq_mul_inv, mul_comm] using he
  · simpa [HyperbolicChart.coordinateDerivative, HyperbolicChart.coordinateVector,
      PiLp.proj_apply, Function.comp_def, Finset.sum_apply, Finset.sum_ite,
      hk, Ne.symm hk] using he
private theorem differential_mul_cutoff (d : ℕ) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (f : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) (hf : DifferentiableAt ℝ f x) (i : Fin d) (k : Fin 3) :
    HyperbolicChart.differential d (fun q => (η (KPCuspLogShape.meanHeight d (arch d q)) : ℂ) * f q) x i k =
      (η (KPCuspLogShape.meanHeight d (arch d x)) : ℂ) * HyperbolicChart.differential d f x i k +
      if k = 0 then (deriv η (KPCuspLogShape.meanHeight d (arch d x)) / d : ℝ) * f x else 0 := by
  have ha : DifferentiableAt ℝ (fun q : HyperbolicChart.Space d =>
      (η (KPCuspLogShape.meanHeight d (arch d q)) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((hη.differentiable (by simp) _).comp x (mean_deriv d x).differentiableAt)
  have hm (j : Fin 3) : HyperbolicChart.coordinateDerivative d i j
      (fun q => (η (KPCuspLogShape.meanHeight d (arch d q)) : ℂ) * f q) x =
        (η (KPCuspLogShape.meanHeight d (arch d x)) : ℂ) * HyperbolicChart.coordinateDerivative d i j f x +
        f x * (if j = 2 then (deriv η (KPCuspLogShape.meanHeight d (arch d x)) / d : ℝ) else 0) := by
    have he := congrArg (fun A : HyperbolicChart.Space d →L[ℝ] ℂ => A (HyperbolicChart.coordinateVector d i j))
        (ha.hasFDerivAt.mul hf.hasFDerivAt).fderiv
    change HyperbolicChart.coordinateDerivative d i j _ x =
      (η (KPCuspLogShape.meanHeight d (arch d x)) : ℂ) * HyperbolicChart.coordinateDerivative d i j f x +
        f x * HyperbolicChart.coordinateDerivative d i j _ x at he
    rw [cutoff_deriv d η hη x i j] at he
    exact he
  fin_cases k
  · simpa [HyperbolicChart.differential, mul_comm] using hm 2
  · simp [HyperbolicChart.differential, hm, mul_left_comm]
  · simp [HyperbolicChart.differential, hm, mul_left_comm]
private theorem norm_reverse (a b : ℂ) : ‖a‖ ^ 2 ≤ 2 * ‖a+b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hh := parallelogram_law_with_norm ℂ (a+b) b
  have hn := sq_nonneg ‖a+b+b‖
  have he : a + b - b = a := by ring
  rw [he] at hh
  nlinarith
private theorem norm_real_mul_sq (a : ℝ) (b : ℂ) : ‖(a : ℂ) * b‖ ^ 2 = a ^ 2 * ‖b‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem mean_height_reverse_cutoff_bound
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ}
    (hd : 0 < KPCuspLogShape.dimension F)
    {T : ℝ} (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) (p : KPCuspCharts.Coordinates F) :
    η p.2 ^ 2 * v.gradientSq p ≤
      2 * cutoffGradientSq v η p +
        2 * (KPCuspLogShape.dimension F : ℝ)⁻¹ *
          (deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) := by
  by_cases hz : η p.2 = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul]
    apply add_nonneg
    · apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun k hk => sq_nonneg _))
    · positivity
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F p)
  have hx : arch d x = KPCuspCharts.toArch F p := arch_real_for_compactEnergy _ _
  have ht : KPCuspLogShape.meanHeight d (arch d x) = p.2 := by
    rw [hx]; exact KPCuspCharts.toArch_meanHeight F hd p
  have hp : p.2 ∈ Set.Ioi T := hη.2.2 (subset_tsupport η (by exact hz))
  have hs : {z : KPArch.Space d | T < KPCuspLogShape.meanHeight d z} ∈
      nhds (arch d x) :=
    (isOpen_lt continuous_const (smooth_mean d).continuous).mem_nhds (by simpa [ht] using hp)
  have hv : DifferentiableAt ℝ (v.val ∘ arch d) x :=
    ((v.smooth.differentiableOn (by simp)).differentiableAt hs).comp x
      ((contDiff_arch_for_compactEnergy d).differentiable (by simp) x)
  have hprod (i : Fin d) (k : Fin 3) := differential_mul_cutoff d η hη.1 (v.val ∘ arch d) x hv i k
  simp only [ht, Function.comp_apply] at hprod
  simp only [hx] at hprod
  let w := HyperbolicChart.differential d (v.val ∘ arch d) x
  let c := HyperbolicChart.differential d (cutoffUpstairs v η) x
  have hi (i : Fin d) (k : Fin 3) :
      η p.2 ^ 2 * ‖w i k‖ ^ 2 ≤ 2 * ‖c i k‖ ^ 2 +
        2 * (if k = 0 then (deriv η p.2 / d) ^ 2 * ‖v.scalar p‖ ^ 2 else 0) := by
    have hn := norm_reverse ((η p.2 : ℂ) * w i k)
      (if k = 0 then (deriv η p.2 / d : ℝ) * v.scalar p else 0)
    have he : c i k = (η p.2 : ℂ) * w i k +
        if k = 0 then (deriv η p.2 / d : ℝ) * v.scalar p else 0 := by
      exact hprod i k
    rw [← he, norm_real_mul_sq] at hn
    by_cases hk : k = 0
    · simp only [hk, if_true] at hn ⊢
      rw [norm_real_mul_sq] at hn
      exact hn
    · simpa only [hk, if_false, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hn
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hi i k))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hn : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have herr : (∑ i : Fin d, ∑ k : Fin 3,
      if k = 0 then (deriv η p.2 / d) ^ 2 * ‖v.scalar p‖ ^ 2 else 0) =
      (d : ℝ)⁻¹ * (deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  rw [herr] at hsum
  simpa only [Representative.gradientSq, cutoffGradientSq, d, x, w, c, mul_assoc] using hsum

end DedekindZetaZeroFree.KPCompactGreen

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

theorem compact_green_specialization
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) :
    (Integrable (fun p => η p.2 ^ 2 * v.gradientSq p) (chartMeasure G) ∧
      Integrable (fun p => deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) (chartMeasure G) ∧
      Integrable (fun p => Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2)
        (chartMeasure G) ∧
      Integrable (fun p => η p.2 ^ 2 *
        (star (v.scalar p) * v.laplacian p).re) (chartMeasure G)) ∧
    (∃ q : ℝ, 0 ≤ q ∧
      q = (∫ p, η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re ∂chartMeasure G) +
        (KPCuspLogShape.dimension F : ℝ)⁻¹ *
          (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂chartMeasure G) ∧
      (∫ p, η p.2 ^ 2 * v.gradientSq p ∂chartMeasure G) ≤
        2 * q + 2 * (KPCuspLogShape.dimension F : ℝ)⁻¹ *
          (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂chartMeasure G)) := by
  have hi := KPCompactGreen.compact_radial_densities_integrable G v η hη
  rcases hi with ⟨hgrad, herror, hpotential, hlap, hcutoff, hpair⟩
  refine ⟨⟨hgrad, herror, hpotential, hlap⟩, ?_⟩
  refine ⟨∫ p, KPCompactGreen.cutoffGradientSq v η p ∂chartMeasure G, ?_, ?_, ?_⟩
  · apply integral_nonneg
    intro p
    unfold KPCompactGreen.cutoffGradientSq
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  · calc
      (∫ p, KPCompactGreen.cutoffGradientSq v η p ∂chartMeasure G) =
          ∫ p, KPCompactGreen.weightedGreenDensity v η p +
            (KPCuspLogShape.dimension F : ℝ)⁻¹ *
              (deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) ∂chartMeasure G := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (KPCompactGreen.mean_height_cutoff_ims G.positive_dimension v η hη)
      _ = (∫ p, KPCompactGreen.weightedGreenDensity v η p ∂chartMeasure G) +
          (KPCuspLogShape.dimension F : ℝ)⁻¹ *
            (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂chartMeasure G) := by
        rw [integral_add hpair (herror.const_mul _), integral_const_mul]
      _ = _ := by
        rw [KPCompactGreen.compact_radial_green_descent G v η hη]
  · have hbound := integral_mono hgrad
        ((hcutoff.const_mul 2).add
          (herror.const_mul (2 * (KPCuspLogShape.dimension F : ℝ)⁻¹)))
        (KPCompactGreen.mean_height_reverse_cutoff_bound G.positive_dimension v η hη)
    simpa only [Pi.add_apply, integral_add (hcutoff.const_mul 2)
      (herror.const_mul (2 * (KPCuspLogShape.dimension F : ℝ)⁻¹)),
      integral_const_mul] using hbound

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

theorem kernel_torus_haar_specialization
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) :
    ∃ μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ),
      μ.IsAddHaarMeasure ∧ IsProbabilityMeasure μ ∧
      ∀ {T : ℝ} (v : Representative ζ hζ S ρ V T) b t,
        Integrable (v.torusSlice G H b t) μ := by
  letI := H.compact
  obtain ⟨hd, _⟩ := G.lattice
  have hle : KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ) ≤
      KPCuspCharts.translationLattice F D.L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, H.kernel_le hx, rfl⟩
  letI : DiscreteTopology (KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ)) :=
    DiscreteTopology.of_subset hd hle
  letI : IsClosed (KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ) : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  let K : TopologicalSpace.PositiveCompacts (KPCuspGenuineMonodromy.KernelTorus S D ρ) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  refine ⟨Measure.addHaarMeasure K, inferInstance, ⟨Measure.addHaarMeasure_self⟩, ?_⟩
  intro T v b t
  have hc : Continuous (v.torusSlice G H b t) := by
    apply (QuotientAddGroup.isQuotientMap_mk
      (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ))).continuous_iff.mpr
    have he : (v.torusSlice G H b t) ∘ QuotientAddGroup.mk =
        fun y => v.val (KPCuspCharts.toArch F ((y,b),t.val)) := by
      funext y
      have h := H.realization_formula (H.realization.symm (v.horizontalSlice G b t)) y
      simpa only [Function.comp_apply, Representative.torusSlice, LinearEquiv.apply_symm_apply,
        Representative.horizontalSlice, Representative.scalar] using h.symm
    rw [he]
    apply v.smooth.continuousOn.comp_continuous
    · unfold KPCuspCharts.toArch
      fun_prop
    · intro y
      change T < KPCuspLogShape.meanHeight _ _
      rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
      exact t.property
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

theorem actual_structural_inputs
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
    {g : KPFiniteCuspAtlas.FiniteCover F ζ hζ}
    {line : KPCuspGenuineMonodromy.LineOutput F ζ hζ U g}
    (A : KPFiniteCuspAtlas.ComponentAtlas F ζ hζ hF U g line)
    (a : Fin A.cuspCount) :
    Nonempty (StructuralInputs ζ hζ _ (A.parabolic a)
      (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g)
        (A.cusp a) (A.representative a)))
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
      (A.geometry a) (A.monodromy a)) := by
  obtain ⟨μ, hμ, hprob, hslice⟩ :=
    kernel_torus_haar_specialization (A.geometry a) (A.monodromy a)
  obtain ⟨c, hc, hgap⟩ := mean_zero_gap_specialization A a μ hμ hprob
  exact ⟨{
    fiberMeasure := μ
    fiberHaar := hμ
    fiberProbability := hprob
    slice_integrable := hslice
    compact_integrable := fun v η hη =>
      (compact_green_specialization (A.geometry a) v η hη).1
    cutoffEnergy := fun v η hη =>
      (compact_green_specialization (A.geometry a) v η hη).2
    potential := c
    positive_potential := hc
    meanZero_coercivity := hgap }⟩

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

end

end
