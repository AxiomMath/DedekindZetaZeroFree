module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.RadialDisintegration

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped Classical

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDescent
open KPMeanZeroWeightedEnergy

theorem half_norm_sq_high_descent
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (v : Representative ζ hζ S ρ V T) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ‖v.val z‖ ^ 2 / 2)
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} ∧
    (∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      ‖v.val (KPCuspCharts.toArch F p.val)‖ ^ 2 / 2 =
        ‖v.val (KPCuspCharts.toArch F q.val)‖ ^ 2 / 2) := by
  constructor
  · simpa using (v.smooth.norm_sq (𝕜 := ℂ)).div_const 2
  · intro p q hrel
    have h := scalar_norm_high_orbit_invariant G v hrel
    simp only [Representative.scalar] at h ⊢
    rw [h]

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDescent

end

end

section

noncomputable section
open MeasureTheory
open Filter

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDescent

theorem integral_weighted_radial_divergence_eq_zero
    (b : ℝ) (J : ℝ → ℝ) (hJ : ContDiff ℝ (⊤ : ℕ∞) J)
    (hcompact : HasCompactSupport J) :
    (∫ t, (-deriv J t + b * J t)
      ∂(volume.withDensity (fun t => ENNReal.ofReal (Real.exp (-b * t))))) = 0 := by

  have hFcd : ContDiff ℝ (⊤ : ℕ∞) (fun t => -(J t * Real.exp (-b * t))) := by
    fun_prop
  have hFcomp : HasCompactSupport (fun t => -(J t * Real.exp (-b * t))) := by
    have h : HasCompactSupport (fun t => J t * Real.exp (-b * t)) := hcompact.mul_right
    exact h.neg
  have hderiv : ∀ t, HasDerivAt (fun t => -(J t * Real.exp (-b * t)))
      (Real.exp (-b * t) * (-deriv J t + b * J t)) t := by
    intro t
    have hJt : HasDerivAt J (deriv J t) t := (hJ.differentiable (by simp) t).hasDerivAt
    have he : HasDerivAt (fun s => Real.exp (-b * s)) (Real.exp (-b * t) * (-b)) t := by
      have h0 : HasDerivAt (fun s : ℝ => -b * s) (-b) t := by
        simpa using (hasDerivAt_id t).const_mul (-b)
      simpa using h0.exp
    have h := (hJt.mul he).neg
    convert h using 1
    ring
  have hderivF : ∀ t, HasDerivAt (fun t => -(J t * Real.exp (-b * t)))
      (deriv (fun t => -(J t * Real.exp (-b * t))) t) t :=
    fun t => (hFcd.differentiable (by simp) t).hasDerivAt
  have hIntF : Integrable (fun t => -(J t * Real.exp (-b * t))) :=
    hFcd.continuous.integrable_of_hasCompactSupport hFcomp
  have hIntdF : Integrable (deriv (fun t => -(J t * Real.exp (-b * t)))) :=
    (hFcd.continuous_deriv (by simp)).integrable_of_hasCompactSupport hFcomp.deriv
  have hzero : ∫ t, deriv (fun t => -(J t * Real.exp (-b * t))) t ∂volume = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hderivF hIntdF hIntF
  have htoReal : ∀ t, (ENNReal.ofReal (Real.exp (-b * t))).toReal = Real.exp (-b * t) :=
    fun t => ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  simp only [htoReal, smul_eq_mul]
  rw [show (∫ t, Real.exp (-b * t) * (-deriv J t + b * J t) ∂volume)
      = ∫ t, deriv (fun t => -(J t * Real.exp (-b * t))) t ∂volume from
    integral_congr_ae (Eventually.of_forall fun t => ((hderiv t).deriv).symm)]
  exact hzero

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDescent

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPCompactGreen
open KPMeanZeroWeightedEnergy

namespace GreenFlux
open HyperbolicChart

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

private theorem smooth_height (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Space d => KPCuspLogShape.meanHeight d (arch d x)) := by
  unfold KPCuspLogShape.meanHeight arch
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem continuous_height (d : ℕ) : Continuous (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  exact (continuous_finset_sum _ (fun i _ => (continuous_apply i).snd)).div_const _

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {ρ : S →* rootsOfUnity 3 F}
    {V : Submodule ℂ ℂ} {T : ℝ}

private theorem representative_smoothAt (v : Representative ζ hζ S ρ V T)
    (x : Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (v.val ∘ arch (KPCuspLogShape.dimension F)) x := by
  have hopen : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
    isOpen_lt continuous_const (continuous_height _)
  exact (v.smooth.contDiffAt (hopen.mem_nhds hx)).comp x (smooth_arch _).contDiffAt

def radialFlux (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) :
    Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F) :=
  fun x i k => star (cutoffUpstairs v (fun t => η t ^ 2) x) *
    differential (KPCuspLogShape.dimension F) (v.val ∘ arch (KPCuspLogShape.dimension F)) x i k

private theorem cutoff_eventually_zero (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ) (x : Space (KPCuspLogShape.dimension F))
    (hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x) ∉ tsupport η) :
    cutoffUpstairs v (fun t => η t ^ 2) =ᶠ[nhds x] 0 := by
  have hh := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
    (smooth_height _).continuous.continuousAt
  filter_upwards [hh] with q hq
  change η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
    (arch (KPCuspLogShape.dimension F) q)) = 0 at hq
  simp [cutoffUpstairs, hq]

private theorem flux_eventually_zero (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ) (x : Space (KPCuspLogShape.dimension F))
    (hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x) ∉ tsupport η) :
    radialFlux v η =ᶠ[nhds x] 0 := by
  filter_upwards [cutoff_eventually_zero v η x hx] with q hq
  funext i k
  simp [radialFlux, hq]

theorem radialFlux_smooth (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) :
    ContDiff ℝ (⊤ : ℕ∞) (radialFlux v η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x) ∈ tsupport η
  · have hv := representative_smoothAt v x (hη.2.2 hx)
    have hc : ContDiffAt ℝ (⊤ : ℕ∞) (cutoffUpstairs v (fun t => η t^2)) x :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((hη.1.pow 2).contDiffAt.comp x (smooth_height _).contDiffAt)).mul hv
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro k
    exact ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp x hc).mul
      (differential_smoothAt _ _ x hv i k)
  · exact contDiffAt_const.congr_of_eventuallyEq (flux_eventually_zero v η x hx)

theorem compact_radial_green_defect
    (hd : 0 < KPCuspLogShape.dimension F)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) (p : KPCuspCharts.Coordinates F) :
    weightedGreenDensity v η p -
      η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re =
    -(codifferential (KPCuspLogShape.dimension F) (radialFlux v η)
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re := by
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F p)
  have hx : arch d x = KPCuspCharts.toArch F p := arch_real d _
  have ht : KPCuspLogShape.meanHeight d (arch d x) = p.2 := by
    rw [hx, KPCuspCharts.toArch_meanHeight F hd]
  by_cases hp : p.2 ∈ tsupport η
  · have hv := representative_smoothAt v x (by rw [ht]; exact hη.2.2 hp)
    have hc : ContDiffAt ℝ (⊤ : ℕ∞) (cutoffUpstairs v (fun t => η t^2)) x :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((hη.1.pow 2).contDiffAt.comp x (smooth_height _).contDiffAt)).mul hv
    have hf := codifferential_star_mul d _ (differential d (v.val ∘ arch d)) x
      (hc.differentiableAt (by simp))
      (fun i k => (differential_smoothAt d _ x hv i k).differentiableAt (by simp))
    rw [codifferential_differential_at d _ x hv] at hf
    change codifferential d (radialFlux v η) x = _ at hf
    have hcval : cutoffUpstairs v (fun t => η t^2) x =
        (η p.2 ^ 2 : ℝ) * v.scalar p := by
      change ((η (KPCuspLogShape.meanHeight d (arch d x)) ^ 2 : ℝ) : ℂ) *
        v.val (arch d x) = _
      rw [ht, hx]
      rfl
    rw [hcval, star_mul] at hf
    have hstar : star ((η p.2 ^ 2 : ℝ) : ℂ) = ((η p.2 ^ 2 : ℝ) : ℂ) := by simp
    rw [hstar, mul_assoc] at hf
    have hf_re := congrArg Complex.re hf
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] at hf_re
    change _ = -(codifferential d (radialFlux v η) x).re
    dsimp only [weightedGreenDensity, Representative.laplacian]
    simp only [Complex.mul_re]
    linear_combination hf_re
  · have hp' : KPCuspLogShape.meanHeight d (arch d x) ∉ tsupport η := by
      simpa only [ht] using hp
    have hc := cutoff_eventually_zero v η x hp'
    have hf := flux_eventually_zero v η x hp'
    have hd0 : differential d (cutoffUpstairs v (fun t => η t^2)) x = 0 := by
      have hh := hc.fderiv_eq (𝕜 := ℝ)
      have hz : fderiv ℝ (0 : Space d → ℂ) x = 0 := congrFun fderiv_zero x
      rw [hz] at hh
      funext i k
      fin_cases k <;> simp [differential, coordinateDerivative, hh]
    have hδ : codifferential d (radialFlux v η) x = 0 := by
      have hh (i : Fin d) (k : Fin 3) :
          (fun q => radialFlux v η q i k) =ᶠ[nhds x] 0 := by
        filter_upwards [hf] with q hq
        change radialFlux v η q = 0 at hq
        rw [hq]
        rfl
      have hder (i : Fin d) (j k : Fin 3) :
          coordinateDerivative d i j (fun q => radialFlux v η q i k) x = 0 := by
        have he := (hh i k).fderiv_eq (𝕜 := ℝ)
        have hz : fderiv ℝ (0 : Space d → ℂ) x = 0 := congrFun fderiv_zero x
        rw [hz] at he
        unfold coordinateDerivative
        rw [he]
        rfl
      simp [codifferential, hder, hf.eq_of_nhds]
    have hzero : η p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
    dsimp only [weightedGreenDensity]
    change _ = -(codifferential d (radialFlux v η) x).re
    rw [hd0, hδ, hzero]
    simp [pairing]

variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {D : KPCuspCharts.ParabolicData F S}

theorem compact_radial_green_integral_defect
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) :
    (∫ p, weightedGreenDensity v η p ∂KPMeanZeroWeightedEnergy.chartMeasure G) -
      (∫ p, η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re
        ∂KPMeanZeroWeightedEnergy.chartMeasure G) =
    -(∫ p : KPCuspCharts.Coordinates F,
      (codifferential (KPCuspLogShape.dimension F) (radialFlux v η)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re
      ∂KPMeanZeroWeightedEnergy.chartMeasure G) := by
  obtain ⟨_, _, _, hL, _, hGreen⟩ := compact_radial_densities_integrable G v η hη
  rw [← integral_sub hGreen hL, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (compact_radial_green_defect G.positive_dimension v η hη)

theorem coordinateDerivative_half_norm_sq (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : DifferentiableAt ℝ g x) (i : Fin d) (k : Fin 3) :
    coordinateDerivative d i k (fun q => ((‖g q‖ ^ 2 / 2 : ℝ) : ℂ)) x =
      ((star (g x) * coordinateDerivative d i k g x).re : ℂ) := by
  have hh := Complex.ofRealCLM.hasFDerivAt.comp x (hg.hasFDerivAt.norm_sq.mul_const (2 : ℝ)⁻¹)
  have he := congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k)) hh.fderiv
  simpa [coordinateDerivative, Function.comp_def, ContinuousLinearMap.comp_apply,
    RCLike.inner_apply, Complex.star_def, div_eq_mul_inv, mul_comm] using he

theorem differential_half_norm_sq (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : DifferentiableAt ℝ g x) (i : Fin d) (k : Fin 3) :
    differential d (fun q => ((‖g q‖ ^ 2 / 2 : ℝ) : ℂ)) x i k =
      ((star (g x) * differential d g x i k).re : ℂ) := by
  have hexp (j : Fin 3) :
      (Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i j
        (fun q => ((‖g q‖ ^ 2 / 2 : ℝ) : ℂ)) x =
      ((star (g x) * ((Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i j g x)).re : ℂ) := by
    rw [coordinateDerivative_half_norm_sq d g x hg]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero, ← Complex.ofReal_mul]
    congr 1
    ring
  fin_cases k
  · exact coordinateDerivative_half_norm_sq d g x hg i 2
  · exact hexp 0
  · exact hexp 1

theorem coordinateDerivative_realPart (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : DifferentiableAt ℝ g x) (i : Fin d) (k : Fin 3) :
    coordinateDerivative d i k (fun q => ((g q).re : ℂ)) x =
      ((coordinateDerivative d i k g x).re : ℂ) := by
  have hh := Complex.ofRealCLM.hasFDerivAt.comp x
    (Complex.reCLM.hasFDerivAt.comp x hg.hasFDerivAt)
  exact congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k)) hh.fderiv

theorem codifferential_realPart (d : ℕ) (W : Space d → Cotangent d) (x : Space d)
    (hW : ∀ i k, DifferentiableAt ℝ (fun q => W q i k) x) :
    codifferential d (fun q i k => ((W q i k).re : ℂ)) x =
      ((codifferential d W x).re : ℂ) := by
  simp only [codifferential, coordinateDerivative_realPart d _ x (hW _ _)]
  rw [show (∑ i, (-coordinateDerivative d i 2 (fun q => W q i 0) x + 2 * W x i 0 -
      (Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i 0 (fun q => W q i 1) x -
      (Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i 1 (fun q => W q i 2) x)).re =
      ∑ i, (-coordinateDerivative d i 2 (fun q => W q i 0) x + 2 * W x i 0 -
      (Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i 0 (fun q => W q i 1) x -
      (Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i 1 (fun q => W q i 2) x).re by
      exact map_sum Complex.reAddGroupHom _ _]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

def scalarRadialFlux (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) :
    Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F) :=
  fun x i k => ((η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) ^ 2 : ℝ) : ℂ) *
    differential (KPCuspLogShape.dimension F)
      (fun q => ((‖v.val (arch (KPCuspLogShape.dimension F) q)‖ ^ 2 / 2 : ℝ) : ℂ)) x i k

theorem scalarRadialFlux_eq_realPart (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) :
    scalarRadialFlux v η = fun x i k => ((radialFlux v η x i k).re : ℂ) := by
  funext x i k
  let d := KPCuspLogShape.dimension F
  let t := KPCuspLogShape.meanHeight d (arch d x)
  by_cases hz : η t = 0
  · have hz' : η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) x)) = 0 := hz
    simp [scalarRadialFlux, radialFlux, cutoffUpstairs, hz']
  · have ht : T < t := hη.2.2 (subset_tsupport η hz)
    have hg : DifferentiableAt ℝ (v.val ∘ arch d) x :=
      (representative_smoothAt v x ht).differentiableAt (by simp)
    change ((η t ^ 2 : ℝ) : ℂ) * differential d
        (fun q => ((‖(v.val ∘ arch d) q‖ ^ 2 / 2 : ℝ) : ℂ)) x i k = _
    rw [differential_half_norm_sq d _ x hg]
    simp only [radialFlux, cutoffUpstairs, star_mul, Complex.star_def, Complex.conj_ofReal,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    dsimp only [d, t, Function.comp_def]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    push_cast
    ring

theorem scalarRadialFlux_codifferential (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) (x : Space (KPCuspLogShape.dimension F)) :
    codifferential (KPCuspLogShape.dimension F) (scalarRadialFlux v η) x =
      ((codifferential (KPCuspLogShape.dimension F) (radialFlux v η) x).re : ℂ) := by
  rw [scalarRadialFlux_eq_realPart v η hη]
  apply codifferential_realPart
  intro i k
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun q => radialFlux v η q i k) :=
    contDiff_pi.mp (contDiff_pi.mp (radialFlux_smooth v η hη) i) k
  exact hs.contDiffAt.differentiableAt (by simp)

theorem compact_radial_scalar_flux_criterion
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) (hη : CompactRadialTest T η) :
    (∫ p, weightedGreenDensity v η p ∂KPMeanZeroWeightedEnergy.chartMeasure G) =
      (∫ p, η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re
        ∂KPMeanZeroWeightedEnergy.chartMeasure G) ↔
    (∫ p : KPCuspCharts.Coordinates F,
      (codifferential (KPCuspLogShape.dimension F) (scalarRadialFlux v η)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re
      ∂KPMeanZeroWeightedEnergy.chartMeasure G) = 0 := by
  have he := compact_radial_green_integral_defect G v η hη
  have hf : (∫ p : KPCuspCharts.Coordinates F,
      (codifferential (KPCuspLogShape.dimension F) (scalarRadialFlux v η)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re
      ∂KPMeanZeroWeightedEnergy.chartMeasure G) =
      ∫ p : KPCuspCharts.Coordinates F,
      (codifferential (KPCuspLogShape.dimension F) (radialFlux v η)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re
      ∂KPMeanZeroWeightedEnergy.chartMeasure G := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => by
      dsimp only
      rw [scalarRadialFlux_codifferential v η hη]
      rfl)
  rw [hf]
  constructor
  · intro h
    rw [h, sub_self] at he
    exact neg_eq_zero.mp he.symm
  · intro h
    rw [h, neg_zero] at he
    exact sub_eq_zero.mp he

end GreenFlux

theorem compact_radial_green_descent
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) :
    (∫ p, weightedGreenDensity v η p ∂chartMeasure G) =
      ∫ p, η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re ∂chartMeasure G := by
  apply (GreenFlux.compact_radial_scalar_flux_criterion G v η hη).mpr
  obtain ⟨hu, hinv⟩ := ScalarFluxDescent.half_norm_sq_high_descent G v
  have hweight : CompactRadialTest T (fun t => η t ^ 2) := by
    refine ⟨hη.1.pow 2, ?_, ?_⟩
    · apply hη.2.1.mono
      intro t ht
      change η t ^ 2 ≠ 0 at ht
      change η t ≠ 0
      exact fun hz => ht (by simp [hz])
    · apply Set.Subset.trans _ hη.2.2
      apply closure_mono
      intro t ht
      change η t ^ 2 ≠ 0 at ht
      change η t ≠ 0
      exact fun hz => ht (by simp [hz])
  obtain ⟨hJ, hcJ, hdiv⟩ := ScalarFluxDescent.scalar_flux_radial_disintegration G
    (fun z => ‖v.val z‖ ^ 2 / 2) hu hinv (fun t => η t ^ 2) hweight
  change (∫ p : KPCuspCharts.Coordinates F,
    (HyperbolicChart.codifferential (KPCuspLogShape.dimension F) (GreenFlux.scalarRadialFlux v η)
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re
    ∂chartMeasure G) = _ at hdiv
  rw [hdiv]
  have hz := ScalarFluxDescent.integral_weighted_radial_divergence_eq_zero
    (2 * (KPCuspLogShape.dimension F : ℝ))
    (ScalarFluxDescent.radialMarginal G (fun x i k =>
      ((η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) x)) ^ 2 : ℝ) : ℂ) *
      HyperbolicChart.differential (KPCuspLogShape.dimension F)
        (fun q => ((‖v.val (arch (KPCuspLogShape.dimension F) q)‖ ^ 2 / 2 : ℝ) : ℂ)) x i k))
    hJ hcJ
  simpa only [KPCuspCharts.radialMeasure, neg_mul] using hz

end DedekindZetaZeroFree.KPCompactGreen

end

end
