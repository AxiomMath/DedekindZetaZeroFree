module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.ZonalRotationCommutation
public import DedekindZetaZeroFree.MeasureTheory.Sphere.UniformProjection
public import DedekindZetaZeroFree.HarmonicAnalysis.SphericalHarmonics.FischerSpanning

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open KPCplxIntertwinerEigenvalues
open scoped BigOperators

noncomputable def polynomialSphere (p : MvPolynomial (Fin 3) ℂ) (x : Sphere) : ℂ :=
  MvPolynomial.eval (fun i => ((x : Ambient) i : ℂ)) p

theorem homogeneous_eval_scale {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ}
    (hp : p.IsHomogeneous ℓ) (t : ℂ) (x : Fin 3 → ℂ) :
    MvPolynomial.eval (fun i => t * x i) p = t ^ ℓ * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ i : Fin 3, d i = ℓ := by
    have hh := hp (MvPolynomial.mem_support_iff.mp hd)
    change Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) d = ℓ at hh
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] at hh
    exact hh
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hdeg]
  ring
theorem homogeneous_sphere_eq_zero {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ}
    (hp : p.IsHomogeneous ℓ) (h : ∀ x : Sphere, polynomialSphere p x = 0) : p = 0 := by
  apply MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => by simpa using Set.infinite_univ.image Complex.ofReal_injective.injOn)
  intro z hz
  have hreal : ∀ i : Fin 3, ∃ r : ℝ, (r : ℂ) = z i := fun i => hz i (Set.mem_univ _)
  choose r hr using hreal
  let x : Ambient := WithLp.toLp 2 r
  have eval_real (y : Ambient) (hy : y ≠ 0) :
      MvPolynomial.eval (fun i => (y i : ℂ)) p = 0 := by
    let u : Sphere := ⟨‖y‖⁻¹ • y, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]⟩
    have hu := h u
    change MvPolynomial.eval (fun i => ((u : Ambient) i : ℂ)) p = 0 at hu
    have hs := homogeneous_eval_scale hp (‖y‖ : ℂ) (fun i => ((u : Ambient) i : ℂ))
    have he : (fun i => (‖y‖ : ℂ) * ((u : Ambient) i : ℂ)) = (fun i => (y i : ℂ)) := by
      funext i
      change (‖y‖ : ℂ) * ((‖y‖⁻¹ * y i : ℝ) : ℂ) = _
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_mul]
    rw [he] at hs
    simpa only [polynomialSphere] using hs.trans (by rw [hu]; simp)
  have hx : x ≠ 0 ∨ x = 0 := ne_or_eq x 0
  rcases hx with hx | hx
  · have hh := eval_real x hx
    simpa only [x, hr, PiLp.toLp_apply, map_zero] using hh
  · have he : MvPolynomial.eval (fun i => (x i : ℂ)) p = 0 := by
      by_cases hℓ : ℓ = 0
      · subst ℓ
        have htd : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := Fin 3)).mpr hp
        have hc : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
        rw [hc]
        have hs := h (⟨WithLp.toLp 2 ![1,0,0], by simp [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩ : Sphere)
        rw [hc] at hs
        simpa only [polynomialSphere, MvPolynomial.eval_C] using hs
      · have hs := homogeneous_eval_scale hp 0 (fun _ => 0)
        simp [hℓ] at hs
        simpa [hx] using hs
    simpa only [x, hr, PiLp.toLp_apply, map_zero] using he

theorem finite_fischer_spanning (p : MvPolynomial (Fin 3) ℂ) :
    ∃ (I : Finset ℕ) (h : ℕ → MvPolynomial (Fin 3) ℂ),
      (∀ ℓ ∈ I, h ℓ ∈ harmonicPolynomials ℓ) ∧
      ∀ x : Sphere, polynomialSphere p x = ∑ ℓ ∈ I, polynomialSphere (h ℓ) x := by
  obtain ⟨I, h, hh, he⟩ := FiniteFischerRaw.unit_radius_spanning p
  refine ⟨I, h, hh, fun x => ?_⟩
  apply he
  have hn : ‖(x : Ambient)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hs := EuclideanSpace.norm_sq_eq (x : Ambient)
  rw [hn] at hs
  simpa using hs.symm

private theorem polynomial_eval_smooth (p : MvPolynomial (Fin 3) ℂ)
    {f : Fin 3 → Ambient → ℂ} {s : Set Ambient}
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (f i) s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval (fun i => f i x) p) s := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiffOn_const : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Ambient => a) s)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hf i)

theorem polynomialSphere_smooth (p : MvPolynomial (Fin 3) ℂ) :
    IsSphereSmooth (polynomialSphere p) := by
  have hn : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Ambient => ‖x‖⁻¹)
      {x : Ambient | x ≠ 0} :=
    ((contDiffOn_id.norm ℝ (fun x hx => hx)).inv
      (fun x hx => norm_ne_zero_iff.mpr hx))
  have hc (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Ambient => ((‖x‖⁻¹ • x) i : ℂ)) {x : Ambient | x ≠ 0} := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((EuclideanSpace.proj i).contDiff.comp_contDiffOn (hn.smul contDiffOn_id))
    convert h using 1
    rfl
  apply (polynomial_eval_smooth p hc).congr
  intro x hx
  have hx' : x ≠ 0 := hx
  simp [radialExtension, polynomialSphere, hx']

noncomputable def densityOuterBump : ContDiffBump (0 : Ambient) :=
  ⟨3 / 2, 2, by norm_num, by norm_num⟩

open MeasureTheory
open scoped RealInnerProductSpace
noncomputable def zonalFactor (i : Option (Fin 3)) : MvPolynomial (Fin 3) ℂ :=
  match i with | none => 1 | some j => MvPolynomial.X j
noncomputable def zonalCoord (i : Option (Fin 3)) (x : Sphere) : ℂ :=
  match i with | none => 1 | some j => ((x : Ambient) j : ℂ)
private theorem zonal_kernel_expand (N : ℕ) (x y : Sphere) :
    ((1 + inner ℝ (x : Ambient) (y : Ambient)) : ℂ)^N =
      ∑ w : Fin N → Option (Fin 3),
        (∏ k : Fin N, zonalCoord (w k) x) * (∏ k : Fin N, zonalCoord (w k) y) := by
  have hs : ((1 + inner ℝ (x : Ambient) (y : Ambient)) : ℂ) =
      ∑ i : Option (Fin 3), zonalCoord i x * zonalCoord i y := by
    simp [zonalCoord, PiLp.inner_apply, mul_comm]
  rw [hs]
  calc
    _ = ∏ k : Fin N, ∑ i : Option (Fin 3), zonalCoord i x * zonalCoord i y := by simp
    _ = _ := by rw [Fintype.prod_sum]; simp_rw [Finset.prod_mul_distrib]
private theorem zonalCoord_continuous (i : Option (Fin 3)) : Continuous (zonalCoord i) := by
  cases i with
  | none => exact continuous_const
  | some j =>
    exact Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp continuous_subtype_val)

noncomputable def polynomialZonalApproximant (N : ℕ) (F : Sphere → ℂ) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.C ((N + 1 : ℂ) / 2^N) *
    ∑ w : Fin N → Option (Fin 3),
      MvPolynomial.C (∫ y : Sphere, (∏ k : Fin N, zonalCoord (w k) y) * F y ∂sphereArea) *
        ∏ k : Fin N, zonalFactor (w k)
private theorem zonalFactor_eval (i : Option (Fin 3)) (x : Sphere) :
    MvPolynomial.eval (fun i => ((x : Ambient) i : ℂ)) (zonalFactor i) = zonalCoord i x := by
  cases i <;> simp [zonalFactor, zonalCoord, polynomialSphere]

theorem polynomialZonalApproximant_eq_integral (N : ℕ) (F : Sphere → ℂ) (hF : Continuous F) (x : Sphere) :
    polynomialSphere (polynomialZonalApproximant N F) x =
      ∫ y : Sphere, ((N + 1 : ℂ) / 2^N) *
        ((1 + inner ℝ (x : Ambient) (y : Ambient)) : ℂ)^N * F y ∂sphereArea := by
  letI := sphereArea_isProbabilityMeasure
  simp only [polynomialZonalApproximant, polynomialSphere, map_mul, map_sum, map_prod, MvPolynomial.eval_C]
  simp_rw [zonalFactor_eval]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  congr 1
  simp_rw [zonal_kernel_expand, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro w hw
    simp_rw [mul_assoc]
    rw [integral_const_mul, mul_comm]
  · intro w hw
    exact ((continuous_const.mul (continuous_finset_prod _ (fun k hk => zonalCoord_continuous (w k)))).mul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem polynomialZonal_affine_bounds (x y : Sphere) :
    0 ≤ (1 + inner ℝ (x : Ambient) (y : Ambient)) / 2 ∧
    (1 + inner ℝ (x : Ambient) (y : Ambient)) / 2 ≤ 1 := by
  have h := abs_real_inner_le_norm (x : Ambient) (y : Ambient)
  simp only [mem_sphere_zero_iff_norm.mp x.property,
    mem_sphere_zero_iff_norm.mp y.property, one_mul] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]

theorem polynomialZonal_far_bound (N : ℕ) (x y : Sphere) (δ : ℝ) (hd : δ ≤ dist x y) (hδ : 0 ≤ δ) :
    (N + 1 : ℝ) * ((1 + inner ℝ (x : Ambient) (y : Ambient)) / 2)^N ≤
      (N + 1 : ℝ) * (1 - δ^2 / 4)^N := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (polynomialZonal_affine_bounds x y).1
  have hs := norm_sub_sq_real (x : Ambient) (y : Ambient)
  simp only [mem_sphere_zero_iff_norm.mp x.property,
    mem_sphere_zero_iff_norm.mp y.property, one_pow] at hs
  have hd' : δ ≤ ‖(x : Ambient) - (y : Ambient)‖ := by
    change δ ≤ dist (x : Ambient) (y : Ambient) at hd
    simpa [dist_eq_norm] using hd
  have hsq : δ^2 ≤ ‖(x : Ambient) - (y : Ambient)‖^2 :=
    pow_le_pow_left₀ hδ hd' 2
  nlinarith

theorem polynomialZonal_concentration (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ 2) :
    Filter.Tendsto (fun N : ℕ => (N + 1 : ℝ) * (1 - δ^2/4)^N)
      Filter.atTop (nhds 0) := by
  have h : |1 - δ^2 / 4| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hh := (tendsto_self_mul_const_pow_of_abs_lt_one h).add
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h)
  simpa only [zero_add, add_mul, one_mul] using hh

theorem polynomialZonal_mass (N : ℕ) (x : Sphere) :
    (∫ y : Sphere, (N + 1 : ℝ) *
      ((1 + inner ℝ (x : Ambient) (y : Ambient)) / 2)^N ∂sphereArea) = 1 := by
  let φ : Sphere → ℝ := fun y => (1 - inner ℝ (x : Ambient) (y : Ambient)) / 2
  have hc : Continuous φ := by
    dsimp [φ]
    fun_prop
  have hf : Continuous (fun t : ℝ => (N + 1 : ℝ) * (1 - t)^N) := by fun_prop
  have hmap := integral_map_of_stronglyMeasurable (μ := sphereArea) hc.measurable hf.stronglyMeasurable
  rw [sphereArea_uniform_projection x] at hmap
  calc
    _ = ∫ y : Sphere, (N + 1 : ℝ) * (1 - φ y)^N ∂sphereArea := by
      congr 1
      ext y
      congr 2
      dsimp [φ]
      ring
    _ = ∫ t in Set.Icc (0 : ℝ) 1, (N + 1 : ℝ) * (1 - t)^N := hmap.symm
    _ = ∫ t in (0 : ℝ)..1, (N + 1 : ℝ) * (1 - t)^N := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]
    _ = (N + 1 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - t)^N := by
      rw [intervalIntegral.integral_const_mul]
    _ = 1 := by
      rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^N) 1]
      simp [integral_pow]
      exact mul_inv_cancel₀ (by positivity)

theorem finite_polynomial_smooth_density_of_finite_order (F : Sphere → ℂ)
    (ha : ∀ N : ℕ, ∃ p : MvPolynomial (Fin 3) ℂ,
      ∀ (w : List (Fin 3)), w.length ≤ N → ∀ x : Sphere,
        ‖rotationWord w (fun y => F y - polynomialSphere p y) x‖ ≤ 1 / (N + 1 : ℝ)) :
    ∃ p : ℕ → MvPolynomial (Fin 3) ℂ, ∀ n : ℕ,
      Filter.Tendsto (fun N => rotationSup n (fun x => F x - polynomialSphere (p N) x))
        Filter.atTop (nhds 0) := by
  classical
  choose p hp using ha
  refine ⟨p, fun n => ?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => rotationSup_nonneg n _)) _
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  apply Real.sSup_le _ (by positivity)
  rintro r ⟨w, hw, x, rfl⟩
  exact hp N w (hw.trans hN) x

theorem rawZonalIntegral_uniform_approximation (F : Sphere → ℂ) (hF : Continuous F) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ x : Sphere,
      ‖F x - rawZonalIntegral N F x‖ ≤ ε := by
  letI := sphereArea_isProbabilityMeasure
  have hh := positiveKernel_uniform_approximation
    (fun N x y => (N + 1 : ℝ) * ((1 + inner ℝ (x : Ambient) (y : Ambient)) / 2)^N)
    (fun δ N => (N + 1 : ℝ) * (1 - δ^2 / 4)^N)
    (by intro N x; fun_prop)
    (by intro N x y; exact mul_nonneg (by positivity) (pow_nonneg (polynomialZonal_affine_bounds x y).1 _))
    polynomialZonal_mass
    (by intro δ hd hu N; apply mul_nonneg (by positivity); apply pow_nonneg; nlinarith)
    (by intro δ hd hu N x y hxy; exact polynomialZonal_far_bound N x y δ hxy hd.le)
    (by intro δ hd hu; exact polynomialZonal_concentration δ hd (by linarith)) F hF
  intro ε hε
  filter_upwards [hh ε hε] with N hN x
  convert hN x using 2
  unfold rawZonalIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat, div_pow]
  ring

theorem finite_polynomial_smooth_density (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    ∃ p : ℕ → MvPolynomial (Fin 3) ℂ,
      ∀ n : ℕ, Filter.Tendsto
        (fun N => rotationSup n (fun x => F x - polynomialSphere (p N) x))
        Filter.atTop (nhds 0) := by
  apply finite_polynomial_smooth_density_of_finite_order F
  intro n
  have h : ∀ᶠ N : ℕ in Filter.atTop, ∀ w : List (Fin 3), w.length ≤ n →
      ∀ x : Sphere,
        ‖rotationWord w F x - rawZonalIntegral N (rotationWord w F) x‖ ≤
          1 / (n + 1 : ℝ) := by
    apply ((List.finite_length_le (Fin 3) n).eventually_all).2
    intro w hw
    exact rawZonalIntegral_uniform_approximation _ ((rotationWord_smooth w hF).continuous) _ (by positivity)
  obtain ⟨N, hN⟩ := h.exists
  refine ⟨polynomialZonalApproximant N F, fun w hw x => ?_⟩
  have hc : Continuous F := hF.continuous
  have hpoly := polynomialSphere_smooth (polynomialZonalApproximant N F)
  rw [show (fun y => F y - polynomialSphere (polynomialZonalApproximant N F) y) =
      (fun y => F y + -(polynomialSphere (polynomialZonalApproximant N F) y)) by funext; ring]
  rw [rotationWord_add w hF (IsSphereSmooth.neg hpoly), rotationWord_neg]
  simp only [Pi.add_apply, Pi.neg_apply]
  rw [show polynomialSphere (polynomialZonalApproximant N F) =
      rawZonalIntegral N F from funext (fun z => polynomialZonalApproximant_eq_integral N F hc z)]
  rw [rawZonalIntegral_rotationWord N F hF w]
  exact hN w hw x

end DedekindZetaZeroFree.ComplexFractionalInverse
