module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.CompactHeightSublevels
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.CodifferentialCovariance
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.UniformCutoffGraphConvergence

@[expose] public section

section

noncomputable section
open scoped ContDiff
open Filter Topology Real
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.RadialProfile

def theta (t : ℝ) : ℝ := 1 - smoothTransition t

theorem theta_smooth : ContDiff ℝ (⊤ : ℕ∞) theta :=
  contDiff_const.sub smoothTransition.contDiff

theorem theta_one {t : ℝ} (ht : t ≤ 0) : theta t = 1 := by
  simp [theta, smoothTransition.zero_of_nonpos ht]

theorem theta_zero {t : ℝ} (ht : 1 ≤ t) : theta t = 0 := by
  simp [theta, smoothTransition.one_of_one_le ht]

private theorem theta_deriv_zero {t : ℝ} (ht : t ∉ Set.Icc (0 : ℝ) 1) :
    deriv theta t = 0 := by
  have h : theta =ᶠ[nhds t] (fun _ => theta t) := by
    by_cases h0 : 0 ≤ t
    · have h1 : 1 < t := lt_of_not_ge (fun h1 => ht ⟨h0,h1⟩)
      filter_upwards [eventually_gt_nhds h1] with u hu
      rw [theta_zero hu.le, theta_zero h1.le]
    · have h0' : t < 0 := lt_of_not_ge h0
      filter_upwards [eventually_lt_nhds h0'] with u hu
      rw [theta_one hu.le, theta_one h0'.le]
  rw [h.deriv_eq]
  simp

theorem theta_deriv_compact : HasCompactSupport (deriv theta) := by
  exact HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (fun t ht => theta_deriv_zero ht)

theorem theta_derivatives_bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
    ‖deriv theta t‖ ≤ B ∧ ‖deriv (deriv theta) t‖ ≤ B := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv theta) := theta_smooth.deriv'
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv theta)) := h1.deriv'
  obtain ⟨B1,hB1⟩ := theta_deriv_compact.isCompact.exists_bound_of_continuousOn'
    (f := fun t => Multiplicative.ofAdd (deriv theta t)) h1.continuous.continuousOn
  obtain ⟨B2,hB2⟩ := theta_deriv_compact.deriv.isCompact.exists_bound_of_continuousOn'
    (f := fun t => Multiplicative.ofAdd (deriv (deriv theta) t)) h2.continuous.continuousOn
  refine ⟨max 0 (max B1 B2), le_max_left _ _, fun t => ⟨?_, ?_⟩⟩
  · by_cases ht : t ∈ tsupport (deriv theta)
    · exact (hB1 t ht).trans ((le_max_left _ _).trans (le_max_right _ _))
    · rw [image_eq_zero_of_notMem_tsupport ht, norm_zero]
      exact le_max_left _ _
  · by_cases ht : t ∈ tsupport (deriv (deriv theta))
    · exact (hB2 t ht).trans ((le_max_right _ _).trans (le_max_right _ _))
    · rw [image_eq_zero_of_notMem_tsupport ht, norm_zero]
      exact le_max_left _ _

def mean (d : ℕ) : HyperbolicChart.Space d →L[ℝ] ℝ :=
  (d : ℝ)⁻¹ • ∑ i : Fin d,
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d × Fin 3 => ℝ) (i,2)

theorem mean_apply (d : ℕ) (p : HyperbolicChart.Space d) :
    mean d p = (d : ℝ)⁻¹ * ∑ i : Fin d, p (i,2) := by
  simp [mean]

theorem mean_coordinate (d : ℕ) (i : Fin d) (k : Fin 3) :
    mean d (HyperbolicChart.coordinateVector d i k) =
      if k = 2 then (d : ℝ)⁻¹ else 0 := by
  simp only [mean_apply, HyperbolicChart.coordinateVector]
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro j hj hji
    simp [hji]
  · simp

theorem radial_partial (d : ℕ) (g : ℝ → ℂ) (hg : Differentiable ℝ g)
    (i : Fin d) (k : Fin 3) (p : HyperbolicChart.Space d) :
    HyperbolicChart.coordinateDerivative d i k (fun q => g (mean d q)) p =
      if k = 2 then (d : ℂ)⁻¹ * deriv g (mean d p) else 0 := by
  unfold HyperbolicChart.coordinateDerivative
  change fderiv ℝ (g ∘ mean d) p _ = _
  rw [fderiv_comp p (hg _) (mean d).differentiableAt,
    ContinuousLinearMap.comp_apply, (mean d).fderiv, fderiv_eq_smul_deriv,
    mean_coordinate]
  split_ifs <;> simp [Algebra.smul_def, mul_comm]

theorem radial_differential (d : ℕ) (g : ℝ → ℂ) (hg : Differentiable ℝ g)
    (p : HyperbolicChart.Space d) (i : Fin d) (k : Fin 3) :
    HyperbolicChart.differential d (fun q => g (mean d q)) p i k =
      if k = 0 then (d : ℂ)⁻¹ * deriv g (mean d p) else 0 := by
  fin_cases k <;> simp [HyperbolicChart.differential, radial_partial d g hg]

theorem radial_laplacian (d : ℕ) (hd : 0 < d) (g : ℝ → ℂ)
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    (p : HyperbolicChart.Space d) :
    HyperbolicChart.laplacian d (fun q => g (mean d q)) p =
      -(d : ℂ)⁻¹ * deriv (deriv g) (mean d p) + 2 * deriv g (mean d p) := by
  have h2 (i : Fin d) : HyperbolicChart.coordinateDerivative d i 2
      (fun q => g (mean d q)) = fun q => (d : ℂ)⁻¹ * deriv g (mean d q) := by
    funext q; simp [radial_partial d g hg]
  have h0 (i : Fin d) : HyperbolicChart.coordinateDerivative d i 0
      (fun q => g (mean d q)) = 0 := by
    funext q; simp [radial_partial d g hg]
  have h1 (i : Fin d) : HyperbolicChart.coordinateDerivative d i 1
      (fun q => g (mean d q)) = 0 := by
    funext q; simp [radial_partial d g hg]
  have hder : deriv (fun t => (d : ℂ)⁻¹ * deriv g t) =
      fun t => (d : ℂ)⁻¹ * deriv (deriv g) t := by
    funext t; exact deriv_const_mul _ (hg' t)
  unfold HyperbolicChart.laplacian
  simp_rw [h2, h0, h1]
  have hz (i : Fin d) (k : Fin 3) :
      HyperbolicChart.coordinateDerivative d i k (0 : HyperbolicChart.Space d → ℂ) p = 0 := by
    simp [HyperbolicChart.coordinateDerivative]
  simp only [hz, add_zero, mul_zero, sub_zero]
  change (∑ i : Fin d, (-HyperbolicChart.coordinateDerivative d i 2
    (fun q => ((fun t => (d : ℂ)⁻¹ * deriv g t) (mean d q))) p +
      2 * ((d : ℂ)⁻¹ * deriv g (mean d p)))) = _
  simp_rw [radial_partial d _ (hg'.const_mul _) _ _ _]
  simp only [ite_true, hder]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem radial_gradient_sq (d : ℕ) (g : ℝ → ℂ) (hg : Differentiable ℝ g)
    (p : HyperbolicChart.Space d) :
    (∑ i : Fin d, ∑ k : Fin 3,
      ‖HyperbolicChart.differential d (fun q => g (mean d q)) p i k‖ ^ 2) =
      (d : ℝ) * ‖(d : ℂ)⁻¹ * deriv g (mean d p)‖ ^ 2 := by
  simp_rw [radial_differential d g hg]
  simp [Fin.sum_univ_succ]

theorem radial_derivative_bound (d : ℕ) (hd : 0 < d) (g : ℝ → ℂ)
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    (B : ℝ) (hB : 0 ≤ B) (h1 : ∀ t, ‖deriv g t‖ ≤ B)
    (h2 : ∀ t, ‖deriv (deriv g) t‖ ≤ B) (p : HyperbolicChart.Space d) :
    Real.sqrt (∑ i : Fin d, ∑ k : Fin 3,
      ‖HyperbolicChart.differential d (fun q => g (mean d q)) p i k‖ ^ 2) +
      ‖HyperbolicChart.laplacian d (fun q => g (mean d q)) p‖ ≤
        (Real.sqrt (d : ℝ) + 3) * B := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hi : ‖(d : ℂ)⁻¹‖ ≤ 1 := by
    simp only [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ hd1
  have hmul (z : ℂ) (hz : ‖z‖ ≤ B) : ‖(d : ℂ)⁻¹ * z‖ ≤ B := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hi (norm_nonneg z)).trans (by simpa using hz)
  have hgB : Real.sqrt (∑ i : Fin d, ∑ k : Fin 3,
      ‖HyperbolicChart.differential d (fun q => g (mean d q)) p i k‖ ^ 2) ≤
      Real.sqrt (d : ℝ) * B := by
    rw [radial_gradient_sq d g hg, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hmul _ (h1 _)) (Real.sqrt_nonneg _)
  have hlB : ‖HyperbolicChart.laplacian d (fun q => g (mean d q)) p‖ ≤ 3 * B := by
    rw [radial_laplacian d hd g hg hg']
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_neg, norm_mul]
    have hh := hmul (deriv (deriv g) (mean d p)) (h2 _)
    rw [norm_mul] at hh
    have ht : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [ht]
    linarith [h1 (mean d p)]
  nlinarith

theorem translated_transition_bound (d : ℕ) (hd : 0 < d) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ (shift : ℝ) (p : HyperbolicChart.Space d),
      Real.sqrt (∑ i : Fin d, ∑ k : Fin 3,
        ‖HyperbolicChart.differential d
          (fun q => (smoothTransition (mean d q - shift) : ℂ)) p i k‖ ^ 2) +
        ‖HyperbolicChart.laplacian d
          (fun q => (smoothTransition (mean d q - shift) : ℂ)) p‖ ≤ B := by
  obtain ⟨B,hB,hθ⟩ := theta_derivatives_bounded
  refine ⟨(Real.sqrt (d : ℝ) + 3) * B, mul_nonneg (by positivity) hB, ?_⟩
  intro shift p
  let g : ℝ → ℂ := fun t => (smoothTransition (t - shift) : ℂ)
  have hs : ContDiff ℝ (⊤ : ℕ∞) smoothTransition := smoothTransition.contDiff
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (deriv smoothTransition) := hs.deriv'
  have hθ1 : deriv theta = -deriv smoothTransition := by
    funext t
    exact ((hs.differentiable (by simp) t).hasDerivAt.const_sub 1).deriv
  have hθ2 : deriv (deriv theta) = -deriv (deriv smoothTransition) := by
    rw [hθ1]
    funext t
    simp [deriv_neg]
  have h1 : deriv g = fun t => ((deriv smoothTransition (t - shift) : ℝ) : ℂ) := by
    funext t
    simpa [g, Function.comp_def] using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (((hs.differentiable (by simp)) (t-shift)).hasDerivAt.comp t
        ((hasDerivAt_id t).sub_const shift))).deriv
  have h2 : deriv (deriv g) =
      fun t => ((deriv (deriv smoothTransition) (t - shift) : ℝ) : ℂ) := by
    rw [h1]
    funext t
    simpa [Function.comp_def] using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (((hs'.differentiable (by simp)) (t-shift)).hasDerivAt.comp t
        ((hasDerivAt_id t).sub_const shift))).deriv
  have hg : Differentiable ℝ g := Complex.ofRealCLM.differentiable.comp
    ((hs.differentiable (by simp)).comp (differentiable_id.sub_const shift))
  have hg' : Differentiable ℝ (deriv g) := by
    rw [h1]
    exact Complex.ofRealCLM.differentiable.comp
      ((hs'.differentiable (by simp)).comp (differentiable_id.sub_const shift))
  apply radial_derivative_bound d hd g hg hg' B hB _ _ p
  · intro t
    rw [h1]
    have h := (hθ (t-shift)).1
    rw [hθ1] at h
    simpa using h
  · intro t
    rw [h2]
    have h := (hθ (t-shift)).2
    rw [hθ2] at h
    simpa using h

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.RadialProfile

end

end

section

noncomputable section
open scoped Classical NumberField ContDiff
open Topology Real
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.CutoffScalars
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
variable (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
abbrev Cusp := Σ i : Fin a.componentCount, Fin (a.cuspAtlas i).cuspCount
abbrev X := KPFiniteCuspAtlas.rawXU F ζ hζ U

def lift (c : Cusp a) (z : KPCuspCharts.Coordinates F) : X (F := F) (ζ := ζ) (hζ := hζ) (U := U) :=
  Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
    (((a.cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F z), a.representative c.1)

def endRegion (T : ℝ) (c : Cusp a) : Set (X (F := F) (ζ := ζ) (hζ := hζ) (U := U)) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative c.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative c.1))
      ((a.cuspAtlas c.1).representative c.2) T

def height (c : Cusp a) (x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)) : ℝ :=
  if h : ∃ z : KPCuspCharts.Coordinates F, a.threshold < z.2 ∧ lift a c z = x
  then (Classical.choose h).2 else 0

def shift (n : ℕ) : ℝ := max (n : ℝ) (a.threshold + 1)

def eta (n : ℕ) (c : Cusp a) : X (F := F) (ζ := ζ) (hζ := hζ) (U := U) → ℝ :=
  (endRegion a a.threshold c).indicator (fun x => smoothTransition (height a c x - shift a n))

def rho (n : ℕ) (x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)) : ℝ :=
  1 - ∑ c : Cusp a, eta a n c x

private theorem range_lift (T : ℝ) (hT : a.threshold ≤ T) (c : Cusp a) :
    lift a c '' {z : KPCuspCharts.Coordinates F | T < z.2} = endRegion a T c :=
  (KPActualCollarBuffer.actual_height_descent F ζ hζ hF U a T hT).1 c

private theorem height_lift (c : Cusp a) (z : KPCuspCharts.Coordinates F)
    (hz : a.threshold < z.2) : height a c (lift a c z) = z.2 :=
  (KPActualCollarBuffer.actual_height_descent F ζ hζ hF U a a.threshold le_rfl).2.1 c z hz

private theorem component_injective (i : Fin a.componentCount) :
    Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)) := by
  intro x y he
  have hh : a.components ⟨i,x⟩ = a.components ⟨i,y⟩ := by
    simpa only [a.components_formula] using he
  exact eq_of_heq (Sigma.mk.inj (a.components.injective hh)).2

private theorem end_unique (c d : Cusp a) (x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U))
    (hc : x ∈ endRegion a a.threshold c) (hd : x ∈ endRegion a a.threshold d) : c = d := by
  obtain ⟨y,hy,he⟩ := hc
  obtain ⟨z,hz,hz'⟩ := hd
  have hh : a.components ⟨c.1,y⟩ = a.components ⟨d.1,z⟩ := by
    simpa only [a.components_formula] using he.trans hz'.symm
  have hi : c.1 = d.1 := Sigma.mk.inj (a.components.injective hh) |>.1
  rcases c with ⟨i,c⟩
  rcases d with ⟨j,d⟩
  dsimp at hi
  subst j
  have heq : y = z := component_injective a i (he.trans hz'.symm)
  subst z
  have hcd : c = d := by
    by_contra hn
    have hdis := (a.cuspAtlas i).disjoint_ends hn
    rw [a.common_threshold i] at hdis
    exact Set.disjoint_left.mp hdis hy hz
  subst d
  rfl

private theorem eta_zero_off (n : ℕ) (c : Cusp a) {x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)}
    (hx : x ∉ endRegion a a.threshold c) : eta a n c x = 0 := by
  exact Set.indicator_of_notMem hx _

private theorem eta_bounds (n : ℕ) (c : Cusp a) (x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)) :
    0 ≤ eta a n c x ∧ eta a n c x ≤ 1 := by
  by_cases hx : x ∈ endRegion a a.threshold c
  · simp only [eta, Set.indicator_of_mem hx]
    exact ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · rw [eta_zero_off a n c hx]
    norm_num

private theorem sum_eq_eta (n : ℕ) (c : Cusp a) {x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)}
    (hx : x ∈ endRegion a a.threshold c) : ∑ d : Cusp a, eta a n d x = eta a n c x := by
  apply Finset.sum_eq_single c
  · intro d _ hdc
    apply eta_zero_off
    exact fun hd => hdc (end_unique a d c x hd hx)
  · simp

theorem rho_bounds (n : ℕ) (x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)) :
    0 ≤ rho a n x ∧ rho a n x ≤ 1 := by
  by_cases hx : ∃ c : Cusp a, x ∈ endRegion a a.threshold c
  · obtain ⟨c,hc⟩ := hx
    unfold rho
    rw [sum_eq_eta a n c hc]
    have hh := eta_bounds a n c x
    constructor <;> linarith
  · have he : ∀ c : Cusp a, eta a n c x = 0 := fun c =>
      eta_zero_off a n c (fun hc => hx ⟨c,hc⟩)
    simp [rho, he]

private theorem profile_zero (n : ℕ) {t : ℝ} (ht : t ≤ a.threshold + 1) :
    smoothTransition (t - shift a n) = 0 := by
  apply smoothTransition.zero_of_nonpos
  have hs := le_max_right (n : ℝ) (a.threshold + 1)
  dsimp [shift]
  linarith

theorem rho_smooth (n : ℕ) (i : Fin a.componentCount) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : KPFiniteCuspAtlas.SymmetricSpace F => rho a n
      (KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
        (KPCuspSiegel.projection F _ x))) := by
  have he (c : Cusp a) :=
    (GenericZeroExtension.scalar_zeroExtension_smooth_continuous a a.threshold
      (a.threshold + 1) le_rfl (by linarith) c
      (fun t => smoothTransition (t - shift a n))
      (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
      (fun t ht => profile_zero a n ht)).1 i
  exact contDiff_const.sub (ContDiff.sum fun c _ => he c)

theorem rho_on_sublevel (n : ℕ) {x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)}
    (hx : x ∉ ⋃ c : Cusp a, endRegion a (shift a n) c) : rho a n x = 1 := by
  have he (c : Cusp a) : eta a n c x = 0 := by
    by_cases hc : x ∈ endRegion a a.threshold c
    · rw [← range_lift a a.threshold le_rfl c] at hc
      obtain ⟨z,hz,rfl⟩ := hc
      have ht : z.2 ≤ shift a n := by
        by_contra hn
        apply hx
        apply Set.mem_iUnion.mpr
        refine ⟨c, ?_⟩
        rw [← range_lift a (shift a n) (by
          dsimp [shift]; have := le_max_right (n : ℝ) (a.threshold + 1); linarith) c]
        exact ⟨z, lt_of_not_ge hn, rfl⟩
      have hm : lift a c z ∈ endRegion a a.threshold c := by
        rw [← range_lift a a.threshold le_rfl c]
        exact ⟨z,hz,rfl⟩
      simp only [eta, Set.indicator_of_mem hm, height_lift a c z hz]
      exact smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht)
    · exact eta_zero_off a n c hc
  simp [rho, he]

theorem rho_on_lift (n : ℕ) (c : Cusp a) (z : KPCuspCharts.Coordinates F)
    (hz : a.threshold < z.2) : rho a n (lift a c z) = RadialProfile.theta (z.2 - shift a n) := by
  have hc : lift a c z ∈ endRegion a a.threshold c := by
    rw [← range_lift a a.threshold le_rfl c]
    exact ⟨z,hz,rfl⟩
  unfold rho
  rw [sum_eq_eta a n c hc]
  simp only [eta, Set.indicator_of_mem hc, height_lift a c z hz, RadialProfile.theta]

theorem rho_compact_support (n : ℕ) : HasCompactSupport (rho a n) := by
  letI := CoreChartLocalizers.quotient_hausdorff F ζ hζ hF U a
  let K := (⋃ c : Cusp a, endRegion a (shift a n + 1) c)ᶜ
  have hK : IsCompact K := by
    simpa only [K, endRegion, Set.iUnion_sigma, Set.compl_eq_univ_sdiff] using
      GenericZeroExtension.height_sublevel_isCompact a (shift a n + 1)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  have hm : x ∈ ⋃ c : Cusp a, endRegion a (shift a n + 1) c := by
    simpa only [K, Set.mem_compl_iff, not_not] using hn
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hm
  have hS : a.threshold ≤ shift a n + 1 := by
    dsimp [shift]; have := le_max_right (n : ℝ) (a.threshold + 1); linarith
  rw [← range_lift a (shift a n + 1) hS c] at hc
  obtain ⟨z,hz,rfl⟩ := hc
  have hz0 : a.threshold < z.2 := lt_of_le_of_lt hS hz
  have he : rho a n (lift a c z) = 0 := by
    rw [rho_on_lift a n c z hz0]
    exact RadialProfile.theta_zero (by change shift a n + 1 < z.2 at hz; linarith)
  exact hx he

def heightBound : ℕ := Nat.ceil (a.threshold + 1)

theorem above_threshold : a.threshold < (heightBound a : ℝ) := by
  have hh : a.threshold + 1 ≤ (heightBound a : ℝ) := Nat.le_ceil _
  linarith

private theorem shift_eq (n : ℕ) (hn : heightBound a ≤ n) : shift a n = n := by
  have hh : a.threshold + 1 ≤ (heightBound a : ℝ) := Nat.le_ceil _
  have hn' : (heightBound a : ℝ) ≤ n := by exact_mod_cast hn
  exact max_eq_left (hh.trans hn')

theorem rho_on_integer_sublevel (n : ℕ) (hn : heightBound a ≤ n)
    {x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)}
    (hx : x ∉ ⋃ c : Cusp a, endRegion a (n : ℝ) c) : rho a n x = 1 := by
  apply rho_on_sublevel
  simpa only [shift_eq a n hn] using hx

theorem rho_on_core (n : ℕ) {x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)}
    (hx : x ∉ ⋃ c : Cusp a, endRegion a a.threshold c) : rho a n x = 1 := by
  have he (c : Cusp a) : eta a n c x = 0 :=
    eta_zero_off a n c (fun hc => hx (Set.mem_iUnion.mpr ⟨c,hc⟩))
  simp [rho, he]

theorem rho_above_next (n : ℕ) (hn : heightBound a ≤ n)
    {x : X (F := F) (ζ := ζ) (hζ := hζ) (U := U)}
    (hx : x ∈ ⋃ i : Fin a.componentCount, ⋃ c : Fin (a.cuspAtlas i).cuspCount,
      KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i)) ''
          (KPCuspSiegel.action F ((a.cuspAtlas i).representative c) ''
            {z | (n : ℝ) + 1 ≤ KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z}))) :
    rho a n x = 0 := by
  obtain ⟨i,hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨c,hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_, ⟨_, ⟨y,hy,rfl⟩,rfl⟩,rfl⟩ := hx
  let z := (KPCuspCharts.toArchHomeomorph F (KPCuspCharts.positive_dimension F hF)).symm y
  have he : KPCuspCharts.toArch F z = y :=
    (KPCuspCharts.toArchHomeomorph F (KPCuspCharts.positive_dimension F hF)).apply_symm_apply y
  have ht : z.2 = KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) y := by
    rw [← he, KPCuspCharts.toArch_meanHeight F (KPCuspCharts.positive_dimension F hF)]
  have hn' : a.threshold < (n : ℝ) :=
    (above_threshold a).trans_le (by exact_mod_cast hn)
  have hz : a.threshold < z.2 := by
    rw [ht]
    change (n : ℝ) + 1 ≤ KPCuspLogShape.meanHeight _ y at hy
    linarith
  rw [← he]
  change rho a n (lift a ⟨i,c⟩ z) = 0
  rw [rho_on_lift a n ⟨i,c⟩ z hz, shift_eq a n hn]
  apply RadialProfile.theta_zero
  rw [ht]
  change (n : ℝ) + 1 ≤ KPCuspLogShape.meanHeight _ y at hy
  linarith

theorem eta_local_model (n : ℕ) (c : Cusp a) (i : Fin a.componentCount)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    let Q := fun y : KPFiniteCuspAtlas.SymmetricSpace F =>
      KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
        (KPCuspSiegel.projection F _ y)
    (fun y => eta a n c (Q y)) =ᶠ[𝓝 x] 0 ∨
      ∃ γ : KPCuspArithmetic.PGL2 F,
        (fun y => eta a n c (Q y)) =ᶠ[𝓝 x]
          (fun y => smoothTransition
            (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (γ • y) - shift a n)) := by
  exact GenericZeroExtension.scalar_zeroExtension_local_model a a.threshold
    (a.threshold + 1) le_rfl (by linarith) c
    (fun t => smoothTransition (t - shift a n)) (fun t ht => profile_zero a n ht) i x

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.CutoffScalars

end

end

section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff
open Filter Topology
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.ScalarIsometry
private theorem sum_real_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] ℝ) :
    ∑ i, (L (b i)) ^ 2 = ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L‖ ^ 2 := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    b.sum_sq_inner_left ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L)

private theorem sum_complex_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b c : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] ℂ) :
    ∑ i, ‖L (b i)‖ ^ 2 = ∑ i, ‖L (c i)‖ ^ 2 := by
  have hRe := (sum_real_basis b (Complex.reCLM.comp L)).trans
    (sum_real_basis c (Complex.reCLM.comp L)).symm
  have hIm := (sum_real_basis b (Complex.imCLM.comp L)).trans
    (sum_real_basis c (Complex.imCLM.comp L)).symm
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at hRe hIm
  simp only [Complex.sq_norm, Complex.normSq_apply, Finset.sum_add_distrib]
  simpa only [pow_two] using congrArg₂ (· + ·) hRe hIm

private theorem differential_frame (d : ℕ) (f : HyperbolicChart.Space d → ℂ) (x : HyperbolicChart.Space d) (k : Fin d × Fin 3) :
    (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) k =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ k)) := by
  rcases k with ⟨i, k⟩
  fin_cases k
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))) =
        HyperbolicChart.coordinateVector d i 2 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (0 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative]
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector d i 0 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (1 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector d i 1 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (2 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]

private theorem differential_norm_isometry (d : ℕ)
    (ψ : HyperbolicChart.Space d → HyperbolicChart.Space d)
    (x : HyperbolicChart.Space d)
    (hψ : DifferentiableAt ℝ ψ x)
    (hm : ∀ v w, HyperbolicChart.metric d (ψ x)
      (fderiv ℝ ψ x v) (fderiv ℝ ψ x w) = HyperbolicChart.metric d x v w)
    (f : HyperbolicChart.Space d → ℂ) (hf : DifferentiableAt ℝ f (ψ x)) :
    (∑ i, ∑ k, ‖HyperbolicChart.differential d (f ∘ ψ) x i k‖ ^ 2) =
    ∑ i, ∑ k, ‖HyperbolicChart.differential d f (ψ x) i k‖ ^ 2 := by
  let Q : EuclideanSpace ℝ (Fin d × Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) :=
    (CotangentLogCoframe.C d (ψ x)).toContinuousLinearMap.comp
      ((fderiv ℝ ψ x).comp (CotangentLogCoframe.H d x).toContinuousLinearMap)
  have hQ : ∀ v w, inner ℝ (Q v) (Q w) = inner ℝ v w := by
    intro v w
    change inner ℝ (CotangentLogCoframe.C d (ψ x)
      (fderiv ℝ ψ x (CotangentLogCoframe.H d x v)))
      (CotangentLogCoframe.C d (ψ x) (fderiv ℝ ψ x (CotangentLogCoframe.H d x w))) = _
    rw [CotangentLogCoframe.inner_C, hm, ← CotangentLogCoframe.inner_C]
    simp [CotangentLogCoframe.H]
  let q : EuclideanSpace ℝ (Fin d × Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) :=
    LinearIsometryEquiv.ofSurjective
      {toLinearMap := Q.toLinearMap,
       norm_map' := (LinearMap.norm_map_iff_inner_map_map Q).2 hQ}
      (by
        apply LinearMap.surjective_of_injective
        exact (show EuclideanSpace ℝ (Fin d × Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) from
          {toLinearMap := Q.toLinearMap,
           norm_map' := (LinearMap.norm_map_iff_inner_map_map Q).2 hQ}).injective)
  let L := (fderiv ℝ f (ψ x)).comp (CotangentLogCoframe.H d (ψ x)).toContinuousLinearMap
  have hh : ∀ v, fderiv ℝ ψ x (CotangentLogCoframe.H d x v) =
      CotangentLogCoframe.H d (ψ x) (q v) := by
    intro v
    apply (CotangentLogCoframe.C d (ψ x)).injective
    simp only [CotangentLogCoframe.H, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hsum := sum_complex_basis ((EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).map q)
    (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ) L
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hsum
  convert hsum using 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [← CotangentLogCoframe.j_apply d (HyperbolicChart.differential d (f ∘ ψ) x) i k,
      differential_frame, fderiv_comp x hf hψ]
    simp only [ContinuousLinearMap.comp_apply, hh, OrthonormalBasis.map_apply, L]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [← CotangentLogCoframe.j_apply d (HyperbolicChart.differential d f (ψ x)) i k,
      differential_frame]
    rfl

private theorem differential_evaluation (d : ℕ) (f : HyperbolicChart.Space d → ℂ)
    (x u : HyperbolicChart.Space d) :
    (∑ ik, (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) ik *
      ((CotangentLogCoframe.C d x u) ik : ℂ)) = fderiv ℝ f x u := by
  simp_rw [differential_frame]
  have he := (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).sum_repr (CotangentLogCoframe.C d x u)
  have hh := congrArg (fun v => fderiv ℝ f x (CotangentLogCoframe.H d x v)) he
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    CotangentLogCoframe.H, ContinuousLinearEquiv.symm_apply_apply, Complex.real_smul, mul_comm] using hh

private theorem smooth_differential (d : ℕ) (f : HyperbolicChart.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (HyperbolicChart.differential d f) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro k
  have hD (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (HyperbolicChart.coordinateDerivative d i j f) := by
    have hh : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
    exact hh.clm_apply contDiff_const
  have hE : ContDiff ℝ (⊤ : ℕ∞) (fun p : HyperbolicChart.Space d => (Real.exp (p (i,2)) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))
  fin_cases k
  · exact hD 2
  · exact hE.mul (hD 0)
  · exact hE.mul (hD 1)

theorem laplacian_isometry (d : ℕ) (hd : 1 ≤ d)
    (ψ : HyperbolicChart.Space d → HyperbolicChart.Space d)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hm : ∀ x u v, HyperbolicChart.metric d (ψ x) (fderiv ℝ ψ x u)
      (fderiv ℝ ψ x v) = HyperbolicChart.metric d x u v)
    (f : HyperbolicChart.Space d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : HyperbolicChart.Space d) :
    HyperbolicChart.laplacian d (f ∘ ψ) x = HyperbolicChart.laplacian d f (ψ x) := by
  let V := fun y => CotangentLogCoframe.j d (HyperbolicChart.differential d (f ∘ ψ) y)
  let W := fun y => CotangentLogCoframe.j d (HyperbolicChart.differential d f y)
  have hj : ContDiff ℝ (⊤ : ℕ∞) (CotangentLogCoframe.j d) :=
    (CotangentLogCoframe.j d).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ |>.contDiff
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := hj.comp (smooth_differential d _ (hf.comp hψ))
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := hj.comp (smooth_differential d _ hf)
  have hp (y : HyperbolicChart.Space d) (u : HyperbolicChart.Space d) :
      ∑ ik, W (ψ y) ik * ((CotangentLogCoframe.C d (ψ y) (fderiv ℝ ψ y u)) ik : ℂ) =
      ∑ ik, V y ik * ((CotangentLogCoframe.C d y u) ik : ℂ) := by
    rw [differential_evaluation, differential_evaluation, fderiv_comp y
      (hf.differentiable (by simp) _ ) (hψ.differentiable (by simp) _)]
    rfl
  have ht := coframe_codifferential_isometry d ψ V W x
    (hψ.contDiffAt.of_le (by simp)) hV.contDiffAt hW.contDiffAt
    (Eventually.of_forall (hm ·)) (Eventually.of_forall hp)
  have hA : (CotangentLogCoframe.j d).symm ∘ V = HyperbolicChart.differential d (f ∘ ψ) := by
    funext y; exact (CotangentLogCoframe.j d).symm_apply_apply _
  have hB : (CotangentLogCoframe.j d).symm ∘ W = HyperbolicChart.differential d f := by
    funext y; exact (CotangentLogCoframe.j d).symm_apply_apply _
  rw [hA,hB, HyperbolicChart.codifferential_differential d hd _ hf,
    HyperbolicChart.codifferential_differential d hd _ (hf.comp hψ)] at ht
  exact ht.symm

theorem derivative_control_isometry (d : ℕ) (hd : 1 ≤ d)
    (ψ : HyperbolicChart.Space d → HyperbolicChart.Space d)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hm : ∀ x u v, HyperbolicChart.metric d (ψ x) (fderiv ℝ ψ x u)
      (fderiv ℝ ψ x v) = HyperbolicChart.metric d x u v)
    (f : HyperbolicChart.Space d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : HyperbolicChart.Space d) :
    Real.sqrt (∑ i, ∑ k, ‖HyperbolicChart.differential d (f ∘ ψ) x i k‖ ^ 2) +
      ‖HyperbolicChart.laplacian d (f ∘ ψ) x‖ =
    Real.sqrt (∑ i, ∑ k, ‖HyperbolicChart.differential d f (ψ x) i k‖ ^ 2) +
      ‖HyperbolicChart.laplacian d f (ψ x)‖ := by
  rw [differential_norm_isometry d ψ x (hψ.differentiable (by simp) _)
    (hm x) f (hf.differentiable (by simp) _), laplacian_isometry d hd ψ hψ hm f hf x]

def actionCoordinates (F : Type) [Field F] [NumberField F]
    (γ : KPCuspArithmetic.PGL2 F) (x : HyperbolicChart.Space (KPCuspLogShape.dimension F)) :=
  (CotangentLogCoframe.A _).symm (γ • CotangentLogCoframe.A _ x)

private theorem action_smooth_metric (F : Type) [Field F] [NumberField F]
    (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (actionCoordinates F γ) ∧
      ∀ x u v, HyperbolicChart.metric (KPCuspLogShape.dimension F) (actionCoordinates F γ x)
        (fderiv ℝ (actionCoordinates F γ) x u) (fderiv ℝ (actionCoordinates F γ) x v) =
        HyperbolicChart.metric (KPCuspLogShape.dimension F) x u v := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  let n := KPCuspLogShape.dimension F
  let A := CotangentLogCoframe.A n
  let g := fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F k).embedding B
  have he : actionCoordinates F (Matrix.ProjGenLinGroup.mk B) =
      fun x => A.symm (KPArch.productAction n g (A x)) := by
    funext x
    unfold actionCoordinates
    change A.symm (KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk B) (A x)) = _
    rw [KPCuspSiegel.action_mk]
    rfl
  rw [he]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => A.symm (KPArch.productAction n g (A x))) :=
    A.symm.contDiff.comp (((KPArch.productAction_contDiff n g).of_le
      (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top)).comp A.contDiff)
  refine ⟨hs, ?_⟩
  have hquad : ∀ x v, HyperbolicChart.metric n (A.symm (KPArch.productAction n g (A x)))
      (fderiv ℝ (fun x => A.symm (KPArch.productAction n g (A x))) x v)
      (fderiv ℝ (fun x => A.symm (KPArch.productAction n g (A x))) x v) =
      HyperbolicChart.metric n x v v := by
    intro x v
    have hder := A.symm.hasFDerivAt.comp x
      (((KPArch.productAction_contDiff n g).differentiable (by simp) (A x)).hasFDerivAt.comp x
        A.hasFDerivAt)
    change HasFDerivAt (fun x => A.symm (KPArch.productAction n g (A x))) _ x at hder
    rw [← CotangentLogCoframe.metric_A, hder.fderiv]
    change KPArch.metric n (A (A.symm (KPArch.productAction n g (A x))))
      (A ((A.symm.toContinuousLinearMap.comp
        ((fderiv ℝ (KPArch.productAction n g) (A x)).comp A.toContinuousLinearMap)) v)) = _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    exact (KPArch.metric_invariant n g (A x) (A v)).trans (CotangentLogCoframe.metric_A n x v)
  have hpolar : ∀ x u w, HyperbolicChart.metric n x (u+w) (u+w) =
      HyperbolicChart.metric n x u u + 2 * HyperbolicChart.metric n x u w +
        HyperbolicChart.metric n x w w := by
    intro x u w
    simp only [← CotangentLogCoframe.inner_C, map_add, inner_add_left, inner_add_right,
      real_inner_comm (CotangentLogCoframe.C n x w) (CotangentLogCoframe.C n x u)]
    ring
  intro x v w
  have hp := hquad x (v+w)
  rw [map_add, hpolar, hpolar, hquad x v, hquad x w] at hp
  linarith

theorem translated_transition_action_bound (F : Type) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ (shift : ℝ) (γ : KPCuspArithmetic.PGL2 F)
      (x : HyperbolicChart.Space (KPCuspLogShape.dimension F)),
      let f := fun q => (Real.smoothTransition
        (RadialProfile.mean (KPCuspLogShape.dimension F) (actionCoordinates F γ q) - shift) : ℂ)
      Real.sqrt (∑ i, ∑ k, ‖HyperbolicChart.differential (KPCuspLogShape.dimension F) f x i k‖ ^ 2) +
        ‖HyperbolicChart.laplacian (KPCuspLogShape.dimension F) f x‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := RadialProfile.translated_transition_bound _ hd
  refine ⟨B,hB, ?_⟩
  intro shift γ x
  let f := fun q => (Real.smoothTransition
    (RadialProfile.mean (KPCuspLogShape.dimension F) q - shift) : ℂ)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp ((RadialProfile.mean _).contDiff.sub contDiff_const))
  have hs := action_smooth_metric F γ
  change Real.sqrt (∑ i, ∑ k, ‖HyperbolicChart.differential (KPCuspLogShape.dimension F)
    (f ∘ actionCoordinates F γ) x i k‖ ^ 2) +
      ‖HyperbolicChart.laplacian (KPCuspLogShape.dimension F) (f ∘ actionCoordinates F γ) x‖ ≤ B
  rw [derivative_control_isometry _ hd (actionCoordinates F γ) hs.1 hs.2 f hf x]
  exact hbound shift (actionCoordinates F γ x)
end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.ScalarIsometry

end

end

section
noncomputable section
open scoped Classical NumberField ContDiff BigOperators
open Filter Topology Real
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.CutoffBounds
open HyperbolicChart
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
variable (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

private theorem differential_congr (d : ℕ) {f g : Space d → ℂ} {x : Space d}
    (h : f =ᶠ[nhds x] g) (i : Fin d) (k : Fin 3) :
    differential d f x i k = differential d g x i k := by
  unfold differential coordinateDerivative
  rw [h.fderiv_eq]

private theorem mean_fromArch (x : Arch F) :
    RadialProfile.mean (KPCuspLogShape.dimension F) (fromArch F x) =
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x := by
  simp [RadialProfile.mean_apply, fromArch, KPCuspLogShape.meanHeight, div_eq_mul_inv, mul_comm]

private theorem A_eq : (CotangentLogCoframe.A (KPCuspLogShape.dimension F) : Coordinates F → Arch F) = toArch F := by
  funext p i
  apply Prod.ext
  · apply Complex.ext <;> simp [CotangentLogCoframe.A, toArch]
  · rfl

private theorem action_mean (γ : KPCuspArithmetic.PGL2 F) (q : Coordinates F) :
    RadialProfile.mean (KPCuspLogShape.dimension F) (ScalarIsometry.actionCoordinates F γ q) =
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (γ • toArch F q) := by
  change RadialProfile.mean _ (fromArch F (γ • CotangentLogCoframe.A _ q)) = _
  rw [mean_fromArch, A_eq]

private theorem coord_zero (d : ℕ) (j : Fin d) (k : Fin 3) : coordinateDerivative d j k 0 = 0 := by
  funext p
  simp [coordinateDerivative]

 def etaLift (n : ℕ) (c : CutoffScalars.Cusp a) (i : Fin a.componentCount) :
    Coordinates F → ℂ :=
  fun p => (CutoffScalars.eta a n c (basePoint F ζ hζ hF U a i (toArch F p)) : ℂ)

private theorem etaLift_smooth (n : ℕ) (c : CutoffScalars.Cusp a) (i : Fin a.componentCount) :
    ContDiff ℝ (⊤ : ℕ∞) (etaLift a n c i) := by
  have he := (GenericZeroExtension.scalar_zeroExtension_smooth_continuous a a.threshold
    (a.threshold + 1) le_rfl (by linarith) c
    (fun t => smoothTransition (t - CutoffScalars.shift a n))
    (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
    (by intro t ht; apply smoothTransition.zero_of_nonpos
        have hh := le_max_right (n : ℝ) (a.threshold + 1)
        dsimp [CutoffScalars.shift]; linarith)).1 i
  exact Complex.ofRealCLM.contDiff.comp (he.comp (cutoff_toArch_contDiff F))

private theorem eta_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ n c i (p : Coordinates F),
    sqrt (∑ j, ∑ k, ‖differential (KPCuspLogShape.dimension F) (etaLift a n c i) p j k‖ ^ 2) +
      ‖laplacian (KPCuspLogShape.dimension F) (etaLift a n c i) p‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := ScalarIsometry.translated_transition_action_bound F
    (KPCuspLogShape.dimension_pos F hF)
  refine ⟨B,hB, ?_⟩
  intro n c i p
  have hm := CutoffScalars.eta_local_model a n c i (toArch F p)
  rcases hm with hz | ⟨γ,hγ⟩
  · have he : etaLift a n c i =ᶠ[nhds p] 0 := by
      have hh := hz.comp_tendsto ((cutoff_toArch_contDiff F).continuous.tendsto p)
      exact hh.mono fun q hq => by simpa [etaLift, basePoint] using congrArg (fun t : ℝ => (t : ℂ)) hq
    have hd : ∀ j k, differential (KPCuspLogShape.dimension F) (etaLift a n c i) p j k = 0 := by
      intro j k
      rw [differential_congr _ he]
      fin_cases k <;> simp [differential, coordinateDerivative]
    rw [laplacian_congr_nhds _ he]
    simpa [hd, laplacian, coord_zero] using hB
  · have he : etaLift a n c i =ᶠ[nhds p]
        (fun q => (smoothTransition (RadialProfile.mean (KPCuspLogShape.dimension F)
          (ScalarIsometry.actionCoordinates F γ q) - CutoffScalars.shift a n) : ℂ)) := by
      have hh := hγ.comp_tendsto ((cutoff_toArch_contDiff F).continuous.tendsto p)
      apply hh.mono
      intro q hq
      simpa only [etaLift, basePoint, action_mean, Function.comp_apply] using
        congrArg (fun t : ℝ => (t : ℂ)) hq
    have hd (j) (k) := differential_congr _ he j k
    simp_rw [hd]
    rw [laplacian_congr_nhds _ he]
    exact hbound (CutoffScalars.shift a n) γ p

private theorem coord_sum {C : Type*} [Fintype C] (d : ℕ) (f : C → Space d → ℂ)
    (hf : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (f c)) (j : Fin d) (k : Fin 3) :
    coordinateDerivative d j k (fun p => ∑ c, f c p) =
      fun p => ∑ c, coordinateDerivative d j k (f c) p := by
  funext p
  unfold coordinateDerivative
  rw [fderiv_fun_sum (fun c _ => (hf c).differentiable (by simp) p)]
  simp

private theorem lap_sum {C : Type*} [Fintype C] (d : ℕ) (f : C → Space d → ℂ)
    (hf : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (f c)) (p : Space d) :
    laplacian d (fun q => ∑ c, f c q) p = ∑ c, laplacian d (f c) p := by
  have hdf (j : Fin d) (k : Fin 3) (c : C) :
      ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative d j k (f c)) :=
    ((hf c).fderiv_right (by simp)).clm_apply contDiff_const
  simp only [laplacian, coord_sum d f hf, coord_sum d _ (hdf _ _)]
  rw [Finset.sum_comm (f := fun c j =>
    -coordinateDerivative d j 2 (coordinateDerivative d j 2 (f c)) p +
      2 * coordinateDerivative d j 2 (f c) p -
      (Real.exp (2 * p (j,2)) : ℂ) *
        (coordinateDerivative d j 0 (coordinateDerivative d j 0 (f c)) p +
          coordinateDerivative d j 1 (coordinateDerivative d j 1 (f c)) p))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.mul_sum, mul_add]

private theorem coord_const_sub (d : ℕ) (f : Space d → ℂ) (j : Fin d) (k : Fin 3) :
    coordinateDerivative d j k (fun q => 1 - f q) = -coordinateDerivative d j k f := by
  funext p
  simp [coordinateDerivative, fderiv_const_sub]

private theorem lap_const_sub (d : ℕ) (f : Space d → ℂ) (p : Space d) :
    laplacian d (fun q => 1 - f q) p = -laplacian d f p := by
  have hn (j : Fin d) (k : Fin 3) :
      coordinateDerivative d j k (-coordinateDerivative d j k f) =
        -coordinateDerivative d j k (coordinateDerivative d j k f) := by
    funext q
    unfold coordinateDerivative
    rw [fderiv_neg]
    rfl
  simp only [laplacian, coord_const_sub, hn]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.neg_apply]
  ring

 def diffVec (d : ℕ) (f : Space d → ℂ) (p : Space d) :
    EuclideanSpace ℂ (Fin d × Fin 3) := WithLp.toLp 2 (fun jk => differential d f p jk.1 jk.2)

private theorem diffVec_norm (d : ℕ) (f : Space d → ℂ) (p : Space d) :
    ‖diffVec d f p‖ = sqrt (∑ j, ∑ k, ‖differential d f p j k‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  rfl

private theorem diffVec_const_sub_sum {C : Type*} [Fintype C] (d : ℕ) (f : C → Space d → ℂ)
    (hf : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (f c)) (p : Space d) :
    diffVec d (fun q => 1 - ∑ c, f c q) p = -∑ c, diffVec d (f c) p := by
  ext ⟨j,k⟩
  fin_cases k <;>
    simp [diffVec, differential, coord_const_sub, coord_sum d f hf, Finset.mul_sum]

theorem rho_derivative_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ n i x,
    scalarGradientNorm F ζ hζ hF U a (CutoffScalars.rho a n) i x +
      ‖scalarLaplacian F ζ hζ hF U a (CutoffScalars.rho a n) i x‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := eta_bound a
  refine ⟨Fintype.card (CutoffScalars.Cusp a) * B, mul_nonneg (Nat.cast_nonneg _) hB, ?_⟩
  intro n i x
  let f := fun c => etaLift a n c i
  have hf := fun c => etaLift_smooth a n c i
  have he : scalarLift F ζ hζ hF U a (CutoffScalars.rho a n) i =
      fun p => 1 - ∑ c, f c p := by
    funext p
    simp [scalarLift, CutoffScalars.rho, f, etaLift]
  change sqrt (∑ j, ∑ k, ‖differential (KPCuspLogShape.dimension F) _ (fromArch F x) j k‖ ^ 2) +
    ‖laplacian (KPCuspLogShape.dimension F) _ (fromArch F x)‖ ≤ _
  rw [he, ← diffVec_norm, diffVec_const_sub_sum _ f hf,
    lap_const_sub, lap_sum _ f hf, norm_neg, norm_neg]
  calc
    _ ≤ (∑ c, ‖diffVec _ (f c) (fromArch F x)‖) +
        ∑ c, ‖laplacian _ (f c) (fromArch F x)‖ :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ = ∑ c, (‖diffVec _ (f c) (fromArch F x)‖ +
        ‖laplacian _ (f c) (fromArch F x)‖) := (Finset.sum_add_distrib).symm
    _ ≤ ∑ _c : CutoffScalars.Cusp a, B := by
      apply Finset.sum_le_sum
      intro c _
      rw [diffVec_norm]
      exact hb n c i (fromArch F x)
    _ = _ := by simp

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.CutoffBounds

end

end
