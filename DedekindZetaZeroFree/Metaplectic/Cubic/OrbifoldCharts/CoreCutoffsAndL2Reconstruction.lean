module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LineBundles.MeasurableOrthonormalFrames
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.EllipticityAndCutoffs
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LineBundles.UnitaryFrameComparison
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.SectionSpaces.PartitionReconstruction

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree
namespace KPCoreChartLocalizers

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

abbrev X := KPFiniteCuspAtlas.rawXU F ζ hζ U
abbrev V := KPCuspGenuineMonodromy.scalarFiber F ζ hζ U

instance : MeasurableSpace (X F ζ hζ U) := borel _

def quotientMeasure (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    Measure (X F ζ hζ U) :=
  ∑ i : Fin A.componentCount,
    Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
      (KPFiniteCuspAtlas.quotientVolume F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
        (A.cuspAtlas i).fundamentalDomain)

abbrev Line (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :=
  Σ i : Fin A.componentCount, KPCuspGenuineMonodromy.OrbifoldLine F ζ hζ U
    (A.representative i) (A.line i).rho

def lineBase (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    Line F ζ hζ hF U A → X F ζ hζ U := fun p =>
  Quotient.lift (fun q => KPFiniteCuspAtlas.componentMap F ζ hζ U
    (A.representative p.1) (KPCuspSiegel.projection F _ q.1)) (by
      intro q q' h
      obtain ⟨γ, hbase, _⟩ := h
      rw [hbase]
      apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative p.1))
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, by
        change γ⁻¹ • (γ • q.1) = q.1
        simp⟩) p.2

structure Realization (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) where
  component : X F ζ hζ U → Fin A.componentCount
  lift : X F ζ hζ U → KPFiniteCuspAtlas.SymmetricSpace F
  measurable_component : Measurable component
  measurable_lift : Measurable lift
  lift_formula : ∀ x, KPFiniteCuspAtlas.componentMap F ζ hζ U
    (A.representative (component x))
    (KPCuspSiegel.projection F _ (lift x)) = x
  lift_in_domain : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A,
    lift x ∈ (A.cuspAtlas (component x)).fundamentalDomain
  free_ae : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A,
    ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U
      (A.representative (component x)),
      (γ : KPCuspArithmetic.PGL2 F) • lift x = lift x → γ = 1

  representative : KPFiniteCuspAtlas.genuineScalars F ζ hζ U →ₗ[ℂ]
    (X F ζ hζ U → V F ζ hζ U)
  section_formula : ∀ s x, (representative s x : ℂ) =
    s.val (lift x, A.representative (component x))

  frame : (x : X F ζ hζ U) → V F ζ hζ U → Line F ζ hζ hF U A
  frame_formula : ∀ x a, frame x a =
    ⟨component x, Quotient.mk _ (lift x, a)⟩
  frame_base : ∀ x a, lineBase F ζ hζ hF U A (frame x a) = x
  frame_injective_ae : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A,
    Function.Injective (frame x)
  frame_surjective_ae : ∀ᵐ x ∂quotientMeasure F ζ hζ hF U A,
    ∀ l : Line F ζ hζ hF U A, lineBase F ζ hζ hF U A l = x →
      ∃ a, frame x a = l

  smooth_test_memLp : ∀ s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U,
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => s.val (z, A.representative i))) →
    HasCompactSupport (representative s) →
    MemLp (representative s) 2 (quotientMeasure F ζ hζ hF U A)

abbrev H (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :=
  Lp (V F ζ hζ U) 2 (quotientMeasure F ζ hζ hF U A)

abbrev HK (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (K : Set (X F ζ hζ U)) :=
  Lp (V F ζ hζ U) 2 ((quotientMeasure F ζ hζ hF U A).restrict K)

def restriction (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (K : Set (X F ζ hζ U)) :
    H F ζ hζ hF U A →L[ℂ] HK F ζ hζ hF U A K :=
  LpToLpRestrictCLM (X F ζ hζ U) (V F ζ hζ U) ℂ
    (quotientMeasure F ζ hζ hF U A) 2 K

theorem restriction_formula (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (K : Set (X F ζ hζ U)) (v : H F ζ hζ hF U A) :
    restriction F ζ hζ hF U A K v
      =ᵐ[(quotientMeasure F ζ hζ hF U A).restrict K] v :=
  LpToLpRestrictCLM_coeFn ℂ K v

theorem norm_restriction_le (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (K : Set (X F ζ hζ U)) (v : H F ζ hζ hF U A) :
    ‖restriction F ζ hζ hF U A K v‖ ≤ ‖v‖ :=
  norm_Lp_toLp_restrict_le K v

def core (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) : Set (H F ζ hζ hF U A) :=
  {v | ∃ s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U,
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => s.val (z, A.representative i))) ∧
    HasCompactSupport (M.representative s) ∧
    (v : X F ζ hζ U → V F ζ hζ U) =ᵐ[quotientMeasure F ζ hζ hF U A]
      M.representative s}

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cube (n : ℕ) (a : ℝ) : Set (E n) := {x | ∀ j, -a ≤ x j ∧ x j ≤ a}

structure Chart (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) where
  n : ℕ
  positive_n : 0 < n
  dimension : n = 3 * KPCuspLogShape.dimension F
  a : ℝ
  positive_a : 0 < a
  radius : ℝ
  positive_radius : 0 < radius
  closed_ball_in_cube : closure (Metric.ball (0 : E n) radius) ⊆ interior (cube n a)
  component : Fin A.componentCount
  center : KPFiniteCuspAtlas.SymmetricSpace F
  finite_stabilizer : Fintype (MulAction.stabilizer
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative component)) center)
  orthogonal : MulAction.stabilizer
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative component)) center →*
      (E n ≃ₗᵢ[ℝ] E n)
  extendedDomain : Set (E n)
  open_extendedDomain : IsOpen extendedDomain
  closed_ball_in_extension : closure (Metric.ball (0 : E n) radius) ⊆ extendedDomain
  invariant_extension : ∀ g, orthogonal g '' extendedDomain = extendedDomain
  coordinates : E n → KPFiniteCuspAtlas.SymmetricSpace F
  coordinates_center : coordinates 0 = center
  smooth_coordinates : ContDiffOn ℝ (⊤ : ℕ∞) coordinates extendedDomain
  coordinates_embedding : Topology.IsEmbedding (Set.restrict extendedDomain coordinates)
  coordinates_open : IsOpen (coordinates '' extendedDomain)
  smooth_inverse : ∃ inv : KPFiniteCuspAtlas.SymmetricSpace F → E n,
    ContDiffOn ℝ (⊤ : ℕ∞) inv (coordinates '' extendedDomain) ∧
    (∀ x ∈ extendedDomain, inv (coordinates x) = x)
  equivariance : ∀ g x, x ∈ extendedDomain →
    coordinates (orthogonal g x) =
      ((g.val : KPCuspArithmetic.PGL2 F) • coordinates x)

  separated : ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U
      (A.representative component), ∀ x y,
    x ∈ extendedDomain → y ∈ extendedDomain →
    (γ : KPCuspArithmetic.PGL2 F) • coordinates x = coordinates y →
      γ ∈ MulAction.stabilizer _ center
  weight : E n → ℝ
  smooth_weight : ContDiffOn ℝ (⊤ : ℕ∞) weight extendedDomain
  invariant_weight : ∀ g x, x ∈ extendedDomain → weight (orthogonal g x) = weight x
  lower : ℝ
  upper : ℝ
  positive_lower : 0 < lower
  finite_bounds : ∀ x ∈ closure (Metric.ball (0 : E n) radius),
    lower ≤ weight x ∧ weight x ≤ upper

  coordinate_volume : Measure.map coordinates
    ((volume.restrict (Metric.ball (0 : E n) radius)).withDensity
      (fun x => ENNReal.ofReal (weight x))) =
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
      (coordinates '' Metric.ball (0 : E n) radius)

attribute [instance] Chart.finite_stabilizer

abbrev Chart.G {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) :=
  MulAction.stabilizer (KPCuspGenuineMonodromy.Component F ζ hζ U
    (A.representative C.component)) C.center

def Chart.rho {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) : C.G F ζ hζ hF U →* ℂˣ :=
  (KPCuspGenuineMonodromy.chi F ζ hζ).comp
    ((A.line C.component).rho.comp (MulAction.stabilizer _ C.center).subtype)

theorem Chart.rho_unitary {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) (g : C.G F ζ hζ hF U) :
    ‖(C.rho F ζ hζ hF U g : ℂ)‖ = 1 := by
  exact (A.line C.component).unitary _

theorem Chart.section_equivariance {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A)
    (s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U)
    (g : C.G F ζ hζ hF U) {x : E C.n} (hx : x ∈ C.extendedDomain) :
    s.val (C.coordinates (C.orthogonal g x), A.representative C.component) =
      (C.rho F ζ hζ hF U g : ℂ) *
        s.val (C.coordinates x, A.representative C.component) := by
  rw [C.equivariance g x hx]
  have h := (A.scalar_realization s C.component).property.2 g.val (C.coordinates x)
  simpa only [A.scalar_realization_formula, Chart.rho, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using h

def Chart.toBase {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) (x : E C.n) : X F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)
    (KPCuspSiegel.projection F _ (C.coordinates x))

def Chart.toLine {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) (x : E C.n) (a : V F ζ hζ U) :
    Line F ζ hζ hF U A :=
  ⟨C.component, Quotient.mk _ (C.coordinates x, a)⟩

def Chart.lineRelation {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) :
    Setoid (Metric.ball (0 : E C.n) C.radius × V F ζ hζ U) :=
  Setoid.ker (fun p => C.toLine F ζ hζ hF U p.1.val p.2)

def Chart.O {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) : Set (X F ζ hζ U) :=
  C.toBase F ζ hζ hF U '' Metric.ball 0 C.radius

def Chart.relation {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) : Setoid (Metric.ball (0 : E C.n) C.radius) :=
  Setoid.ker (fun x => C.toBase F ζ hζ hF U x.val)

def Chart.average {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) (f : E C.n → ℂ) : E C.n → ℂ :=
  (Metric.ball 0 C.radius).indicator (fun x =>
    (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹ *
      ∑ g : C.G F ζ hζ hF U, ((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) *
        f (C.orthogonal g x))

def Chart.metricMatrix {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) (x : E C.n) : Matrix (Fin C.n) (Fin C.n) ℝ :=
  fun j k =>
    (KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)) -
    KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single j 1)) -
    KPArch.metric (KPCuspLogShape.dimension F) (C.coordinates x)
      (fderiv ℝ C.coordinates x (EuclideanSpace.single k 1))) / 2

def Chart.energyMatrix {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}
    (C : Chart F ζ hζ hF U A) (x : E C.n) : Matrix (Fin C.n) (Fin C.n) ℝ :=
  (C.metricMatrix F ζ hζ hF U x)⁻¹

section ChartFacts

variable {A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U} (C : Chart F ζ hζ hF U A)
theorem Chart.orthogonal_mem_ball (g : C.G F ζ hζ hF U) (x : E C.n) :
    C.orthogonal g x ∈ Metric.ball 0 C.radius ↔ x ∈ Metric.ball 0 C.radius := by
  simp only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
theorem Chart.average_eq_self (f : E C.n → ℂ)
    (heq : ∀ (g : C.G F ζ hζ hF U) x, x ∈ Metric.ball 0 C.radius →
      f (C.orthogonal g x) = (C.rho F ζ hζ hF U g : ℂ) * f x)
    {x : E C.n} (hx : x ∈ Metric.ball 0 C.radius) :
    C.average F ζ hζ hF U f x = f x := by
  rw [Chart.average, Set.indicator_of_mem hx]
  have hs : (∑ g : C.G F ζ hζ hF U,
      (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g x)) =
      (Fintype.card (C.G F ζ hζ hF U) : ℂ) * f x := by
    simp [heq _ _ hx, ← mul_assoc]
  rw [hs, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
theorem Chart.average_zero_outside (f : E C.n → ℂ)
    {x : E C.n} (hx : x ∉ Metric.ball 0 C.radius) :
    C.average F ζ hζ hF U f x = 0 := by
  exact Set.indicator_of_notMem hx _

theorem Chart.average_equivariant (f : E C.n → ℂ)
    (h : C.G F ζ hζ hF U) (x : E C.n) :
    C.average F ζ hζ hF U f (C.orthogonal h x) =
      (C.rho F ζ hζ hF U h : ℂ) * C.average F ζ hζ hF U f x := by
  by_cases hx : x ∈ Metric.ball 0 C.radius
  · rw [Chart.average, Set.indicator_of_mem ((C.orthogonal_mem_ball F ζ hζ hF U h x).mpr hx),
      Set.indicator_of_mem hx]
    have hs : (∑ g : C.G F ζ hζ hF U,
        (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g (C.orthogonal h x))) =
        (C.rho F ζ hζ hF U h : ℂ) *
        ∑ g : C.G F ζ hζ hF U,
          (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g x) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_equiv (Equiv.mulRight h)
      intro g
      change (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) *
        f (C.orthogonal g (C.orthogonal h x)) =
        (C.rho F ζ hζ hF U h : ℂ) *
          ((((C.rho F ζ hζ hF U (g * h))⁻¹ : ℂˣ) : ℂ) *
            f (C.orthogonal (g * h) x))
      simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
        mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
      have hn := Units.ne_zero (C.rho F ζ hζ hF U h)
      field_simp
    rw [hs]
    ring
  · rw [C.average_zero_outside F ζ hζ hF U f hx,
      C.average_zero_outside F ζ hζ hF U f
        (fun hh => hx ((C.orthogonal_mem_ball F ζ hζ hF U h x).mp hh)), mul_zero]

theorem Chart.average_idempotent (f : E C.n → ℂ) :
    C.average F ζ hζ hF U (C.average F ζ hζ hF U f) =
      C.average F ζ hζ hF U f := by
  funext x
  by_cases hx : x ∈ Metric.ball 0 C.radius
  · exact C.average_eq_self F ζ hζ hF U _
      (fun g y _ => C.average_equivariant F ζ hζ hF U f g y) hx
  · exact (C.average_zero_outside F ζ hζ hF U _ hx).trans
      (C.average_zero_outside F ζ hζ hF U _ hx).symm

theorem Chart.norm_average_le (f : E C.n → ℂ) (x : E C.n) :
    ‖C.average F ζ hζ hF U f x‖ ≤
      (Fintype.card (C.G F ζ hζ hF U) : ℝ)⁻¹ *
        ∑ g : C.G F ζ hζ hF U, ‖f (C.orthogonal g x)‖ := by
  by_cases hx : x ∈ Metric.ball 0 C.radius
  · rw [Chart.average, Set.indicator_of_mem hx, norm_mul, norm_inv,
      Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    calc
      _ ≤ ∑ g : C.G F ζ hζ hF U,
          ‖(((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) * f (C.orthogonal g x)‖ :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv,
          C.rho_unitary F ζ hζ hF U g, inv_one, one_mul]
  · rw [C.average_zero_outside F ζ hζ hF U f hx, norm_zero]
    positivity
theorem Chart.invariant_ball :
    ∀ g : C.G F ζ hζ hF U,
      C.orthogonal g '' Metric.ball 0 C.radius = Metric.ball 0 C.radius := by
  intro g
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (C.orthogonal_mem_ball F ζ hζ hF U g y).mpr hy
  · intro hx
    refine ⟨(C.orthogonal g).symm x, ?_, (C.orthogonal g).apply_symm_apply x⟩
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
      using hx

theorem Chart.toBase_invariant (g : C.G F ζ hζ hF U) (x : E C.n)
    (hx : x ∈ C.extendedDomain) :
    C.toBase F ζ hζ hF U (C.orthogonal g x) = C.toBase F ζ hζ hF U x := by
  unfold Chart.toBase
  rw [C.equivariance g x hx]
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component))
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact MulAction.mem_orbit_iff.mpr ⟨g.val, rfl⟩

theorem Chart.orbit_relation (x y : Metric.ball (0 : E C.n) C.radius) :
    (C.relation F ζ hζ hF U).r x y ↔
      ∃ g : C.G F ζ hζ hF U, C.orthogonal g x.val = y.val := by
  have hx : x.val ∈ C.extendedDomain :=
    C.closed_ball_in_extension (subset_closure x.property)
  have hy : y.val ∈ C.extendedDomain :=
    C.closed_ball_in_extension (subset_closure y.property)
  constructor
  · intro h
    change C.toBase F ζ hζ hF U x.val = C.toBase F ζ hζ hF U y.val at h
    have hb : KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
        (C.coordinates x.val) =
        KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
          (C.coordinates y.val) := by
      have he := A.components.injective
        ((A.components_formula _ _).trans (h.trans (A.components_formula _ _).symm))
      exact eq_of_heq (Sigma.mk.inj he).2
    have ho := MulAction.orbitRel_apply.mp (Quotient.exact hb)
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp ho
    have hγ' : ((γ⁻¹ : KPCuspGenuineMonodromy.Component F ζ hζ U
        (A.representative C.component)) : KPCuspArithmetic.PGL2 F) •
        C.coordinates x.val = C.coordinates y.val := by
      change γ⁻¹ • C.coordinates x.val = C.coordinates y.val
      rw [← hγ]
      simp
    have hstab : γ⁻¹ ∈ MulAction.stabilizer _ C.center :=
      C.separated γ⁻¹ x.val y.val hx hy hγ'
    let g : C.G F ζ hζ hF U := ⟨γ⁻¹, hstab⟩
    have hgx : C.orthogonal g x.val ∈ C.extendedDomain := by
      rw [← C.invariant_extension g]
      exact ⟨x.val, hx, rfl⟩
    refine ⟨g, ?_⟩
    apply congrArg Subtype.val
      (C.coordinates_embedding.injective (a₁ := ⟨C.orthogonal g x.val, hgx⟩)
        (a₂ := ⟨y.val, hy⟩) ?_)
    change C.coordinates (C.orthogonal g x.val) = C.coordinates y.val
    rw [C.equivariance g x.val hx]
    exact hγ'
  · rintro ⟨g, h⟩
    change C.toBase F ζ hζ hF U x.val = C.toBase F ζ hζ hF U y.val
    rw [← h]
    exact (C.toBase_invariant F ζ hζ hF U g x.val hx).symm
theorem Chart.lineBase_toLine (x : E C.n) (a : V F ζ hζ U) :
    lineBase F ζ hζ hF U A (C.toLine F ζ hζ hF U x a) =
      C.toBase F ζ hζ hF U x := rfl

theorem Chart.toLine_equivariant (g : C.G F ζ hζ hF U) (x : E C.n)
    (hx : x ∈ C.extendedDomain) (a b : V F ζ hζ U)
    (hab : (b : ℂ) = (C.rho F ζ hζ hF U g : ℂ) * (a : ℂ)) :
    C.toLine F ζ hζ hF U (C.orthogonal g x) b =
      C.toLine F ζ hζ hF U x a := by
  apply congrArg (Sigma.mk C.component)
  apply Eq.symm
  apply Quotient.sound
  exact ⟨g.val, C.equivariance g x hx, hab⟩

theorem Chart.line_orbit_relation (x y : Metric.ball (0 : E C.n) C.radius)
    (a b : V F ζ hζ U) :
    (C.lineRelation F ζ hζ hF U).r (x,a) (y,b) ↔
      ∃ g : C.G F ζ hζ hF U,
        C.orthogonal g x.val = y.val ∧
        (b : ℂ) = (C.rho F ζ hζ hF U g : ℂ) * (a : ℂ) := by
  have hx : x.val ∈ C.extendedDomain :=
    C.closed_ball_in_extension (subset_closure x.property)
  have hy : y.val ∈ C.extendedDomain :=
    C.closed_ball_in_extension (subset_closure y.property)
  constructor
  · intro h
    change C.toLine F ζ hζ hF U x.val a = C.toLine F ζ hζ hF U y.val b at h
    have hl : Quotient.mk (KPCuspGenuineMonodromy.flatLineRelation F ζ hζ U
        (A.representative C.component) (A.line C.component).rho) (C.coordinates x.val, a) =
        Quotient.mk _ (C.coordinates y.val, b) :=
      eq_of_heq (Sigma.mk.inj h).2
    obtain ⟨γ, hγ, hab⟩ := Quotient.exact hl
    have hstab := C.separated γ x.val y.val hx hy hγ.symm
    let g : C.G F ζ hζ hF U := ⟨γ, hstab⟩
    refine ⟨g, ?_, hab⟩
    have hgx : C.orthogonal g x.val ∈ C.extendedDomain := by
      rw [← C.invariant_extension g]
      exact ⟨x.val, hx, rfl⟩
    apply congrArg Subtype.val
      (C.coordinates_embedding.injective (a₁ := ⟨C.orthogonal g x.val, hgx⟩)
        (a₂ := ⟨y.val, hy⟩) ?_)
    change C.coordinates (C.orthogonal g x.val) = C.coordinates y.val
    rw [C.equivariance g x.val hx]
    exact hγ.symm
  · rintro ⟨g, hxy, hab⟩
    change C.toLine F ζ hζ hF U x.val a = C.toLine F ζ hζ hF U y.val b
    rw [← hxy]
    exact (C.toLine_equivariant F ζ hζ hF U g x.val hx a b hab).symm

theorem Chart.line_chart_surjective (l : Line F ζ hζ hF U A)
    (hl : lineBase F ζ hζ hF U A l ∈ C.O F ζ hζ hF U) :
    ∃ (x : Metric.ball (0 : E C.n) C.radius) (a : V F ζ hζ U),
      C.toLine F ζ hζ hF U x.val a = l := by
  obtain ⟨x, hx, hxl⟩ := hl
  obtain ⟨j, l⟩ := l
  induction l using Quotient.inductionOn with
  | h p =>
    have he : (⟨C.component, KPCuspSiegel.projection F _ (C.coordinates x)⟩ :
        Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) =
        ⟨j, KPCuspSiegel.projection F _ p.1⟩ := by
      apply A.components.injective
      simpa only [A.components_formula, Chart.toBase, lineBase, Quotient.lift_mk] using hxl
    have hj : C.component = j := (Sigma.mk.inj he).1
    subst j
    have hb := eq_of_heq (Sigma.mk.inj he).2
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hb))
    let a : V F ζ hζ U :=
      (KPCuspGenuineMonodromy.chi F ζ hζ ((A.line C.component).rho γ) : ℂ) • p.2
    refine ⟨⟨x, hx⟩, a, ?_⟩
    apply congrArg (Sigma.mk C.component)
    apply Eq.symm
    apply Quotient.sound
    refine ⟨γ, ?_, rfl⟩
    exact hγ.symm

theorem Chart.coordinates_open_embedding :
    IsOpenEmbedding (Set.restrict C.extendedDomain C.coordinates) := by
  refine ⟨C.coordinates_embedding, ?_⟩
  convert C.coordinates_open using 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
theorem Chart.coordinates_ball_open_map :
    IsOpenMap (Set.restrict (Metric.ball (0 : E C.n) C.radius) C.coordinates) := by
  let inc : Metric.ball (0 : E C.n) C.radius → C.extendedDomain := fun x =>
    ⟨x.val, C.closed_ball_in_extension (subset_closure x.property)⟩
  have ho : IsOpenMap inc := by
    exact (Metric.isOpen_ball.isOpenMap_subtype_val).subtype_mk _
  exact (Chart.coordinates_open_embedding F ζ hζ hF U C).isOpenMap.comp ho
theorem Chart.toBase_ball_open_map :
    IsOpenMap (Set.restrict (Metric.ball (0 : E C.n) C.radius) (C.toBase F ζ hζ hF U)) := by
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component)
  letI : ContinuousConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => KPCuspSiegel.continuous_action F g.val⟩
  have hq : IsOpenMap (KPCuspSiegel.projection F Γ) := isOpenMap_quotient_mk'_mul
  have hc : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)) := by
    have hh := A.components.isOpenMap.comp (isOpenMap_sigmaMk (i := C.component))
    simpa only [Function.comp_def, A.components_formula] using hh
  exact hc.comp (hq.comp (Chart.coordinates_ball_open_map F ζ hζ hF U C))
theorem Chart.open_image : IsOpen (C.O F ζ hζ hF U) := by
  have ho := (Chart.toBase_ball_open_map F ζ hζ hF U C).isOpen_range
  convert ho using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
theorem Chart.toBase_ball_continuous :
    Continuous (Set.restrict (Metric.ball (0 : E C.n) C.radius) (C.toBase F ζ hζ hF U)) := by
  let inc : Metric.ball (0 : E C.n) C.radius → C.extendedDomain := fun x =>
    ⟨x.val, C.closed_ball_in_extension (subset_closure x.property)⟩
  have hi : Continuous inc := continuous_subtype_val.subtype_mk _
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)) := by
    have hh := A.components.continuous.comp (continuous_sigmaMk (i := C.component))
    simpa only [Function.comp_def, A.components_formula] using hh
  exact hc.comp (continuous_quot_mk.comp (C.coordinates_embedding.continuous.comp hi))
def Chart.quotientChart : Quotient (C.relation F ζ hζ hF U) ≃ₜ C.O F ζ hζ hF U := by
  let f : Metric.ball (0 : E C.n) C.radius → C.O F ζ hζ hF U :=
    fun x => ⟨C.toBase F ζ hζ hF U x.val, Set.mem_image_of_mem _ x.property⟩
  have ho : IsOpenMap f := (Chart.toBase_ball_open_map F ζ hζ hF U C).subtype_mk _
  have hc : Continuous f := (Chart.toBase_ball_continuous F ζ hζ hF U C).subtype_mk _
  have hs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have he : C.relation F ζ hζ hF U = Setoid.ker f := by
    ext x y
    change (f x).val = (f y).val ↔ f x = f y
    exact Subtype.ext_iff.symm
  exact (Homeomorph.Quotient.congrRight (fun x y => by rw [he])).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨f, hc⟩) (ho.isQuotientMap hc hs))
theorem Chart.quotientChart_formula (x : Metric.ball (0 : E C.n) C.radius) :
    (Chart.quotientChart F ζ hζ hF U C (Quotient.mk _ x)).val =
      C.toBase F ζ hζ hF U x.val := by
  rfl

theorem Chart.measurePreserving_ball (g : C.G F ζ hζ hF U) :
    MeasurePreserving (C.orthogonal g)
      (volume.restrict (Metric.ball (0 : E C.n) C.radius))
      (volume.restrict (Metric.ball (0 : E C.n) C.radius)) := by
  have he : (C.orthogonal g) ⁻¹' Metric.ball (0 : E C.n) C.radius =
      Metric.ball (0 : E C.n) C.radius := by
    ext x
    exact C.orthogonal_mem_ball F ζ hζ hF U g x
  have hm : MeasurePreserving (C.orthogonal g) (volume : Measure (E C.n)) volume :=
    LinearIsometryEquiv.measurePreserving (C.orthogonal g)
  have hr := hm.restrict_preimage (s := Metric.ball (0 : E C.n) C.radius)
    Metric.isOpen_ball.measurableSet
  rw [he] at hr
  exact hr

def Chart.orthogonalPullback (g : C.G F ζ hζ hF U) :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) →ₗᵢ[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (C.orthogonal g)
    (Chart.measurePreserving_ball F ζ hζ hF U C g)

def Chart.averageLp :
    Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius)) :=
  (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹ •
    ∑ g : C.G F ζ hζ hF U, (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
      (Chart.orthogonalPullback F ζ hζ hF U C g).toContinuousLinearMap
theorem Chart.norm_averageLp_le
    (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius))) :
    ‖Chart.averageLp F ζ hζ hF U C f‖ ≤ ‖f‖ := by
  simp only [Chart.averageLp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (C.G F ζ hζ hF U) : ℝ)⁻¹ *
        ∑ g : C.G F ζ hζ hF U,
          ‖((((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ) •
            (Chart.orthogonalPullback F ζ hζ hF U C g).toContinuousLinearMap f)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (Fintype.card (C.G F ζ hζ hF U) : ℝ)⁻¹ *
        ((Fintype.card (C.G F ζ hζ hF U) : ℝ) * ‖f‖) := by
      congr 1
      simp only [norm_smul, Units.val_inv_eq_inv_val, norm_inv,
        C.rho_unitary F ζ hζ hF U, inv_one, one_mul,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ‖f‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
theorem Chart.averageLp_formula
    (f : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius))) :
    Chart.averageLp F ζ hζ hF U C f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
      C.average F ζ hζ hF U f := by
  let b : C.G F ζ hζ hF U → ℂ := fun g => (((C.rho F ζ hζ hF U g)⁻¹ : ℂˣ) : ℂ)
  let p := fun g : C.G F ζ hζ hF U => Chart.orthogonalPullback F ζ hζ hF U C g f
  have hp : ∀ g, (p g : E C.n → ℂ) =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
      fun x => f (C.orthogonal g x) := fun g =>
    Lp.coeFn_compMeasurePreserving f (Chart.measurePreserving_ball F ζ hζ hF U C g)
  have hb : ∀ g, ((b g • p g : Lp ℂ 2 (volume.restrict (Metric.ball (0 : E C.n) C.radius))) : E C.n → ℂ)
      =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
        fun x => b g * f (C.orthogonal g x) := by
    intro g
    exact (Lp.coeFn_smul (b g) (p g)).trans ((hp g).const_smul (b g))
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun g => b g • p g)
  have hs := hsum.trans (eventuallyEq_sum fun g _ => hb g)
  have hout := (Lp.coeFn_smul (Fintype.card (C.G F ζ hζ hF U) : ℂ)⁻¹
    (∑ g, b g • p g)).trans (hs.const_smul _)
  filter_upwards [hout, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hball
  simpa only [Chart.averageLp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    LinearIsometry.coe_toContinuousLinearMap, Chart.average, Set.indicator_of_mem hball,
    b, p, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hx
theorem Chart.average_congr_ae {f k : E C.n → ℂ}
    (hfk : f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)] k) :
    C.average F ζ hζ hF U f =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
      C.average F ζ hζ hF U k := by
  have hg : ∀ g : C.G F ζ hζ hF U,
      (fun x => f (C.orthogonal g x)) =ᵐ[volume.restrict (Metric.ball (0 : E C.n) C.radius)]
        fun x => k (C.orthogonal g x) := fun g =>
    (Chart.measurePreserving_ball F ζ hζ hF U C g).quasiMeasurePreserving.ae_eq_comp hfk
  filter_upwards [Filter.eventually_all.mpr hg] with x hx
  by_cases hball : x ∈ Metric.ball (0 : E C.n) C.radius
  · simp only [Chart.average, Set.indicator_of_mem hball]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    rw [hx g]
  · simp only [Chart.average, Set.indicator_of_notMem hball]
theorem Chart.averageLp_idempotent :
    (Chart.averageLp F ζ hζ hF U C).comp (Chart.averageLp F ζ hζ hF U C) =
      Chart.averageLp F ζ hζ hF U C := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (Chart.averageLp_formula F ζ hζ hF U C _).trans
    ((Chart.average_congr_ae F ζ hζ hF U C (Chart.averageLp_formula F ζ hζ hF U C f)).trans
      (by simpa only [C.average_idempotent F ζ hζ hF U f] using
        (Chart.averageLp_formula F ζ hζ hF U C f).symm))
theorem Chart.opNorm_averageLp_le : ‖Chart.averageLp F ζ hζ hF U C‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using Chart.norm_averageLp_le F ζ hζ hF U C f

theorem Chart.smooth_cutoff_section (ψ : E C.n → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Metric.ball (0 : E C.n) C.radius)
    (s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun z => s.val (z, A.representative C.component))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x • s.val (C.coordinates x, A.representative C.component)) ∧
      HasCompactSupport (fun x => ψ x • s.val (C.coordinates x, A.representative C.component)) ∧
      tsupport (fun x => ψ x • s.val (C.coordinates x, A.representative C.component)) ⊆
        interior (cube C.n C.a) := by
  let f := fun x => ψ x • s.val (C.coordinates x, A.representative C.component)
  have ht : tsupport f ⊆ tsupport ψ := tsupport_smul_subset_left ψ _
  refine ⟨?_, hc.smul_right, ht.trans (hsupp.trans (subset_closure.trans C.closed_ball_in_cube))⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport ψ
  · have he : x ∈ C.extendedDomain := C.closed_ball_in_extension (subset_closure (hsupp hx))
    exact (hψ.contDiffAt).smul
      (hs.contDiffAt.comp x (C.smooth_coordinates.contDiffAt (C.open_extendedDomain.mem_nhds he)))
  · have hz : ψ =ᶠ[nhds x] 0 := by
      exact notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [f, hy, Pi.zero_apply, zero_smul]

end ChartFacts

theorem cutoff_derivative_bounds {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ k x, ‖iteratedFDeriv ℝ k f x‖ ≤ B k := by
  choose B hB hbound using hc.exists_bound_iteratedFDeriv hf
  exact ⟨B, hB, fun k x => hbound k k le_rfl x⟩

structure Localizers (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) (K : Set (X F ζ hζ U)) where
  count : ℕ
  empty_case : K = ∅ → count = 0
  chart : Fin count → Chart F ζ hζ hF U A
  open_image : ∀ i, IsOpen ((chart i).O F ζ hζ hF U)
  quotient_chart : ∀ i, Quotient ((chart i).relation F ζ hζ hF U) ≃ₜ
    ((chart i).O F ζ hζ hF U)
  quotient_chart_formula : ∀ i (x : Metric.ball (0 : E (chart i).n) (chart i).radius),
    (quotient_chart i (Quotient.mk _ x)).val = (chart i).toBase F ζ hζ hF U x.val
  orbit_relation : ∀ i (x y : Metric.ball (0 : E (chart i).n) (chart i).radius),
    ((chart i).relation F ζ hζ hF U).r x y ↔
      ∃ g : (chart i).G F ζ hζ hF U, (chart i).orthogonal g x.val = y.val

  line_orbit_relation : ∀ i (x y : Metric.ball (0 : E (chart i).n) (chart i).radius)
      (a b : V F ζ hζ U),
    ((chart i).lineRelation F ζ hζ hF U).r (x,a) (y,b) ↔
      ∃ g : (chart i).G F ζ hζ hF U,
        (chart i).orthogonal g x.val = y.val ∧
        (b : ℂ) = ((chart i).rho F ζ hζ hF U g : ℂ) * (a : ℂ)
  line_chart_surjective : ∀ i (l : Line F ζ hζ hF U A),
    lineBase F ζ hζ hF U A l ∈ (chart i).O F ζ hζ hF U →
      ∃ (x : Metric.ball (0 : E (chart i).n) (chart i).radius) (a : V F ζ hζ U),
        (chart i).toLine F ζ hζ hF U x.val a = l
  invariant_ball : ∀ i (g : (chart i).G F ζ hζ hF U),
    (chart i).orthogonal g '' Metric.ball 0 (chart i).radius =
      Metric.ball 0 (chart i).radius
  unitary_character : ∀ i (g : (chart i).G F ζ hζ hF U),
    ‖((chart i).rho F ζ hζ hF U g : ℂ)‖ = 1

  section_equivariance : ∀ i (s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U)
      (g : (chart i).G F ζ hζ hF U) x, x ∈ (chart i).extendedDomain →
    s.val ((chart i).coordinates ((chart i).orthogonal g x),
      A.representative (chart i).component) =
    ((chart i).rho F ζ hζ hF U g : ℂ) *
      s.val ((chart i).coordinates x, A.representative (chart i).component)

  chart_measure : ∀ i, Measure.map ((chart i).toBase F ζ hζ hF U)
    ((Fintype.card ((chart i).G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
      (volume.restrict (Metric.ball 0 (chart i).radius)).withDensity
        (fun x => ENNReal.ofReal ((chart i).weight x))) =
    (quotientMeasure F ζ hζ hF U A).restrict ((chart i).O F ζ hζ hF U)
  ellipticity : Fin count → ℝ
  positive_ellipticity : ∀ i, 0 < ellipticity i
  uniform_ellipticity : ∀ i x, x ∈ closure (Metric.ball (0 : E (chart i).n) (chart i).radius) →
    ∀ ξ : E (chart i).n,
      ellipticity i * ‖ξ‖ ^ 2 ≤
        ∑ j, ∑ k, (chart i).energyMatrix F ζ hζ hF U x j k * ξ j * ξ k
  phi : Fin count → X F ζ hζ U → ℝ
  nonnegative_phi : ∀ i x, 0 ≤ phi i x
  compact_phi : ∀ i, HasCompactSupport (phi i)
  support_phi : ∀ i, tsupport (phi i) ⊆ (chart i).O F ζ hζ hF U
  smooth_phi : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
    (fun z => phi i (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
      (KPCuspSiegel.projection F _ z)))
  neighborhood : Set (X F ζ hζ U)
  open_neighborhood : IsOpen neighborhood
  covers_compact : K ⊆ neighborhood
  partition : ∀ x ∈ neighborhood, ∑ i, phi i x = 1

  cutoff : ∀ i, E (chart i).n → ℝ
  cutoff_formula : ∀ i, cutoff i =
    (Metric.ball 0 (chart i).radius).indicator
      (fun x => phi i ((chart i).toBase F ζ hζ hF U x))
  smooth_cutoff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (cutoff i)
  compact_cutoff : ∀ i, HasCompactSupport (cutoff i)
  support_cutoff : ∀ i, tsupport (cutoff i) ⊆ Metric.ball 0 (chart i).radius
  invariant_cutoff : ∀ i (g : (chart i).G F ζ hζ hF U) x,
    cutoff i ((chart i).orthogonal g x) = cutoff i x
  derivativeBound : Fin count → ℕ → ℝ
  nonnegative_derivativeBound : ∀ i k, 0 ≤ derivativeBound i k
  derivative_bounds : ∀ i k x, x ∈ tsupport (cutoff i) →
    ‖iteratedFDeriv ℝ k (cutoff i) x‖ ≤ derivativeBound i k

  phase : ∀ i, E (chart i).n → ℂˣ
  measurable_phase : ∀ i, Measurable (phase i)
  unitary_phase : ∀ i x, ‖(phase i x : ℂ)‖ = 1
  frame_comparison : ∀ i (s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U),
    ∀ᵐ x ∂volume.restrict (Metric.ball 0 (chart i).radius),
      s.val ((chart i).coordinates x, A.representative (chart i).component) =
        (phase i x : ℂ) * (M.representative s ((chart i).toBase F ζ hζ hF U x) : ℂ)
  restriction : H F ζ hζ hF U A →L[ℂ] HK F ζ hζ hF U A K
  restriction_formula : ∀ v,
    restriction v =ᵐ[(quotientMeasure F ζ hζ hF U A).restrict K] v
  T : ∀ i, H F ζ hζ hF U A →L[ℂ]
    Lp ℂ 2 (volume.restrict (cube (chart i).n (chart i).a))
  T_formula : ∀ i v,
    T i v =ᵐ[volume.restrict (cube (chart i).n (chart i).a)]
      (Metric.ball 0 (chart i).radius).indicator (fun x =>
        (phi i ((chart i).toBase F ζ hζ hF U x) : ℂ) * (phase i x : ℂ) *
          (v ((chart i).toBase F ζ hζ hF U x) : ℂ))
  R : ∀ i, Lp ℂ 2 (volume.restrict (cube (chart i).n (chart i).a)) →L[ℂ]
    HK F ζ hζ hF U A K

  R_formula : ∀ i f,
    ∀ᵐ x ∂volume.restrict (Metric.ball 0 (chart i).radius),
      (chart i).toBase F ζ hζ hF U x ∈ K →
      R i f ((chart i).toBase F ζ hζ hF U x) =
        (V F ζ hζ U).orthogonalProjectionOnto
          (((phase i x)⁻¹ : ℂˣ) * (chart i).average F ζ hζ hF U f x)
  R_zero_extension : ∀ i f,
    ∀ᵐ x ∂(quotientMeasure F ζ hζ hF U A).restrict K,
      x ∉ (chart i).O F ζ hζ hF U → R i f x = 0
  reconstruction : ∀ v, restriction v = ∑ i, R i (T i v)
  smooth_core_image : ∀ i v, v ∈ core F ζ hζ hF U A M →
    ∃ f : E (chart i).n → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ interior (cube (chart i).n (chart i).a) ∧
      T i v =ᵐ[volume.restrict (cube (chart i).n (chart i).a)] f

def emptyLocalizers (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) :
    Localizers F ζ hζ hF U A M ∅ := by
  refine { count := 0
           chart := Fin.elim0
           neighborhood := ∅
           restriction := 0
           empty_case := fun _ => rfl
           open_neighborhood := isOpen_empty
           covers_compact := Set.Subset.rfl
           partition := by intro x hx; exact False.elim hx
           restriction_formula := by intro v; simp only [Measure.restrict_empty, ae_zero]; exact Filter.eventually_bot
           reconstruction := by intro v; simp
           open_image := by intro i; exact Fin.elim0 i
           quotient_chart := by intro i; exact Fin.elim0 i
           quotient_chart_formula := by intro i; exact Fin.elim0 i
           orbit_relation := by intro i; exact Fin.elim0 i
           line_orbit_relation := by intro i; exact Fin.elim0 i
           line_chart_surjective := by intro i; exact Fin.elim0 i
           invariant_ball := by intro i; exact Fin.elim0 i
           unitary_character := by intro i; exact Fin.elim0 i
           section_equivariance := by intro i; exact Fin.elim0 i
           chart_measure := by intro i; exact Fin.elim0 i
           ellipticity := by intro i; exact Fin.elim0 i
           positive_ellipticity := by intro i; exact Fin.elim0 i
           uniform_ellipticity := by intro i; exact Fin.elim0 i
           phi := by intro i; exact Fin.elim0 i
           nonnegative_phi := by intro i; exact Fin.elim0 i
           compact_phi := by intro i; exact Fin.elim0 i
           support_phi := by intro i; exact Fin.elim0 i
           smooth_phi := by intro i; exact Fin.elim0 i
           cutoff := by intro i; exact Fin.elim0 i
           cutoff_formula := by intro i; exact Fin.elim0 i
           smooth_cutoff := by intro i; exact Fin.elim0 i
           compact_cutoff := by intro i; exact Fin.elim0 i
           support_cutoff := by intro i; exact Fin.elim0 i
           invariant_cutoff := by intro i; exact Fin.elim0 i
           derivativeBound := by intro i; exact Fin.elim0 i
           nonnegative_derivativeBound := by intro i; exact Fin.elim0 i
           derivative_bounds := by intro i; exact Fin.elim0 i
           phase := by intro i; exact Fin.elim0 i
           measurable_phase := by intro i; exact Fin.elim0 i
           unitary_phase := by intro i; exact Fin.elim0 i
           frame_comparison := by intro i; exact Fin.elim0 i
           T := by intro i; exact Fin.elim0 i
           T_formula := by intro i; exact Fin.elim0 i
           R := by intro i; exact Fin.elim0 i
           R_formula := by intro i; exact Fin.elim0 i
           R_zero_extension := by intro i; exact Fin.elim0 i
           smooth_core_image := by intro i; exact Fin.elim0 i }

theorem nonempty_localizers_empty (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : Realization F ζ hζ hF U A) :
    Nonempty (Localizers F ζ hζ hF U A M ∅) :=
  ⟨emptyLocalizers F ζ hζ hF U A M⟩

 def ofRawRealization (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : CoreChartLocalizers.Realization F ζ hζ hF U A) :
    Realization F ζ hζ hF U A :=
  { component := M.component
    lift := M.lift
    measurable_component := M.measurable_component
    measurable_lift := M.measurable_lift
    lift_formula := M.lift_formula
    lift_in_domain := M.lift_in_domain
    free_ae := M.free_ae
    representative := M.representative
    section_formula := M.section_formula
    frame := M.frame
    frame_formula := M.frame_formula
    frame_base := M.frame_base
    frame_injective_ae := M.frame_injective_ae
    frame_surjective_ae := M.frame_surjective_ae
    smooth_test_memLp := M.smooth_test_memLp }

 def ofRawChart (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : CoreChartLocalizers.Chart F ζ hζ hF U A) :
    Chart F ζ hζ hF U A :=
  { n := C.n
    positive_n := C.positive_n
    dimension := C.dimension
    a := C.a
    positive_a := C.positive_a
    radius := C.radius
    positive_radius := C.positive_radius
    closed_ball_in_cube := C.closed_ball_in_cube
    component := C.component
    center := C.center
    finite_stabilizer := C.finite_stabilizer
    orthogonal := C.orthogonal
    extendedDomain := C.extendedDomain
    open_extendedDomain := C.open_extendedDomain
    closed_ball_in_extension := C.closed_ball_in_extension
    invariant_extension := C.invariant_extension
    coordinates := C.coordinates
    coordinates_center := C.coordinates_center
    smooth_coordinates := C.smooth_coordinates
    coordinates_embedding := C.coordinates_embedding
    coordinates_open := C.coordinates_open
    smooth_inverse := C.smooth_inverse
    equivariance := C.equivariance
    separated := C.separated
    weight := C.weight
    smooth_weight := C.smooth_weight
    invariant_weight := C.invariant_weight
    lower := C.lower
    upper := C.upper
    positive_lower := C.positive_lower
    finite_bounds := C.finite_bounds
    coordinate_volume := C.coordinate_volume }

 def ofRawLocalizers (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (M : CoreChartLocalizers.Realization F ζ hζ hF U A)
    {K : Set (X F ζ hζ U)} (hK : MeasurableSet K)
    (C : CoreChartLocalizers.FiniteCutoffs F ζ hζ hF U A K)
    (P : CoreChartLocalizers.FrameComparison F ζ hζ hF U A M C)
    (B : CoreChartLocalizers.LocalOperators F ζ hζ hF U A M C P) :
    Localizers F ζ hζ hF U A (ofRawRealization F ζ hζ hF U A M) K := by
  choose D hD hbound using fun i =>
    cutoff_derivative_bounds (C.smooth_cutoff i) (C.compact_cutoff i)
  refine {
    count := C.count
    chart := fun i => ofRawChart F ζ hζ hF U A (C.chart i)
    empty_case := C.empty_case
    open_image := fun i => Chart.open_image F ζ hζ hF U _
    quotient_chart := fun i => Chart.quotientChart F ζ hζ hF U _
    quotient_chart_formula := fun i x => Chart.quotientChart_formula F ζ hζ hF U _ x
    orbit_relation := fun i x y => Chart.orbit_relation F ζ hζ hF U _ x y
    line_orbit_relation := fun i x y a b => Chart.line_orbit_relation F ζ hζ hF U _ x y a b
    line_chart_surjective := fun i l hl => Chart.line_chart_surjective F ζ hζ hF U _ l hl
    invariant_ball := fun i => Chart.invariant_ball F ζ hζ hF U _
    unitary_character := fun i => Chart.rho_unitary F ζ hζ hF U _
    section_equivariance := fun i s g x hx => Chart.section_equivariance F ζ hζ hF U _ s g hx
    chart_measure := C.chart_measure
    ellipticity := C.ellipticity
    positive_ellipticity := C.positive_ellipticity
    uniform_ellipticity := C.uniform_ellipticity
    phi := C.phi
    nonnegative_phi := C.nonnegative_phi
    compact_phi := C.compact_phi
    support_phi := C.support_phi
    smooth_phi := C.smooth_phi
    neighborhood := C.neighborhood
    open_neighborhood := C.open_neighborhood
    covers_compact := C.covers_compact
    partition := C.partition
    cutoff := C.cutoff
    cutoff_formula := C.cutoff_formula
    smooth_cutoff := C.smooth_cutoff
    compact_cutoff := C.compact_cutoff
    support_cutoff := C.support_cutoff
    invariant_cutoff := C.invariant_cutoff
    derivativeBound := D
    nonnegative_derivativeBound := hD
    derivative_bounds := fun i k x _ => hbound i k x
    phase := P.phase
    measurable_phase := P.measurable_phase
    unitary_phase := P.unitary_phase
    frame_comparison := P.frame_comparison
    restriction := restriction F ζ hζ hF U A K
    restriction_formula := restriction_formula F ζ hζ hF U A K
    T := B.T
    T_formula := B.T_formula
    R := B.R
    R_formula := B.R_formula
    R_zero_extension := B.R_zero_extension
    smooth_core_image := B.smooth_core_image
    reconstruction := CoreChartLocalizers.local_reconstruction F ζ hζ hF U A M hK C P B }

theorem actual_realization_and_localizers
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    ∃ M : Realization F ζ hζ hF U A,
      ∀ K : Set (X F ζ hζ U), IsCompact K →
        Nonempty (Localizers F ζ hζ hF U A M K) := by
  obtain ⟨M⟩ := CoreChartLocalizers.measurable_realization F ζ hζ hF U A
  refine ⟨ofRawRealization F ζ hζ hF U A M, ?_⟩
  intro K hK
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  letI : T2Space (X F ζ hζ U) :=
    CoreChartLocalizers.quotient_hausdorff F ζ hζ hF U A
  obtain ⟨C⟩ := CoreChartLocalizers.finite_cutoffs F ζ hζ hF U A K hK
  obtain ⟨P⟩ := CoreChartLocalizers.frame_comparison F ζ hζ hF U A M C
  obtain ⟨B⟩ := CoreChartLocalizers.bounded_local_operators F ζ hζ hF U A M
    hK.measurableSet C P
  exact ⟨ofRawLocalizers F ζ hζ hF U A M hK.measurableSet C P B⟩

end KPCoreChartLocalizers

theorem kp_cont_core_chart_localizers
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) :
    ∃ (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
      (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
      (M : KPCoreChartLocalizers.Realization F ζ hζ hF U A),
      ∀ K : Set (KPCoreChartLocalizers.X F ζ hζ U), IsCompact K →
        Nonempty (KPCoreChartLocalizers.Localizers F ζ hζ hF U A M K) := by
  obtain ⟨hF, _, ⟨A⟩⟩ := kp_cont_finite_cusp_atlas F ζ hζ U
  obtain ⟨M, hM⟩ := KPCoreChartLocalizers.actual_realization_and_localizers F ζ hζ hF U A
  exact ⟨hF, A, M, hM⟩

end DedekindZetaZeroFree

end
