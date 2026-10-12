module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.CoframeCalculus
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.MetricCodifferentialDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescent

open KPContActualSectorSmoothTestModules KPContActualCotangentCountableShrinking
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentOverlapRationalBranches KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def liftExtension {W : Type*} [Zero W] (a : ActualChart (U := U) (H := H))
    (f : omega a → W) (x : M F) : W :=
  if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

def chartDifferential (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ)
    (x : omega a) : E F :=
  CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (liftExtension a f) x.val)

def chartCodifferential (a : ActualChart (U := U) (H := H)) (W : omega a → E F)
    (x : omega a) : ℂ :=
  HyperbolicChart.codifferential (d F)
    (fun y => (CotangentLogCoframe.j (d F)).symm (liftExtension a W y)) x.val

 theorem differential_descent (f : S_U F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a => chartDifferential a (f.val a)) ∧
    ∀ hv : IsMeasurableCotangentFamily (fun a => chartDifferential a (f.val a)),
      (⟨fun a => chartDifferential a (f.val a), hv⟩ : Family (U := U) (H := H)) ∈
        cotangentTests ∧
      cotangentSupport ⟨fun a => chartDifferential a (f.val a), hv⟩ ⊆
        scalarSupport f.val := by
  exact KPContActualSectorTestDifferentialDescentCalculus.scalar_differential_descent.1 f

 theorem chart_differential_add (a : ActualChart (U := U) (H := H))
    (f g : omega a → ℂ) (hf : SmoothOnLift a f) (hg : SmoothOnLift a g) :
    chartDifferential a (f + g) = chartDifferential a f + chartDifferential a g := by
  exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.1 a f g hf hg

 theorem chart_differential_smul (a : ActualChart (U := U) (H := H))
    (c : ℂ) (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    chartDifferential a (c • f) = c • chartDifferential a f := by
  exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.2.1 a c f hf

def D_U : S_U F ζ hζ U R P H →ₗ[ℂ] T_U F ζ hζ U R P H where
  toFun f := ⟨⟨fun a => chartDifferential a (f.val a), (differential_descent f).1⟩,
    ((differential_descent f).2 _).1⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact chart_differential_add a (f.val a) (g.val a) (f.property.1 a) (g.property.1 a)
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact chart_differential_smul a c (f.val a) (f.property.1 a)

 theorem codifferential_descent (W : T_U F ζ hζ U R P H) :
    (fun a => chartCodifferential a (coefficient W.val a)) ∈ scalarTests ∧
    scalarSupport (fun a => chartCodifferential a (coefficient W.val a)) ⊆
      cotangentSupport W.val := by
  exact KPContActualSectorTestDifferentialDescentCalculus.metric_codifferential_descent.1 W

 theorem chart_codifferential_add (a : ActualChart (U := U) (H := H))
    (V W : omega a → E F) (hV : SmoothOnLift a V) (hW : SmoothOnLift a W) :
    chartCodifferential a (V + W) = chartCodifferential a V + chartCodifferential a W := by
  exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.2.2.1 a V W hV hW

 theorem chart_codifferential_smul (a : ActualChart (U := U) (H := H))
    (c : ℂ) (W : omega a → E F) (hW : SmoothOnLift a W) :
    chartCodifferential a (c • W) = c • chartCodifferential a W := by
  exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.2.2.2.1 a c W hW

def δ_U : T_U F ζ hζ U R P H →ₗ[ℂ] S_U F ζ hζ U R P H where
  toFun W := ⟨fun a => chartCodifferential a (coefficient W.val a),
    (codifferential_descent W).1⟩
  map_add' V W := by
    apply Subtype.ext
    funext a
    exact chart_codifferential_add a (coefficient V.val a) (coefficient W.val a)
      (V.property.1 a) (W.property.1 a)
  map_smul' c W := by
    apply Subtype.ext
    funext a
    exact chart_codifferential_smul a c (coefficient W.val a) (W.property.1 a)

structure RealSmoothCutoff (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) where
  val : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ
  smooth : ∀ a : ActualChart (U := U) (H := H),
    SmoothOnLift a (fun x => val (q a x.val))

def cutoffLift (η : RealSmoothCutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) : ℂ :=
  (η.val (q a x.val) : ℂ)

def cutoffDifferential (η : RealSmoothCutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) : E F :=
  chartDifferential a (cutoffLift η a) x

 theorem cutoff_scalar_mem (η : RealSmoothCutoff F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) :
    (fun a x => cutoffLift η a x * f.val a x) ∈ scalarTests := by
  exact (KPContActualSectorTestDifferentialDescentCalculus.scalar_differential_descent.2
    η.val η.smooth).1 f

 theorem cutoff_tensor_mem (η : RealSmoothCutoff F ζ hζ U R P H)
    (W : T_U F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a x => cutoffLift η a x • coefficient W.val a x) ∧
    ∀ hv : IsMeasurableCotangentFamily (fun a x => cutoffLift η a x • coefficient W.val a x),
      (⟨fun a x => cutoffLift η a x • coefficient W.val a x, hv⟩ :
        Family (U := U) (H := H)) ∈ cotangentTests := by
  exact (KPContActualSectorTestDifferentialDescentCalculus.scalar_differential_descent.2
    η.val η.smooth).2.1 W

 theorem cutoff_gradient_mem (η : RealSmoothCutoff F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a x => f.val a x • cutoffDifferential η a x) ∧
    ∀ hv : IsMeasurableCotangentFamily (fun a x => f.val a x • cutoffDifferential η a x),
      (⟨fun a x => f.val a x • cutoffDifferential η a x, hv⟩ :
        Family (U := U) (H := H)) ∈ cotangentTests := by
  exact (KPContActualSectorTestDifferentialDescentCalculus.scalar_differential_descent.2
    η.val η.smooth).2.2 f

def scalarMultiply (η : RealSmoothCutoff F ζ hζ U R P H) :
    S_U F ζ hζ U R P H →ₗ[ℂ] S_U F ζ hζ U R P H where
  toFun f := ⟨fun a x => cutoffLift η a x * f.val a x, cutoff_scalar_mem η f⟩
  map_add' f g := by
    apply Subtype.ext
    funext a x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext a x
    change cutoffLift η a x * (c * f.val a x) = c * (cutoffLift η a x * f.val a x)
    ring

def cotangentMultiply (η : RealSmoothCutoff F ζ hζ U R P H) :
    T_U F ζ hζ U R P H →ₗ[ℂ] T_U F ζ hζ U R P H where
  toFun W := ⟨⟨fun a x => cutoffLift η a x • coefficient W.val a x,
    (cutoff_tensor_mem η W).1⟩, (cutoff_tensor_mem η W).2 _⟩
  map_add' V W := by
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact smul_add _ _ _
  map_smul' c W := by
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact smul_comm (cutoffLift η a x) c (coefficient W.val a x)

def cutoffGradientTimes (η : RealSmoothCutoff F ζ hζ U R P H) :
    S_U F ζ hζ U R P H →ₗ[ℂ] T_U F ζ hζ U R P H where
  toFun f := ⟨⟨fun a x => f.val a x • cutoffDifferential η a x,
    (cutoff_gradient_mem η f).1⟩, (cutoff_gradient_mem η f).2 _⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact add_smul _ _ _
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact mul_smul _ _ _

def contraction (v W : E F) : ℂ :=
  ∑ i : Fin (d F), ∑ k : Fin 3, v (i, k) * W (i, k)

def cutoffContraction (η : RealSmoothCutoff F ζ hζ U R P H) :
    T_U F ζ hζ U R P H →ₗ[ℂ] S_U F ζ hζ U R P H where
  toFun W := ⟨fun a x => contraction (cutoffDifferential η a x) (coefficient W.val a x),
    KPContActualSectorTestDifferentialDescentCalculus.metric_codifferential_descent.2
      η.val η.smooth W⟩
  map_add' V W := by
    apply Subtype.ext
    funext a x
    simp [contraction, coefficient, mul_add, Finset.sum_add_distrib]
  map_smul' c W := by
    apply Subtype.ext
    funext a x
    simp [contraction, coefficient, Finset.mul_sum, mul_left_comm]

structure Properties : Prop where
  differential_chart : ∀ (f : S_U F ζ hζ U R P H)
      (a : ActualChart (U := U) (H := H)) (x : omega a),
    coefficient (D_U f).val a x = chartDifferential a (f.val a) x
  codifferential_chart : ∀ (W : T_U F ζ hζ U R P H)
      (a : ActualChart (U := U) (H := H)) (x : omega a),
    (δ_U W).val a x = chartCodifferential a (coefficient W.val a) x
  differential_isotropy : ∀ (f : S_U F ζ hζ U R P H)
      (a : ActualChart (U := U) (H := H)) (γ : Gamma a) (x : M F) (hx : x ∈ omega a),
    coefficient (D_U f).val a ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ =
      T (isotropyArrow a γ) x (omega_subset_larger a hx)
        (coefficient (D_U f).val a ⟨x, hx⟩)
  differential_overlap : ∀ (f : S_U F ζ hζ U R P H)
      (a b : ActualChart (U := U) (H := H)) (e : ActualBranch a b)
      (x : M F) (hx : x ∈ e.arrow.domain),
    coefficient (D_U f).val b ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
      T e.arrow x hx (coefficient (D_U f).val a ⟨x, e.source_shrinking hx⟩)
  codifferential_isotropy : ∀ (W : T_U F ζ hζ U R P H)
      (a : ActualChart (U := U) (H := H)) (γ : Gamma a) (x : M F) (hx : x ∈ omega a),
    (δ_U W).val a ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ =
      (isotropyArrow a γ).phase x * (δ_U W).val a ⟨x, hx⟩
  codifferential_overlap : ∀ (W : T_U F ζ hζ U R P H)
      (a b : ActualChart (U := U) (H := H)) (e : ActualBranch a b)
      (x : M F) (hx : x ∈ e.arrow.domain),
    (δ_U W).val b ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
      e.arrow.phase x * (δ_U W).val a ⟨x, e.source_shrinking hx⟩
  differential_support : ∀ f : S_U F ζ hζ U R P H,
    cotangentSupport (D_U f).val ⊆ scalarSupport f.val
  codifferential_support : ∀ W : T_U F ζ hζ U R P H,
    scalarSupport (δ_U W).val ⊆ cotangentSupport W.val
  laplacian_chart : ∀ (f : S_U F ζ hζ U R P H)
      (a : ActualChart (U := U) (H := H)) (x : omega a),
    (δ_U (D_U f)).val a x =
      HyperbolicChart.laplacian (d F) (liftExtension a (f.val a)) x.val
  cutoff_real : ∀ (η : RealSmoothCutoff F ζ hζ U R P H)
      (a : ActualChart (U := U) (H := H)) (x : omega a)
      (i : Fin (d F)) (k : Fin 3),
    (cutoffDifferential η a x (i, k)).im = 0
  differential_product : ∀ (η : RealSmoothCutoff F ζ hζ U R P H)
      (f : S_U F ζ hζ U R P H),
    D_U (scalarMultiply η f) = cotangentMultiply η (D_U f) + cutoffGradientTimes η f
  codifferential_product : ∀ (η : RealSmoothCutoff F ζ hζ U R P H)
      (W : T_U F ζ hζ U R P H),
    δ_U (cotangentMultiply η W) = scalarMultiply η (δ_U W) - cutoffContraction η W

end DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescent

namespace DedekindZetaZeroFree

open KPContActualSectorTestDifferentialDescent KPContActualSectorSmoothTestModules
open KPContActualCotangentMeasurableFamilies

theorem kp_cont_actual_sector_test_differential_descent
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorTestDifferentialDescent.Properties (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) := by
  refine {
    differential_chart := ?_
    codifferential_chart := ?_
    differential_isotropy := ?_
    differential_overlap := ?_
    codifferential_isotropy := ?_
    codifferential_overlap := ?_
    differential_support := ?_
    codifferential_support := ?_
    laplacian_chart := ?_
    cutoff_real := ?_
    differential_product := ?_
    codifferential_product := ?_
  }
  · intros; rfl
  · intros; rfl
  · intro f a γ x hx
    exact (D_U f).val.property.2.1 a γ x hx
  · intro f a b e x hx
    exact (D_U f).val.property.2.2 a b e x hx
  · intro W a γ x hx
    exact (δ_U W).property.2.1.1 a γ x hx
  · intro W a b e x hx
    exact (δ_U W).property.2.1.2 a b e x hx
  · intro f
    exact ((differential_descent f).2 _).2
  · intro W
    exact (codifferential_descent W).2
  · intro f a x
    exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.2.2.2.2.1
      a (f.val a) (f.property.1 a) x
  · intro η a x i k
    exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.2.2.2.2.2.1
      a (fun y => η.val (KPContCotangentOverlapRationalBranches.q a y.val))
      (η.smooth a) x i k
  · intro η f
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.2.2.2.2.2.2.1
      a (fun y => η.val (KPContCotangentOverlapRationalBranches.q a y.val))
      (f.val a) (η.smooth a) (f.property.1 a) x
  · intro η W
    apply Subtype.ext
    funext a x
    exact KPContActualSectorTestDifferentialDescentCalculus.coframe_calculus.2.2.2.2.2.2.2
      a (fun y => η.val (KPContCotangentOverlapRationalBranches.q a y.val))
      (coefficient W.val a) (η.smooth a) (W.property.1 a) x

end DedekindZetaZeroFree

end
