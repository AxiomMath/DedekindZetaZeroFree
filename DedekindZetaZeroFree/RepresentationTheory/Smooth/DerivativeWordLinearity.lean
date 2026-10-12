module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology Manifold ContDiff

namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualWordLinearity
open KPSmoothActualFlowData

private theorem rightTranslate_mul
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    (a b : G F ζ hζ) (x : X F ζ hζ) :
    KPSmoothActualFlowData.rightTranslate F ζ hζ b (KPSmoothActualFlowData.rightTranslate F ζ hζ a x) =
      KPSmoothActualFlowData.rightTranslate F ζ hζ (a * b) x := by
  induction x using Quotient.inductionOn with
  | h g => change Quotient.mk _ ((g * a) * b) = Quotient.mk _ (g * (a * b)); rw [mul_assoc]

section Generic
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V G] [LieGroup 𝓘(ℝ, V) (⊤ : ℕ∞) G]
variable {B : Type*} [Fintype B]

private theorem right_derivative_smooth (D : HilbertLieExponentialData G V B)
    (q : G → ℂ) (hq : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) q) (b : B) :
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun a => deriv (fun t : ℝ => q (a * D.exponential (t • D.basis b))) 0) := by
  intro a
  let f : G → ℝ → ℂ := fun a t => q (a * D.exponential (t • D.basis b))
  have hp : ContMDiffAt ((𝓘(ℝ, V)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ)
      (⊤ : ℕ∞) (Function.uncurry f) (a, 0) := by
    exact hq.contMDiffAt.comp _ (contMDiffAt_fst.mul
      (D.exponential_smooth.contMDiffAt.comp _ (contMDiffAt_snd.smul contMDiffAt_const)))
  have hd := ContMDiffAt.mfderiv (m := (⊤ : ℕ∞)) f (fun _ : G => (0 : ℝ))
    hp contMDiffAt_const (by simp)
  simp +unfoldPartialApp only [inTangentCoordinates,
    inCoordinates_tangent_bundle_core_model_space] at hd
  have hd' := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
  convert hd' using 1
  funext g
  rw [mfderiv_eq_fderiv]
  rfl
end Generic

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem smooth_orbit_contMDiff
    [C : ChartedSpace (LieCoordinates F) (GInfinity F)]
    [L : LieGroup 𝓘(ℝ, LieCoordinates F) (⊤ : ℕ∞) (GInfinity F)]
    (D : HilbertLieExponentialData (GInfinity F) (LieCoordinates F) (B F))
    (hD : D.exponential = exponential F)
    (f : X F ζ hζ → ℂ) (hf : SmoothAutomorphic F ζ hζ f) (x : X F ζ hζ) :
    ContMDiff 𝓘(ℝ, LieCoordinates F) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun a => f (KPSmoothActualFlowData.rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ a) x)) := by
  intro a
  let E := D.exponentialChart.toOpenPartialHomeomorph
  let q : GInfinity F → ℂ := fun g => f (KPSmoothActualFlowData.rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ g) x)
  let φ : LieCoordinates F → ℂ := fun v => q (a * exponential F v)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    convert hf.2 (KPSmoothActualFlowData.rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ a) x) using 1
    funext v
    dsimp [φ, q]
    rw [rightTranslate_mul, ← (archimedean_insertion_properties F ζ hζ).2.1]
  have hi : ContMDiffAt 𝓘(ℝ, LieCoordinates F) 𝓘(ℝ, LieCoordinates F)
      (⊤ : ℕ∞) E.symm (1 : GInfinity F) := by
    have h1 : E 0 = (1 : GInfinity F) := (D.chart_eq_exponential 0 D.zero_mem_source).trans D.exponential_zero
    exact h1 ▸ D.exponentialChart.symm.contMDiffOn.contMDiffAt
      (E.open_target.mem_nhds (E.map_source D.zero_mem_source))
  have hψ : ContMDiffAt 𝓘(ℝ, LieCoordinates F) 𝓘(ℝ, LieCoordinates F)
      (⊤ : ℕ∞) (fun g : GInfinity F => E.symm (a⁻¹ * g)) a :=
    hi.comp_of_eq (contMDiffAt_const.mul contMDiffAt_id) (inv_mul_cancel a)
  have hh := hφ.contMDiff.contMDiffAt.comp a hψ
  apply hh.congr_of_eventuallyEq
  have hn : ∀ᶠ g in 𝓝 a, a⁻¹ * g ∈ E.target :=
    (show ContinuousAt (fun g : GInfinity F => a⁻¹ * g) a from
      continuousAt_const.mul continuousAt_id).preimage_mem_nhds (by
      change E.target ∈ 𝓝 (a⁻¹ * a)
      rw [inv_mul_cancel]
      have h1 : E 0 = (1 : GInfinity F) := (D.chart_eq_exponential 0 D.zero_mem_source).trans D.exponential_zero
      exact E.open_target.mem_nhds (h1 ▸ E.map_source D.zero_mem_source))
  filter_upwards [hn] with g hg
  dsimp [φ]
  rw [← hD, ← D.chart_eq_exponential _ (E.map_target hg)]
  change q g = q (a * E (E.symm (a⁻¹ * g)))
  rw [E.right_inv hg, ← mul_assoc, mul_inv_cancel, one_mul]

theorem word_orbit_contDiff (f : X F ζ hζ → ℂ)
    (hf : SmoothAutomorphic F ζ hζ f) (w : List (B F)) (x : X F ζ hζ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : LieCoordinates F =>
      wordDerivative F ζ hζ w f
        (KPSmoothActualFlowData.rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ (exponential F a)) x)) := by
  obtain ⟨C, hC⟩ := actual_archimedean_lie_data F
  letI := C
  obtain ⟨L, D, hD, hbasis, _⟩ := hC
  letI := L
  have hflow (b : B F) (t : ℝ) : D.exponential (t • D.basis b) = flow F b t := by
    rw [hD]
    apply congrArg (exponential F)
    funext c
    simp only [Pi.smul_apply, hbasis, smul_eq_mul]
    split_ifs <;> simp
  let q : List (B F) → GInfinity F → ℂ := fun u a =>
    wordDerivative F ζ hζ u f (KPSmoothActualFlowData.rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ a) x)
  have hq (u : List (B F)) : ContMDiff 𝓘(ℝ, LieCoordinates F) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (q u) := by
    induction u with
    | nil => exact smooth_orbit_contMDiff F ζ hζ D hD f hf x
    | cons b u ih =>
      convert right_derivative_smooth D (q u) ih b using 1
      funext a
      apply congrArg (fun p : ℝ → ℂ => deriv p 0)
      funext t
      dsimp [q, wordDerivative, flowDerivative]
      rw [rightTranslate_mul, ← (archimedean_insertion_properties F ζ hζ).2.1, hflow]
  have he : ContMDiff 𝓘(ℝ, LieCoordinates F) 𝓘(ℝ, LieCoordinates F) (⊤ : ℕ∞)
      (exponential F) := hD ▸ D.exponential_smooth
  exact ((hq w).comp he).contDiff

theorem word_orbit_continuous (f : X F ζ hζ → ℂ)
    (hf : SmoothAutomorphic F ζ hζ f) (w : List (B F)) (x : X F ζ hζ) :
    Continuous (fun a : GInfinity F => wordDerivative F ζ hζ w f
      (KPSmoothActualFlowData.rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ a) x)) := by
  obtain ⟨C, hC⟩ := actual_archimedean_lie_data F
  letI := C
  obtain ⟨L, D, hD, hbasis, _⟩ := hC
  letI := L
  have hflow (b : B F) (t : ℝ) : D.exponential (t • D.basis b) = flow F b t := by
    rw [hD]
    apply congrArg (exponential F)
    funext c
    simp only [Pi.smul_apply, hbasis, smul_eq_mul]
    split_ifs <;> simp
  let q : List (B F) → GInfinity F → ℂ := fun u a =>
    wordDerivative F ζ hζ u f (KPSmoothActualFlowData.rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ a) x)
  have hq (u : List (B F)) : ContMDiff 𝓘(ℝ, LieCoordinates F) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (q u) := by
    induction u with
    | nil => exact smooth_orbit_contMDiff F ζ hζ D hD f hf x
    | cons b u ih =>
      convert right_derivative_smooth D (q u) ih b using 1
      funext a
      apply congrArg (fun p : ℝ → ℂ => deriv p 0)
      funext t
      dsimp [q, wordDerivative, flowDerivative]
      rw [rightTranslate_mul, ← (archimedean_insertion_properties F ζ hζ).2.1, hflow]
  exact (hq w).continuous

theorem word_hasDerivAt_flow (f : X F ζ hζ → ℂ)
    (hf : SmoothAutomorphic F ζ hζ f) (w : List (B F)) (b : B F) (x : X F ζ hζ) :
    HasDerivAt (fun t : ℝ => wordDerivative F ζ hζ w f
      (KPSmoothActualFlowData.rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ (flow F b t)) x))
      (wordDerivative F ζ hζ (b :: w) f x) 0 := by
  let c : ℝ → LieCoordinates F := fun t a => if a = b then t else 0
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := by
    apply contDiff_pi.mpr
    intro a
    dsimp [c]
    split_ifs <;> fun_prop
  exact ((word_orbit_contDiff F ζ hζ f hf w x).comp hc).differentiable (by simp) 0 |>.hasDerivAt

theorem word_add (f g : X F ζ hζ → ℂ)
    (hf : SmoothAutomorphic F ζ hζ f) (hg : SmoothAutomorphic F ζ hζ g)
    (w : List (B F)) :
    wordDerivative F ζ hζ w (f + g) =
      wordDerivative F ζ hζ w f + wordDerivative F ζ hζ w g := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext x
    change deriv _ 0 = _
    simp only [ih, Pi.add_apply]
    exact ((word_hasDerivAt_flow F ζ hζ f hf w b x).add
      (word_hasDerivAt_flow F ζ hζ g hg w b x)).deriv

theorem word_smul (c : ℂ) (f : X F ζ hζ → ℂ)
    (hf : SmoothAutomorphic F ζ hζ f) (w : List (B F)) :
    wordDerivative F ζ hζ w (c • f) = c • wordDerivative F ζ hζ w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext x
    change deriv _ 0 = _
    simp only [ih, Pi.smul_apply]
    exact ((word_hasDerivAt_flow F ζ hζ f hf w b x).const_smul c).deriv

def wordLinearMap (V : Submodule ℂ (X F ζ hζ → ℂ))
    (hV : ∀ v : V, SmoothAutomorphic F ζ hζ v.val) (w : List (B F)) :
    V →ₗ[ℂ] (X F ζ hζ → ℂ) where
  toFun v := wordDerivative F ζ hζ w v.val
  map_add' v u := word_add F ζ hζ v.val u.val (hV v) (hV u) w
  map_smul' c v := word_smul F ζ hζ c v.val (hV v) w

@[simp] theorem wordLinearMap_apply (V : Submodule ℂ (X F ζ hζ → ℂ))
    (hV : ∀ v : V, SmoothAutomorphic F ζ hζ v.val) (w : List (B F))
    (v : V) (x : X F ζ hζ) :
    wordLinearMap F ζ hζ V hV w v x = wordDerivative F ζ hζ w v.val x := rfl

end DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualWordLinearity

end
