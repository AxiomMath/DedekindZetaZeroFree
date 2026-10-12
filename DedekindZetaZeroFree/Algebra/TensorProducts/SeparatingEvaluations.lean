module

public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

noncomputable section
open scoped TensorProduct
namespace DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.PointwiseKernel

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]

def tensorEvaluation (f : ∀ i, V i →ₗ[𝕜] 𝕜) :
    (⨂[𝕜] i, V i) →ₗ[𝕜] 𝕜 :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra 𝕜 ι 𝕜).compLinearMap f)

run_cmd Lean.Elab.Command.liftTermElabM do
  let some _ ← Lean.Meta.getEqnsFor? ``tensorEvaluation
    | throwError "failed to realize tensorEvaluation equations at their origin"

 lemma tensorEvaluation_map
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module 𝕜 (W i)]
    (φ : ∀ i, W i →ₗ[𝕜] 𝕜) (ψ : ∀ i, V i →ₗ[𝕜] W i) (y : ⨂[𝕜] i, V i) :
    tensorEvaluation φ (PiTensorProduct.map ψ y) =
      tensorEvaluation (fun i => φ i ∘ₗ ψ i) y := by
  have h : (tensorEvaluation φ).comp (PiTensorProduct.map ψ) =
      tensorEvaluation (fun i => φ i ∘ₗ ψ i) := by
    apply PiTensorProduct.ext
    ext x
    simp [tensorEvaluation, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod,
      MultilinearMap.mkPiAlgebra_apply, MultilinearMap.compLinearMap_apply]
  exact LinearMap.congr_fun h y

private lemma dualDistrib_tprod_eq_tensorEvaluation
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module 𝕜 (W i)]
    (φ : ∀ i, W i →ₗ[𝕜] 𝕜) :
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod 𝕜 φ) =
      tensorEvaluation (𝕜 := 𝕜) φ := by
  apply PiTensorProduct.ext
  ext x
  simp [PiTensorProduct.dualDistrib_apply, tensorEvaluation, PiTensorProduct.lift.tprod,
    MultilinearMap.mkPiAlgebra_apply]

private theorem tensor_evaluations_separate_finite
    [∀ i, Module.Finite 𝕜 (V i)]
    {A : ι → Type*} (f : ∀ i, A i → V i →ₗ[𝕜] 𝕜)
    (hsep : ∀ i (v : V i), (∀ a, f i a v = 0) → v = 0)
    (y : ⨂[𝕜] i, V i)
    (hy : ∀ a : ∀ i, A i, tensorEvaluation (fun i => f i (a i)) y = 0) :
    y = 0 := by
  classical
  have hspan : ∀ i, Submodule.span 𝕜 (Set.range (f i)) = ⊤ := by
    intro i
    apply Submodule.eq_top_iff'.mpr
    intro φ
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have hv0 : v = 0 := hsep i v fun a => by
      exact (Submodule.mem_iInf _).mp hv a
    simp [hv0]
  let L : (⨂[𝕜] i, Module.Dual 𝕜 (V i)) →ₗ[𝕜] 𝕜 :=
    (LinearMap.applyₗ y).comp PiTensorProduct.dualDistrib
  have hL : L = 0 := by
    apply PiTensorProduct.ext_of_span_eq_top hspan
    intro a
    change PiTensorProduct.dualDistrib (PiTensorProduct.tprod 𝕜 (fun i => f i (a i))) y = 0
    rw [dualDistrib_tprod_eq_tensorEvaluation]
    exact hy a
  apply (Module.forall_dual_apply_eq_zero_iff 𝕜 y).mp
  intro φ
  let w := (PiTensorProduct.dualDistribEquiv (R := 𝕜) (M := V)).symm φ
  have hw : PiTensorProduct.dualDistrib w = φ := by
    exact (PiTensorProduct.dualDistribEquiv (R := 𝕜) (M := V)).apply_symm_apply φ
  rw [← hw]
  exact LinearMap.congr_fun hL w

private theorem tensor_evaluations_separate_functionSpace
    {A : ι → Type*} (z : ⨂[𝕜] i, (A i → 𝕜))
    (hz : ∀ a : ∀ i, A i,
      tensorEvaluation (fun i => (LinearMap.proj (a i) : (A i → 𝕜) →ₗ[𝕜] 𝕜)) z = 0) :
    z = 0 := by
  classical

  obtain ⟨T, hT, hzT⟩ := Submodule.mem_span_finite_of_mem_span
    (show z ∈ Submodule.span 𝕜 (Set.range (PiTensorProduct.tprod 𝕜)) from by
      rw [PiTensorProduct.span_tprod_eq_top]
      trivial)
  have hrep : ∀ t : T, ∃ x : ∀ i, A i → 𝕜,
      PiTensorProduct.tprod 𝕜 x = t.val := fun t => hT t.property
  choose x hx using hrep
  let P : ∀ i, Submodule 𝕜 (A i → 𝕜) := fun i =>
    Submodule.span 𝕜 (Set.range (fun t : T => x t i))
  have : ∀ i, Module.Finite 𝕜 (P i) := fun i =>
    Module.Finite.span_of_finite 𝕜 (Set.finite_range (fun t : T => x t i))
  let η : (⨂[𝕜] i, P i) →ₗ[𝕜] (⨂[𝕜] i, (A i → 𝕜)) :=
    PiTensorProduct.map (fun i => (P i).subtype)
  have hTrange : (T : Set (⨂[𝕜] i, (A i → 𝕜))) ⊆ LinearMap.range η := by
    intro t ht
    let xt : ∀ i, P i := fun i =>
      ⟨x ⟨t, ht⟩ i, Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩⟩
    refine ⟨PiTensorProduct.tprod 𝕜 xt, ?_⟩
    change PiTensorProduct.map (fun i => (P i).subtype)
      (PiTensorProduct.tprod 𝕜 xt) = t
    rw [PiTensorProduct.map_tprod]
    exact hx ⟨t, ht⟩
  have hzrange : z ∈ LinearMap.range η :=
    (Submodule.span_le.mpr hTrange) hzT
  obtain ⟨w, hw⟩ := hzrange
  have hw0 : w = 0 := by
    apply tensor_evaluations_separate_finite
      (fun i a => (LinearMap.proj a : (A i → 𝕜) →ₗ[𝕜] 𝕜) ∘ₗ (P i).subtype)
    · intro i v hv
      apply Subtype.ext
      funext a
      exact hv a
    · intro a
      rw [← tensorEvaluation_map]
      change tensorEvaluation (fun i => LinearMap.proj (a i)) (η w) = 0
      rw [hw]
      exact hz a
  rw [← hw, hw0, map_zero]

theorem tensor_evaluations_separate
    {A : ι → Type*} (f : ∀ i, A i → V i →ₗ[𝕜] 𝕜)
    (hsep : ∀ i (y : V i), (∀ a, f i a y = 0) → y = 0)
    (y : ⨂[𝕜] i, V i)
    (hy : ∀ a : ∀ i, A i, tensorEvaluation (fun i => f i (a i)) y = 0) :
    y = 0 := by
  classical

  let fhat : ∀ i, V i →ₗ[𝕜] (A i → 𝕜) := fun i =>
    { toFun := fun v => fun a => f i a v
      map_add' := by intro v w; funext a; simp
      map_smul' := by intro c v; funext a; simp }
  have hker : ∀ i, LinearMap.ker (fhat i) = ⊥ := by
    intro i
    rw [Submodule.eq_bot_iff]
    intro v hv
    refine hsep i v (fun a => ?_)
    have h1 : (fhat i) v = 0 := hv
    have h2 := congrFun h1 a
    simpa [fhat] using h2

  let g : ∀ i, (A i → 𝕜) →ₗ[𝕜] V i := fun i => (fhat i).leftInverse
  have hg : ∀ i, (g i).comp (fhat i) = LinearMap.id := fun i =>
    LinearMap.leftInverse_comp_of_inj (hker i)
  have hleft : (PiTensorProduct.map g).comp (PiTensorProduct.map fhat) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    have hfun : (fun i => g i ∘ₗ fhat i) = fun i => (LinearMap.id : V i →ₗ[𝕜] V i) :=
      funext fun i => hg i
    rw [hfun, PiTensorProduct.map_id]
  have hinj : Function.Injective (PiTensorProduct.map fhat) := by
    intro a b hab
    have h2 : ∀ x, PiTensorProduct.map g (PiTensorProduct.map fhat x) = x :=
      fun x => LinearMap.congr_fun hleft x
    rw [← h2 a, hab, h2 b]
  have hzero : PiTensorProduct.map fhat y = 0 := by
    apply tensor_evaluations_separate_functionSpace
    intro a
    have hfun : (fun i => (LinearMap.proj (a i) : (A i → 𝕜) →ₗ[𝕜] 𝕜) ∘ₗ fhat i) =
        fun i => f i (a i) := by
      funext i
      ext v
      simp [fhat]
    rw [tensorEvaluation_map, hfun, hy a]
  exact hinj (by rw [hzero, map_zero])

end DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.PointwiseKernel

end
