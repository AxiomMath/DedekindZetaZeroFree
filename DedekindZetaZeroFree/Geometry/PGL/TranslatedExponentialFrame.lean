module

public import DedekindZetaZeroFree.Analysis.LieGroups.SmoothExponentialFrameCriterion
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.WordDerivativesAndSmoothOrbits

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Manifold ContDiff

namespace DedekindZetaZeroFree.PGLExponential

set_option backward.isDefEq.respectTransparency false in

theorem translated_exponential_frame
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [ChartedSpace V G]
    [LieGroup (𝓘(ℝ, V)) (⊤ : ℕ∞) G]
    {B : Type*} [Fintype B]
    (D : HilbertLieExponentialData G V B) (g : G) :
    ∃ E : OpenPartialHomeomorph V G,
      (0 : V) ∈ E.source ∧
      (∀ a ∈ E.source, E a = g * D.exponential a) ∧
      ContMDiffOn (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞) E E.source ∧
      ContMDiffOn (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞) E.symm E.target ∧
      (∀ b : B, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun a => deriv (fun t : ℝ => E.symm
          (E a * D.exponential (t • D.basis b))) 0) E.source) ∧
      (∀ a ∈ E.source, ∃ F : Module.Basis B ℝ V,
        ∀ b, F b = deriv (fun t : ℝ => E.symm
          (E a * D.exponential (t • D.basis b))) 0) := by
  let L (h : G) : Diffeomorph (𝓘(ℝ, V)) (𝓘(ℝ, V)) G G (⊤ : ℕ∞) :=
    { toEquiv := Equiv.mulLeft h
      contMDiff_toFun := contMDiff_const.mul contMDiff_id
      contMDiff_invFun := contMDiff_const.mul contMDiff_id }
  let Φ := D.exponentialChart.trans (L g).toPartialDiffeomorph
  let E := Φ.toOpenPartialHomeomorph
  have hs : E.source = D.exponentialChart.source := by
    ext a
    simp [E, Φ, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph]
  have he (a : V) : E a = g * D.exponentialChart a := rfl
  have h0 : (0 : V) ∈ E.source := hs.symm ▸ D.zero_mem_source
  have hf : ContMDiffOn (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞) E E.source :=
    Φ.contMDiffOn
  have hi : ContMDiffOn (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞) E.symm E.target :=
    Φ.symm.contMDiffOn
  refine ⟨E, h0, ?_, hf, hi, ?_, ?_⟩
  · intro a ha
    rw [he, D.chart_eq_exponential a (hs ▸ ha)]
  · intro b a ha
    let f : V → ℝ → V := fun x t => E.symm (E x * D.exponential (t • D.basis b))
    have hEa := hf.contMDiffAt (E.open_source.mem_nhds ha)
    have hEi := hi.contMDiffAt (E.open_target.mem_nhds (E.map_source ha))
    have hprod : ContMDiffAt ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, V))
        (⊤ : ℕ∞) (Function.uncurry f) (a, 0) := by
      have hx := hEa.comp (a, (0 : ℝ))
        (contMDiffAt_fst (I := 𝓘(ℝ, V)) (J := 𝓘(ℝ, ℝ)))
      have ht : ContMDiffAt ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, V))
          (⊤ : ℕ∞) (fun p : V × ℝ => p.2 • D.basis b) (a, 0) :=
        (contMDiffAt_snd (I := 𝓘(ℝ, V)) (J := 𝓘(ℝ, ℝ))).smul
          (contMDiffAt_const (I := (𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ)))
            (I' := 𝓘(ℝ, V)) (c := D.basis b))
      have hex := D.exponential_smooth.contMDiffAt.comp (a, (0 : ℝ)) ht
      exact hEi.comp_of_eq (hx.mul hex) (by simp [D.exponential_zero])
    have hd := ContMDiffAt.mfderiv (m := (⊤ : ℕ∞)) f (fun _ : V => (0 : ℝ))
      hprod contMDiffAt_const (by simp)
    simp +unfoldPartialApp only [inTangentCoordinates,
      inCoordinates_tangent_bundle_core_model_space] at hd
    have hd' := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
    have hd'' : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞)
        (fun x => deriv (f x) 0) a := by
      convert hd' using 1
      funext x
      rw [mfderiv_eq_fderiv]
      rfl
    exact hd''.contDiffAt.contDiffWithinAt
  · intro a ha
    let f : V → V := fun u => E.symm (E a * D.exponential u)
    have hd0 : IsLocalDiffeomorphAt (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞)
        D.exponential 0 :=
      ⟨D.exponentialChart, D.zero_mem_source, fun u hu =>
        (D.chart_eq_exponential u hu).symm⟩
    have hd1 := (L (E a)).isLocalDiffeomorph (D.exponential 0)
    have hd2 : IsLocalDiffeomorphAt (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞)
        E.symm (E a * D.exponential 0) := by
      rw [D.exponential_zero, mul_one]
      exact ⟨Φ.symm, E.map_source ha, fun u hu => rfl⟩
    have hd : IsLocalDiffeomorphAt (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞) f 0 :=
      (hd0.comp (𝓘(ℝ, V)) G hd1).comp (𝓘(ℝ, V)) V hd2
    let A : V ≃L[ℝ] V := hd.mfderivToContinuousLinearEquiv (by simp)
    refine ⟨D.basis.map A.toLinearEquiv, ?_⟩
    intro b
    have hd' : HasFDerivAt f (fderiv ℝ f 0) 0 :=
      (hd.contMDiffAt.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    have hr : HasDerivAt (fun t : ℝ => t • D.basis b) (D.basis b) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (D.basis b)
    have hd'' : HasFDerivAt f (fderiv ℝ f 0) ((0 : ℝ) • D.basis b) := by
      simpa using hd'
    change A (D.basis b) = _
    have hA : A (D.basis b) = fderiv ℝ f 0 (D.basis b) := by
      change (mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, V)) f 0) (D.basis b) = _
      rw [mfderiv_eq_fderiv]
      rfl
    rw [hA]
    exact (hd''.comp_hasDerivAt 0 hr).deriv.symm

end DedekindZetaZeroFree.PGLExponential

end
