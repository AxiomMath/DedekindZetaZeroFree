module

public import DedekindZetaZeroFree.Analysis.SpectralTheory.ResolventPencils.FiniteWindowEigenvectors
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

@[expose] public section

open scoped ContinuousFunctionalCalculus
open Topology

namespace DedekindZetaZeroFree.KPFiniteWindowPencil

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma cfc_eigen (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (r : ℝ)
    (u : H) (hu : u ≠ 0) (he : B u = r • u) (f : ℝ → ℝ) (hf : Continuous f) :
    (cfc f B) u = f r • u := by
  have hr : r ∈ spectrum ℝ B := by
    rw [spectrum.mem_iff]
    intro h
    have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp h).1
    apply hu
    apply hi
    simpa [he, Algebra.algebraMap_eq_smul_one] using (show (r • (1 : H →L[ℂ] H) - B) u = 0 by simp [he])
  let x : spectrum ℝ B := ⟨r, hr⟩
  have hh : ∀ g : C(spectrum ℝ B, ℝ), (cfcHom hB g) u = g x • u := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      change ((cfcHom hB) (algebraMap ℝ _ r)) u = r • u
      rw [AlgHomClass.commutes]
      simp [Algebra.algebraMap_eq_smul_one]
    | id => simpa [x, cfcHom_id] using he
    | star_id => simpa [x, cfcHom_id] using he
    | add g k hg hk => simp [hg, hk, add_smul]
    | mul g k hg hk =>
      simp only [map_mul, ContinuousLinearMap.mul_apply, ContinuousMap.mul_apply]
      rw [hk, ContinuousLinearMap.map_smul_of_tower, hg, mul_smul, smul_comm]
    | frequently g hg =>
      have hc : IsClosed {g : C(spectrum ℝ B, ℝ) | (cfcHom hB g) u = g x • u} :=
        isClosed_eq ((cfcHom_continuous hB).clm_apply continuous_const) (by fun_prop)
      have hm : g ∈ closure {g : C(spectrum ℝ B, ℝ) | (cfcHom hB g) u = g x • u} :=
        mem_closure_iff_frequently.mpr hg
      rw [hc.closure_eq] at hm
      exact hm
  rw [cfc_apply f B hB hf.continuousOn]
  exact hh _

 noncomputable def W (B : H →L[ℂ] H) (J : Set ℝ) : Submodule ℂ H :=
  ⨅ (f : ℝ → ℝ) (_ : Continuous f)
          (_ : ∀ ν ∈ J, f (1 / (1 + ν)) = 0),
          (cfc f B).toLinearMap.ker

private lemma W_mem (B : H →L[ℂ] H) (J : Set ℝ) (u : H) :
    u ∈ W B J ↔ ∀ (f : ℝ → ℝ) (hf : Continuous f)
      (hzero : ∀ ν ∈ J, f (1 / (1 + ν)) = 0), (cfc f B) u = 0 := by
  simp [W]

private lemma W_invariant (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (J : Set ℝ)
    (u : H) (hu : u ∈ W B J) : B u ∈ W B J := by
  rw [W_mem] at hu ⊢
  intro f hf hf0
  have hc : Commute B (cfc f B) := by
    simpa only [cfc_id ℝ B hB] using cfc_commute_cfc (id : ℝ → ℝ) f B
  have hc' : B ((cfc f B) u) = (cfc f B) (B u) := by
    exact congr($(hc.eq).toLinearMap u)
  rw [← hc', hu f hf hf0, map_zero]

lemma pencil_isolated_of_finite_window
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (μ : ℝ) (hμ : ¬ IsUnit (1 - (μ + 1) • B))
    (J : Set ℝ) (hμJ : μ ∈ interior J)
    (hfinite : Module.Finite ℂ
      (⨅ (f : ℝ → ℝ) (_ : Continuous f)
        (_ : ∀ ν ∈ J, f (1 / (1 + ν)) = 0),
        (cfc f B).toLinearMap.ker : Submodule ℂ H)) :
    ∃ η : ℝ, 0 < η ∧
      ∀ ν : ℝ, ¬ IsUnit (1 - (ν + 1) • B) → |ν - μ| < η → ν = μ := by
  let p := W B J
  let T : Module.End ℂ p := LinearMap.restrict B.toLinearMap (W_invariant B hB J)
  have hTf : {z : ℂ | T.HasEigenvalue z}.Finite := by
    letI : Module.Finite ℂ p := hfinite
    exact T.finite_hasEigenvalue
  let F : Set ℝ := {ν | ν ∈ interior J ∧ ¬ IsUnit (1 - (ν + 1) • B)}
  have hinj : Function.Injective (fun ν : ℝ => ((1 / (1 + ν) : ℝ) : ℂ)) := by
    intro a b hab
    have hab' : (1 + a)⁻¹ = (1 + b)⁻¹ := by
      change ((1 / (1 + a) : ℝ) : ℂ) = ((1 / (1 + b) : ℝ) : ℂ) at hab
      have h : (1 / (1 + a) : ℝ) = 1 / (1 + b) := Complex.ofReal_injective hab
      simpa only [one_div] using h
    have := inv_injective hab'
    linarith
  have hF : F.Finite := by
    apply (hTf.preimage hinj.injOn).subset
    intro ν hν
    rcases DedekindZetaZeroFree.KPFiniteWindowPencil.pencil_eigenvector_of_finite_window
      B hB ν hν.2 J hν.1 hfinite with ⟨u, hu, he⟩
    have hn : ν + 1 ≠ 0 := by
      intro hn
      apply hν.2
      simp [hn]
    have he' : B u = (1 / (1 + ν) : ℝ) • u := by
      calc
        B u = (1 / (1 + ν) : ℝ) • ((ν + 1) • B u) := by
          rw [smul_smul, show (1 / (1 + ν)) * (ν + 1) = 1 by
            rw [add_comm 1 ν, one_div, inv_mul_cancel₀ hn], one_smul]
        _ = (1 / (1 + ν) : ℝ) • u := by rw [← he]
    have huW : u ∈ p := by
      rw [W_mem]
      intro f hf hf0
      rw [cfc_eigen B hB _ u hu he' f hf, hf0 ν (interior_subset hν.1), zero_smul]
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := (⟨u, huW⟩ : p))
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    constructor
    · apply Subtype.ext
      change B u = ((1 / (1 + ν) : ℝ) : ℂ) • u
      change B u = (algebraMap ℝ ℂ (1 / (1 + ν))) • u
      rw [algebraMap_smul]
      exact he'
    · simpa only [ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero] using hu
  have hnear : (interior J) ∩ (F \ {μ})ᶜ ∈ nhds μ := by
    have ho : IsOpen ((interior J) ∩ (F \ {μ})ᶜ) :=
      isOpen_interior.inter hF.diff.isClosed.isOpen_compl
    exact ho.mem_nhds ⟨hμJ, by simp⟩
  rcases Metric.mem_nhds_iff.mp hnear with ⟨η, hη, hηball⟩
  refine ⟨η, hη, fun ν hv hν => ?_⟩
  have hball : ν ∈ Metric.ball μ η := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hν
  have hgood := hηball hball
  have hνF : ν ∈ F := ⟨hgood.1, hv⟩
  by_contra hne
  exact hgood.2 ⟨hνF, by simpa only [Set.mem_singleton_iff] using hne⟩

end DedekindZetaZeroFree.KPFiniteWindowPencil
