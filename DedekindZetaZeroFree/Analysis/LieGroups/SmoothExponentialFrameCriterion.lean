module

public import Mathlib

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section

noncomputable section
open scoped Manifold ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.SmoothWordOrbit.DomainToSmooth.RawFrame

structure Data (G V B : Type*) [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [ChartedSpace V G]
  [Fintype B] where
  basis : Module.Basis B ℝ V
  exponential : V → G
  exponential_zero : exponential 0 = 1
  exponential_add_ray : ∀ (X : V) (s t : ℝ),
    exponential ((s + t) • X) = exponential (s • X) * exponential (t • X)
  exponential_smooth : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ exponential
  exponentialChart : PartialDiffeomorph (𝓘(ℝ, V)) (𝓘(ℝ, V)) V G ∞
  zero_mem_source : (0 : V) ∈ exponentialChart.toPartialEquiv.source
  chart_eq_exponential : ∀ X ∈ exponentialChart.toPartialEquiv.source,
    exponentialChart X = exponential X

set_option backward.isDefEq.respectTransparency false in

theorem translated_exponential_frame
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [ChartedSpace V G]
    [LieGroup (𝓘(ℝ, V)) (⊤ : ℕ∞) G]
    {B : Type*} [Fintype B]
    (D : Data G V B) (g : G) :
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

open scoped Manifold ContDiff Convex
open Topology Filter Asymptotics

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V G]
  [LieGroup (𝓘(ℝ, V)) (↑(⊤ : ℕ∞) : ℕ∞ω) G]
variable {B : Type*} [Fintype B]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem right_frame_hasDerivAt (D : Data G V B)
    (f : G → E) (h : B → G → E)
    (hderiv : ∀ (b : B) (a : G),
      HasDerivAt (fun t : ℝ => f (a * D.exponential (t • D.basis b))) (h b a) 0)
    (b : B) (a : G) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (a * D.exponential (s • D.basis b)))
      (h b (a * D.exponential (t • D.basis b))) t := by
  have hd := hderiv b (a * D.exponential (t • D.basis b))
  have hd' := (show HasDerivAt _ _ (t - t) by simpa using hd).comp_sub_const t t
  convert hd' using 1
  funext s
  rw [mul_assoc, ← D.exponential_add_ray, show t + (s - t) = s by ring]

theorem right_frame_ray_contDiff_one (D : Data G V B)
    (f : G → E) (h : B → G → E) (hh : ∀ b, Continuous (h b))
    (hderiv : ∀ (b : B) (a : G),
      HasDerivAt (fun t : ℝ => f (a * D.exponential (t • D.basis b))) (h b a) 0)
    (b : B) (a : G) :
    ContDiff ℝ 1 (fun t : ℝ => f (a * D.exponential (t • D.basis b))) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (right_frame_hasDerivAt D f h hderiv b a t).differentiableAt, ?_⟩
  have he : deriv (fun t : ℝ => f (a * D.exponential (t • D.basis b))) =
      fun t => h b (a * D.exponential (t • D.basis b)) := by
    funext t
    exact (right_frame_hasDerivAt D f h hderiv b a t).deriv
  rw [he]
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, V)) (↑(⊤ : ℕ∞) : ℕ∞ω)
  exact (hh b).comp (continuous_const.mul
    (D.exponential_smooth.continuous.comp (continuous_id.smul continuous_const)))

theorem right_frame_uniform_ray_expansion (D : Data G V B)
    (f : G → E) (h : B → G → E) (hh : ∀ b, Continuous (h b))
    (hderiv : ∀ (b : B) (a : G),
      HasDerivAt (fun t : ℝ => f (a * D.exponential (t • D.basis b))) (h b a) 0)
    (b : B) (a : G) :
    (fun p : G × ℝ => f (p.1 * D.exponential (p.2 • D.basis b)) - f p.1 -
      p.2 • h b a) =o[𝓝 (a, 0)] (fun p : G × ℝ => p.2) := by
  let F : (G × ℝ) → ℝ → E := fun p t => f (p.1 * D.exponential (t • D.basis b))
  let F' : (G × ℝ) → ℝ → ℝ →L[ℝ] E := fun p t =>
    ContinuousLinearMap.toSpanSingleton ℝ (h b (p.1 * D.exponential (t • D.basis b)))
  have hv : Tendsto (fun p : G × ℝ => p.2) (𝓝 (a, 0)) (𝓝 (0 : ℝ)) :=
    continuous_snd.continuousAt
  have hw : Tendsto (fun _ : G × ℝ => (0 : ℝ)) (𝓝 (a, 0)) (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds
  have hd : ∀ᶠ p in 𝓝 (a, (0 : ℝ)) ×ˢ 𝓝[Set.univ] (0 : ℝ),
      HasFDerivWithinAt (F p.1) (F' p.1 p.2) Set.univ p.2 := by
    exact Eventually.of_forall fun p =>
      (right_frame_hasDerivAt D f h hderiv b p.1.1 p.2).hasFDerivAt.hasFDerivWithinAt
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, V)) (↑(⊤ : ℕ∞) : ℕ∞ω)
  have hc : Continuous (fun p : (G × ℝ) × ℝ => F' p.1 p.2) := by
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp
      ((hh b).comp ((continuous_fst.fst).mul
        (D.exponential_smooth.continuous.comp (continuous_snd.smul continuous_const))))
  have hc' : Tendsto (Function.uncurry F')
      (𝓝 (a, (0 : ℝ)) ×ˢ 𝓝[Set.univ] (0 : ℝ))
      (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (h b a))) := by
    rw [nhdsWithin_univ, ← nhds_prod_eq]
    change Tendsto (fun p : (G × ℝ) × ℝ => F' p.1 p.2)
      (𝓝 ((a, 0), 0)) (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (h b a)))
    simpa [F', D.exponential_zero, ContinuousAt] using
      hc.continuousAt (x := ((a, 0), 0))
  have H : (fun p : G × ℝ => F p (p.2) - F p 0 -
      (ContinuousLinearMap.toSpanSingleton ℝ (h b a)) (p.2 - 0))
      =o[𝓝 (a, 0)] (fun p : G × ℝ => p.2 - 0) := by
    rw [isLittleO_iff]
    intro ε hε
    have seg : ∀ᶠ p : G × ℝ in 𝓝 (a, 0),
        [((0 : ℝ)) -[ℝ] p.2] ⊆ Set.univ := by simp
    have hd' := Eventually.segment_of_prod_nhdsWithin
      (r := fun p z => HasFDerivWithinAt (F p) (F' p z) Set.univ z) hw hv hd seg
    have hc'' : ∀ᶠ p : G × ℝ in 𝓝 (a, 0), ∀ z ∈ [((0 : ℝ)) -[ℝ] p.2],
        ‖F' p z - ContinuousLinearMap.toSpanSingleton ℝ (h b a)‖ < ε := by
      simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at hc'
      exact (hc' ε hε).segment_of_prod_nhdsWithin hw hv seg
    filter_upwards [seg, hd', hc''] with p hseg hdf hcf
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z hz => (hdf z hz).mono hseg) (fun z hz => (hcf z hz).le)
      (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)
  simpa [F, sub_zero, D.exponential_zero] using H

section FiniteProducts

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem right_frame_insertion_hasFDerivAt_zero (D : Data G V B)
    (f : G → E) (h : B → G → E) (hh : ∀ b, Continuous (h b))
    (hderiv : ∀ (b : B) (a : G),
      HasDerivAt (fun t : ℝ => f (a * D.exponential (t • D.basis b))) (h b a) 0)
    (b : B) (A : W → G) (hA : ContinuousAt A 0)
    (L : W →L[ℝ] E) (c : W →L[ℝ] ℝ)
    (hd : HasFDerivAt (fun x => f (A x)) L 0) :
    HasFDerivAt (fun x => f (A x * D.exponential (c x • D.basis b)))
      (L + c.smulRight (h b (A 0))) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hu := right_frame_uniform_ray_expansion D f h hh hderiv b (A 0)
  have ht : Tendsto (fun x : W => (A x, c x)) (𝓝 0) (𝓝 (A 0, 0)) := by
    simpa [ContinuousAt] using hA.prodMk c.continuous.continuousAt
  have he := (hu.comp_tendsto ht).trans_isBigO (c.isBigO_id (𝓝 0))
  have hf := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd)
  have hs := hf.add he
  convert hs using 1
  funext x
  simp only [zero_add, map_zero, zero_smul, D.exponential_zero, mul_one,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Function.comp_apply]
  abel

theorem right_frame_product_hasFDerivAt_zero (D : Data G V B)
    (f : G → E) (h : B → G → E) (hh : ∀ b, Continuous (h b))
    (hderiv : ∀ (b : B) (a : G),
      HasDerivAt (fun t : ℝ => f (a * D.exponential (t • D.basis b))) (h b a) 0)
    (w : List B) (c : B → W →L[ℝ] ℝ) (a : G) :
    HasFDerivAt (fun x : W => f (a * (w.map
      (fun b => D.exponential (c b x • D.basis b))).prod))
      ((w.map (fun b => (c b).smulRight (h b a))).sum) 0 := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, V))
    (↑(⊤ : ℕ∞) : ℕ∞ω)
  induction w using List.reverseRecOn with
  | nil => simpa using (hasFDerivAt_const (𝕜 := ℝ) (f a) (0 : W))
  | append_singleton w b ih =>
    let A : W → G := fun x => a * (w.map
      (fun b => D.exponential (c b x • D.basis b))).prod
    have hA : Continuous A := by
      apply continuous_const.mul
      exact continuous_list_prod w (fun b _ => D.exponential_smooth.continuous.comp
        ((c b).continuous.smul continuous_const))
    have hA0 : A 0 = a := by
      dsimp [A]
      have hp : (w.map (fun b => D.exponential (c b 0 • D.basis b))).prod = 1 := by
        induction w with
        | nil => rfl
        | cons b w ih => simp [ih, D.exponential_zero]
      rw [hp, mul_one]
    have H := right_frame_insertion_hasFDerivAt_zero D f h hh hderiv b A
      hA.continuousAt _ (c b) ih
    simpa [List.map_append, List.prod_append, List.sum_append,
      mul_assoc, hA0, A] using H

end FiniteProducts

set_option backward.isDefEq.respectTransparency false in

theorem continuous_right_frame_contMDiff_one
    (D : Data G V B)
    (f : G → E) (h : B → G → E)
    (hf : Continuous f) (hh : ∀ b, Continuous (h b))
    (hderiv : ∀ (b : B) (a : G),
      HasDerivAt (fun t : ℝ => f (a * D.exponential (t • D.basis b))) (h b a) 0) :
    ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) 1 f := by
  classical
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, V)) (↑(⊤ : ℕ∞) : ℕ∞ω)
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  intro g
  obtain ⟨P, h0, hP, hp, hpi, hX, hbasis⟩ :=
    translated_exponential_frame D g
  have hPg : P 0 = g := by simpa [D.exponential_zero] using hP 0 h0
  let φ : V → E := fun a => f (P a)
  let X : B → V → V := fun b a => deriv
    (fun t : ℝ => P.symm (P a * D.exponential (t • D.basis b))) 0
  let A : V → V →L[ℝ] V := fun a => (D.basis.constr ℝ (fun b => X b a)).toContinuousLinearMap
  let H : V → V →L[ℝ] E := fun a => (D.basis.constr ℝ (fun b => h b (P a))).toContinuousLinearMap
  have hA (a : V) (ha : a ∈ P.source) : ContDiffAt ℝ (0 : ℕ∞ω) A a := by
    apply (contDiffWithinAt_clm_apply (s := Set.univ)).mpr
    intro v
    change ContDiffWithinAt ℝ (0 : ℕ∞ω)
      (fun a => (D.basis.constr ℝ (fun b => X b a)) v) Set.univ a
    simp only [Module.Basis.constr_apply_fintype]
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.sum
    intro b _
    exact ((hX b).contDiffAt (P.open_source.mem_nhds ha)).of_le (by simp) |>.const_smul _
  have hH (a : V) (ha : a ∈ P.source) : ContDiffAt ℝ (0 : ℕ∞ω) H a := by
    apply (contDiffWithinAt_clm_apply (s := Set.univ)).mpr
    intro v
    change ContDiffWithinAt ℝ (0 : ℕ∞ω)
      (fun a => (D.basis.constr ℝ (fun b => h b (P a))) v) Set.univ a
    simp only [Module.Basis.constr_apply_fintype]
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.sum
    intro b _
    apply ContDiffAt.const_smul
    rw [contDiffAt_zero]
    exact ⟨P.source, P.open_source.mem_nhds ha, (hh b).continuousOn.comp hp.continuousOn (fun _ hx => Set.mem_univ _)⟩
  have hinv (a : V) (ha : a ∈ P.source) : (A a).IsInvertible := by
    obtain ⟨F, hF⟩ := hbasis a ha
    let L := (D.basis.equiv F (Equiv.refl B)).toContinuousLinearEquiv
    refine ⟨L, ?_⟩
    apply ContinuousLinearMap.coe_injective
    apply D.basis.ext
    intro b
    simp [L, A, Module.Basis.constr_basis, hF, X]
  have hc (a : V) (ha : a ∈ P.source) : DifferentiableAt ℝ φ a := by
    let c : B → V →L[ℝ] ℝ := fun b =>
      (ContinuousLinearMap.proj b).comp D.basis.equivFun.toContinuousLinearEquiv.toContinuousLinearMap
    let w : List B := Finset.univ.toList
    let R : V → G := fun x => P a * (w.map
      (fun b => D.exponential (c b x • D.basis b))).prod
    have hR0 : R 0 = P a := by
      have hz : ∀ l : List B, (l.map (fun b => D.exponential (c b 0 • D.basis b))).prod = 1 := by
        intro l
        induction l with
        | nil => rfl
        | cons b l ih => simp [ih, D.exponential_zero]
      dsimp [R]
      rw [hz, mul_one]
    have hR : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞) R := by
      apply contMDiff_const.mul
      have ht : ∀ l : List B, ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞)
          (fun x => (l.map (fun b => D.exponential (c b x • D.basis b))).prod) := by
        intro l
        induction l with
        | nil => simpa using (contMDiff_const (c := (1 : G)))
        | cons b l ih =>
          simp only [List.map_cons, List.prod_cons]
          apply ContMDiff.mul _ ih
          change ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) (⊤ : ℕ∞)
            (D.exponential ∘ (fun x => c b x • D.basis b))
          exact D.exponential_smooth.comp
            ((c b).contDiff.contMDiff.smul contMDiff_const)
      exact ht w
    let Q : V → V := fun x => P.symm (R x)
    have hQ0 : Q 0 = a := by simp [Q, hR0, P.left_inv ha]
    have hQ : ContDiffAt ℝ 1 Q 0 := by
      exact (((hpi.of_le (by simp)).contMDiffAt
        (P.open_target.mem_nhds (P.map_source ha))).comp_of_eq
        ((hR.of_le (by simp)).contMDiffAt) hR0).contDiffAt
    have hQr (b : B) : (fun t : ℝ => Q (t • D.basis b)) =
        (fun t => P.symm (P a * D.exponential (t • D.basis b))) := by
      funext t
      dsimp [Q, R]
      congr 2
      rw [List.prod_map_eq_pow_single b]
      · rw [List.count_eq_one_of_mem (Finset.nodup_toList Finset.univ) (by simp)]
        simp [c]
      · intro b' hb' _
        simp [c, hb', D.exponential_zero]
    have hdQ : HasFDerivAt Q (A a) 0 := by
      convert hQ.differentiableAt_one.hasFDerivAt using 1
      apply ContinuousLinearMap.coe_injective
      apply D.basis.ext
      intro b
      have hr : HasDerivAt (fun t : ℝ => t • D.basis b) (D.basis b) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (D.basis b)
      have hd0 : HasFDerivAt Q (fderiv ℝ Q 0) ((0 : ℝ) • D.basis b) := by
        simpa using hQ.differentiableAt_one.hasFDerivAt
      have hd := hd0.comp_hasDerivAt 0 hr
      change HasDerivAt (fun t => Q (t • D.basis b)) _ 0 at hd
      rw [hQr b] at hd
      simpa [A, X, Module.Basis.constr_basis] using hd.deriv
    obtain ⟨L, hL⟩ := hinv a ha
    have hdL : HasFDerivAt Q (L : V →L[ℝ] V) 0 := by simpa [hL] using hdQ
    let S := hQ.localInverse hdL (by simp)
    have hS : ContDiffAt ℝ 1 S a := by
      simpa [hQ0, S] using hQ.to_localInverse hdL (by simp)
    have hS0 : S a = 0 := by
      simpa [hQ0, S] using hQ.localInverse_apply_image hdL (by simp)
    have hdR := right_frame_product_hasFDerivAt_zero D f h hh hderiv w c (P a)
    have hdRS : DifferentiableAt ℝ (fun y => f (R (S y))) a := by
      have hdR' : DifferentiableAt ℝ (fun x => f (R x)) (S a) := by
        simpa [hS0, R] using hdR.differentiableAt
      exact hdR'.comp a hS.differentiableAt_one
    have heq : (fun y => f (R (S y))) =ᶠ[𝓝 a] φ := by
      have hi : ∀ᶠ y in 𝓝 a, Q (S y) = y := by
        change ∀ᶠ y in 𝓝 a, Q (hQ.localInverse hdL (by simp) y) = y
        simpa only [hQ0, ContDiffAt.localInverse] using
          (hQ.hasStrictFDerivAt' hdL (by simp)).eventually_right_inverse
      have ht : ∀ᶠ y in 𝓝 a, R (S y) ∈ P.target := by
        have hcont : ContinuousAt (fun y => R (S y)) a := by
          exact hR.continuous.continuousAt.comp hS.continuousAt
        apply hcont.preimage_mem_nhds
        simp only [hS0, hR0]
        exact P.open_target.mem_nhds (P.map_source ha)
      filter_upwards [hi, ht] with y hy hty
      change f (R (S y)) = f (P y)
      exact congrArg f ((P.right_inv hty).symm.trans (congrArg P hy))
    exact hdRS.congr_of_eventuallyEq heq.symm
  have hrel (a : V) (ha : a ∈ P.source) :
      (fderiv ℝ φ a).comp (A a) = H a := by
    apply ContinuousLinearMap.coe_injective
    apply D.basis.ext
    intro b
    change (fderiv ℝ φ a) ((A a) (D.basis b)) = (H a) (D.basis b)
    simp only [A, H, LinearMap.coe_toContinuousLinearMap', Module.Basis.constr_basis]
    let c : ℝ → G := fun t => P a * D.exponential (t • D.basis b)
    have hc0 : c 0 = P a := by simp [c, D.exponential_zero]
    have hcs : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, V)) 1 c 0 := by
      exact contMDiffAt_const.mul ((D.exponential_smooth.of_le (by simp)).contMDiffAt.comp 0
        (contMDiffAt_id.smul contMDiffAt_const))
    have hci : ContDiffAt ℝ 1 (fun t => P.symm (c t)) 0 := by
      exact (((hpi.of_le (by simp)).contMDiffAt
        (P.open_target.mem_nhds (P.map_source ha))).comp_of_eq hcs hc0).contDiffAt
    have hdi : HasDerivAt (fun t => P.symm (c t)) (X b a) 0 := by
      exact hci.differentiableAt_one.hasDerivAt
    have hdφ : HasFDerivAt φ (fderiv ℝ φ a) (P.symm (c 0)) := by
      simpa only [hc0, P.left_inv ha] using (hc a ha).hasFDerivAt
    have hd := hdφ.comp_hasDerivAt 0 hdi
    have heq : (fun t => φ (P.symm (c t))) =ᶠ[nhds (0 : ℝ)] (fun t => f (c t)) := by
      have hn : ∀ᶠ t in nhds (0 : ℝ), c t ∈ P.target :=
        hcs.continuousAt.preimage_mem_nhds (by
          rw [hc0]
          exact P.open_target.mem_nhds (P.map_source ha))
      filter_upwards [hn] with t ht
      exact congrArg f (P.right_inv ht)
    exact (hd.congr_of_eventuallyEq heq.symm).unique (hderiv b (P a))
  have hfd (a : V) (ha : a ∈ P.source) :
      fderiv ℝ φ a = (H a).comp (ContinuousLinearMap.inverse (A a)) := by
    rw [← hrel a ha, ContinuousLinearMap.comp_assoc, (hinv a ha).self_comp_inverse,
      ContinuousLinearMap.comp_id]
  have hs : ContDiffAt ℝ (1 : ℕ∞ω) φ 0 := by
    apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨fun a => (H a).comp (ContinuousLinearMap.inverse (A a)),
      ⟨P.source, P.open_source.mem_nhds h0, ?_⟩, ?_⟩
    · intro a ha
      exact (hc a ha).hasFDerivAt.congr_fderiv (hfd a ha)
    · exact (hH 0 h0).clm_comp ((hinv 0 h0).contDiffAt_map_inverse.comp 0 (hA 0 h0))
  have hsi := (hpi.of_le (by simp : (1 : ℕ∞ω) ≤ (⊤ : ℕ∞))).contMDiffAt
    (P.open_target.mem_nhds (P.map_source h0))
  have hcomp := hs.contMDiffAt.comp_of_eq hsi (P.left_inv h0)
  have heq : (fun x => φ (P.symm x)) =ᶠ[nhds (P 0)] f := by
    filter_upwards [P.open_target.mem_nhds (P.map_source h0)] with x hx
    exact congrArg f (P.right_inv hx)
  rw [← hPg]
  apply heq.contMDiffAt_iff.mp
  change ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) (1 : ℕ∞ω)
    (φ ∘ P.symm) (P 0)
  exact hcomp

open scoped Manifold ContDiff

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V G]
  [LieGroup (𝓘(ℝ, V)) (↑(⊤ : ℕ∞) : ℕ∞ω) G]
variable {B : Type*} [Fintype B]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem right_frame_contMDiff_succ
    (D : Data G V B)
    (n : ℕ) (f : G → E) (h : B → G → E)
    (hf : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) 1 f)
    (hh : ∀ b, ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) (n : ℕ∞ω) (h b))
    (hderiv : ∀ (b : B) (a : G),
      HasDerivAt (fun t : ℝ => f (a * D.exponential (t • D.basis b))) (h b a) 0) :
    ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) ((n + 1 : ℕ) : ℕ∞ω) f := by
  classical
  intro g
  obtain ⟨P, h0, hP, hp, hpi, hX, hbasis⟩ :=
    translated_exponential_frame D g
  have hPg : P 0 = g := by simpa [D.exponential_zero] using hP 0 h0
  let φ : V → E := fun a => f (P a)
  let X : B → V → V := fun b a => deriv
    (fun t : ℝ => P.symm (P a * D.exponential (t • D.basis b))) 0
  let A : V → V →L[ℝ] V := fun a => (D.basis.constr ℝ (fun b => X b a)).toContinuousLinearMap
  let H : V → V →L[ℝ] E := fun a => (D.basis.constr ℝ (fun b => h b (P a))).toContinuousLinearMap
  have hc (a : V) (ha : a ∈ P.source) : ContDiffAt ℝ 1 φ a :=
    (hf.contMDiffAt.comp a ((hp.of_le (by simp)).contMDiffAt
      (P.open_source.mem_nhds ha))).contDiffAt
  have hA (a : V) (ha : a ∈ P.source) : ContDiffAt ℝ (n : ℕ∞ω) A a := by
    apply (contDiffWithinAt_clm_apply (s := Set.univ)).mpr
    intro v
    change ContDiffWithinAt ℝ (n : ℕ∞ω)
      (fun a => (D.basis.constr ℝ (fun b => X b a)) v) Set.univ a
    simp only [Module.Basis.constr_apply_fintype]
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.sum
    intro b _
    exact ((hX b).contDiffAt (P.open_source.mem_nhds ha)).of_le (by simp) |>.const_smul _
  have hH (a : V) (ha : a ∈ P.source) : ContDiffAt ℝ (n : ℕ∞ω) H a := by
    apply (contDiffWithinAt_clm_apply (s := Set.univ)).mpr
    intro v
    change ContDiffWithinAt ℝ (n : ℕ∞ω)
      (fun a => (D.basis.constr ℝ (fun b => h b (P a))) v) Set.univ a
    simp only [Module.Basis.constr_apply_fintype]
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.sum
    intro b _
    exact ((hh b).contMDiffAt.comp a ((hp.of_le (by simp)).contMDiffAt
      (P.open_source.mem_nhds ha))).contDiffAt.const_smul _
  have hinv (a : V) (ha : a ∈ P.source) : (A a).IsInvertible := by
    obtain ⟨F, hF⟩ := hbasis a ha
    let L := (D.basis.equiv F (Equiv.refl B)).toContinuousLinearEquiv
    refine ⟨L, ?_⟩
    apply ContinuousLinearMap.coe_injective
    apply D.basis.ext
    intro b
    simp [L, A, Module.Basis.constr_basis, hF, X]
  have hrel (a : V) (ha : a ∈ P.source) :
      (fderiv ℝ φ a).comp (A a) = H a := by
    apply ContinuousLinearMap.coe_injective
    apply D.basis.ext
    intro b
    change (fderiv ℝ φ a) ((A a) (D.basis b)) = (H a) (D.basis b)
    simp only [A, H, LinearMap.coe_toContinuousLinearMap', Module.Basis.constr_basis]
    let c : ℝ → G := fun t => P a * D.exponential (t • D.basis b)
    have hc0 : c 0 = P a := by simp [c, D.exponential_zero]
    have hcs : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, V)) 1 c 0 := by
      exact contMDiffAt_const.mul ((D.exponential_smooth.of_le (by simp)).contMDiffAt.comp 0
        (contMDiffAt_id.smul contMDiffAt_const))
    have hci : ContDiffAt ℝ 1 (fun t => P.symm (c t)) 0 := by
      exact (((hpi.of_le (by simp)).contMDiffAt
        (P.open_target.mem_nhds (P.map_source ha))).comp_of_eq hcs hc0).contDiffAt
    have hdi : HasDerivAt (fun t => P.symm (c t)) (X b a) 0 := by
      exact hci.differentiableAt_one.hasDerivAt
    have hdφ : HasFDerivAt φ (fderiv ℝ φ a) (P.symm (c 0)) := by
      simpa only [hc0, P.left_inv ha] using (hc a ha).differentiableAt_one.hasFDerivAt
    have hd := hdφ.comp_hasDerivAt 0 hdi
    have heq : (fun t => φ (P.symm (c t))) =ᶠ[nhds (0 : ℝ)] (fun t => f (c t)) := by
      have hn : ∀ᶠ t in nhds (0 : ℝ), c t ∈ P.target :=
        hcs.continuousAt.preimage_mem_nhds (by
          rw [hc0]
          exact P.open_target.mem_nhds (P.map_source ha))
      filter_upwards [hn] with t ht
      exact congrArg f (P.right_inv ht)
    exact (hd.congr_of_eventuallyEq heq.symm).unique (hderiv b (P a))
  have hfd (a : V) (ha : a ∈ P.source) :
      fderiv ℝ φ a = (H a).comp (ContinuousLinearMap.inverse (A a)) := by
    rw [← hrel a ha, ContinuousLinearMap.comp_assoc, (hinv a ha).self_comp_inverse,
      ContinuousLinearMap.comp_id]
  have hs : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ∞ω) φ 0 := by
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun a => (H a).comp (ContinuousLinearMap.inverse (A a)),
      ⟨P.source, P.open_source.mem_nhds h0, ?_⟩, ?_⟩
    · intro a ha
      exact (hc a ha).differentiableAt_one.hasFDerivAt.congr_fderiv (hfd a ha)
    · exact (hH 0 h0).clm_comp ((hinv 0 h0).contDiffAt_map_inverse.comp 0 (hA 0 h0))
  have hsi := (hpi.of_le (by simp : ((n + 1 : ℕ) : ℕ∞ω) ≤ (⊤ : ℕ∞))).contMDiffAt
    (P.open_target.mem_nhds (P.map_source h0))
  have hcomp := hs.contMDiffAt.comp_of_eq hsi (P.left_inv h0)
  have heq : (fun x => φ (P.symm x)) =ᶠ[nhds (P 0)] f := by
    filter_upwards [P.open_target.mem_nhds (P.map_source h0)] with x hx
    exact congrArg f (P.right_inv hx)
  rw [← hPg]
  apply heq.contMDiffAt_iff.mp
  change ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ((n + 1 : ℕ) : ℕ∞ω)
    (φ ∘ P.symm) (P 0)
  exact hcomp

end RawFrame

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V G] [LieGroup (𝓘(ℝ, V)) ∞ G]
variable {B : Type*} [Fintype B]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem translated_basis_derivative_at
    (basis : Module.Basis B ℝ V) (exponential : V → G)
    (hexp_add : ∀ (X : V) (s t : ℝ),
      exponential ((s + t) • X) = exponential (s • X) * exponential (t • X))
    (f : G → E) (D : B → G → E)
    (hderiv : ∀ b g, HasDerivAt
      (fun t : ℝ => f (g * exponential (t • basis b))) (D b g) 0)
    (b : B) (g : G) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * exponential (s • basis b)))
      (D b (g * exponential (t • basis b))) t := by
  have hd := (hderiv b (g * exponential (t • basis b))).scomp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  simp only [one_smul] at hd
  convert hd using 1
  funext s
  dsimp only [Function.comp_apply, id]
  rw [mul_assoc, ← hexp_add, add_sub_cancel]

theorem translated_basis_orbit_contDiff
    (basis : Module.Basis B ℝ V) (exponential : V → G)
    (hexp_add : ∀ (X : V) (s t : ℝ),
      exponential ((s + t) • X) = exponential (s • X) * exponential (t • X))
    (hexp_smooth : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ exponential)
    (n : ℕ) (f : G → E) (D : B → G → E)
    (hD : ∀ b, ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) n (D b))
    (hderiv : ∀ b g, HasDerivAt
      (fun t : ℝ => f (g * exponential (t • basis b))) (D b g) 0)
    (b : B) (g : G) :
    ContDiff ℝ (n + 1 : ℕ) (fun t : ℝ => f (g * exponential (t • basis b))) := by
  have hd := translated_basis_derivative_at basis exponential hexp_add f D hderiv b g
  rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
    contDiff_succ_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
  have he : deriv (fun t : ℝ => f (g * exponential (t • basis b))) =
      fun t : ℝ => D b (g * exponential (t • basis b)) := by
    funext t
    exact (hd t).deriv
  rw [he]
  apply ContMDiff.contDiff
  apply (hD b).comp
  apply contMDiff_const.mul
  apply (hexp_smooth.of_le (by simp)).comp
  exact (contDiff_id.smul contDiff_const).contMDiff

theorem contMDiff_succ_of_translated_basis_derivatives
    (basis : Module.Basis B ℝ V) (exponential : V → G)
    (hexp_zero : exponential 0 = 1)
    (hexp_add : ∀ (X : V) (s t : ℝ),
      exponential ((s + t) • X) = exponential (s • X) * exponential (t • X))
    (hexp_smooth : ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ exponential)
    (chart : PartialDiffeomorph (𝓘(ℝ, V)) (𝓘(ℝ, V)) V G ∞)
    (hzero : (0 : V) ∈ chart.toPartialEquiv.source)
    (hchart : ∀ X ∈ chart.toPartialEquiv.source, chart X = exponential X)
    (n : ℕ) (f : G → E) (D : B → G → E)
    (hf : Continuous f)
    (hD : ∀ b, ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) n (D b))
    (hderiv : ∀ b g, HasDerivAt
      (fun t : ℝ => f (g * exponential (t • basis b))) (D b g) 0) :
    ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, E)) (n + 1 : ℕ) f := by
  let d : RawFrame.Data G V B := {
    basis := basis
    exponential := exponential
    exponential_zero := hexp_zero
    exponential_add_ray := hexp_add
    exponential_smooth := hexp_smooth
    exponentialChart := chart
    zero_mem_source := hzero
    chart_eq_exponential := hchart }
  have hc := RawFrame.continuous_right_frame_contMDiff_one d f D hf
    (fun b => (hD b).continuous) hderiv
  exact RawFrame.right_frame_contMDiff_succ d n f D hc hD hderiv

end DedekindZetaZeroFree.SmoothWordOrbit.DomainToSmooth

end
