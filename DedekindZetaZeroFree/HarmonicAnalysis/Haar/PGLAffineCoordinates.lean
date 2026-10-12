module

public import Mathlib

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AffineLie
open MeasureTheory Topology
open scoped Matrix.Norms.Operator Manifold ContDiff

abbrev RawGroup := Matrix.ProjGenLinGroup (Fin 2) ℂ
abbrev RawCoordinates := Fin 6 → ℝ

local instance : TopologicalSpace RawGroup := inferInstanceAs
  (TopologicalSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))
local instance : IsTopologicalGroup RawGroup := inferInstanceAs
  (IsTopologicalGroup (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

def rawComplexCoordinates (x : RawCoordinates) : Fin 3 → ℂ :=
  ![⟨x 0, x 1⟩, ⟨x 2, x 3⟩, ⟨x 4, x 5⟩]

def rawMatrix (x : RawCoordinates) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, rawComplexCoordinates x 1; rawComplexCoordinates x 2, 1 + rawComplexCoordinates x 0]

def rawDelta (x : RawCoordinates) : ℂ :=
  1 + rawComplexCoordinates x 0 - rawComplexCoordinates x 1 * rawComplexCoordinates x 2

theorem rawMatrix_det (x : RawCoordinates) : (rawMatrix x).det = rawDelta x := by
  simp [rawMatrix, rawDelta, Matrix.det_fin_two]

structure NormalizedChart (h : OpenPartialHomeomorph RawCoordinates RawGroup) : Prop where
  source : h.source = {x | rawDelta x ≠ 0}
  target : h.target = {g | g.out.val 0 0 ≠ 0}
  displayed : ∀ (x : RawCoordinates) (hx : rawDelta x ≠ 0), h x =
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero (rawMatrix x)
      (by rwa [rawMatrix_det]))

def rawRatios (a : Matrix (Fin 2) (Fin 2) ℂ) : RawCoordinates :=
  let u := a 1 1 / a 0 0 - 1
  let b := a 0 1 / a 0 0
  let c := a 1 0 / a 0 0
  ![u.re, u.im, b.re, b.im, c.re, c.im]

def rawMultiply (p : RawCoordinates × RawCoordinates) : RawCoordinates :=
  rawRatios (rawMatrix p.1 * rawMatrix p.2)

end DedekindZetaZeroFree.PGLComplex.AffineLie

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AffineLie
open MeasureTheory Topology Set
open scoped Matrix.Norms.Operator Manifold ContDiff
local instance translationJacobianTopology : TopologicalSpace RawGroup := inferInstanceAs
  (TopologicalSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))
local instance translationJacobianTopologicalGroup : IsTopologicalGroup RawGroup := inferInstanceAs
  (IsTopologicalGroup (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

private theorem tj_rawMatrix_rawRatios (a : Matrix (Fin 2) (Fin 2) ℂ) (ha : a 0 0 ≠ 0) :
    rawMatrix (rawRatios a) = (a 0 0)⁻¹ • a := by
  have h0 : rawComplexCoordinates (rawRatios a) 0 = a 1 1 / a 0 0 - 1 := by
    apply Complex.ext <;> simp [rawComplexCoordinates, rawRatios]
  have h1 : rawComplexCoordinates (rawRatios a) 1 = a 0 1 / a 0 0 := by
    apply Complex.ext <;> simp [rawComplexCoordinates, rawRatios]
  have h2 : rawComplexCoordinates (rawRatios a) 2 = a 1 0 / a 0 0 := by
    apply Complex.ext <;> simp [rawComplexCoordinates, rawRatios]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawMatrix, h0, h1, h2, Matrix.smul_apply, ha, div_eq_mul_inv, mul_comm]

private theorem tj_rawDelta_rawRatios (a : Matrix (Fin 2) (Fin 2) ℂ) (ha : a 0 0 ≠ 0) :
    rawDelta (rawRatios a) = a.det / (a 0 0) ^ 2 := by
  rw [← rawMatrix_det, tj_rawMatrix_rawRatios a ha, Matrix.det_smul]
  simp [Fintype.card_fin, div_eq_mul_inv, mul_comm]

private theorem tj_rawDelta_multiply (x y : RawCoordinates)
    (hxy : 1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0) :
    rawDelta (rawMultiply (x, y)) = rawDelta x * rawDelta y /
      (1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2) ^ 2 := by
  have h00 : (rawMatrix x * rawMatrix y) 0 0 =
      1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, rawMatrix]
  rw [rawMultiply, tj_rawDelta_rawRatios _ (h00 ▸ hxy), Matrix.det_mul,
    rawMatrix_det, rawMatrix_det, h00]

private theorem tj_rawMultiply_mem_source
    (h : OpenPartialHomeomorph RawCoordinates RawGroup) (hn : NormalizedChart h)
    (x y : RawCoordinates) (hx : x ∈ h.source) (hy : y ∈ h.source)
    (hxy : 1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0) :
    rawMultiply (x, y) ∈ h.source := by
  rw [hn.source] at hx hy ⊢
  change rawDelta (rawMultiply (x,y)) ≠ 0
  rw [tj_rawDelta_multiply x y hxy]
  exact div_ne_zero (mul_ne_zero hx hy) (pow_ne_zero 2 hxy)

private theorem tj_rawMultiply_chart
    (h : OpenPartialHomeomorph RawCoordinates RawGroup) (hn : NormalizedChart h)
    (x y : RawCoordinates) (hx : x ∈ h.source) (hy : y ∈ h.source)
    (hxy : 1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0) :
    h (rawMultiply (x, y)) = h x * h y := by
  have hx' : rawDelta x ≠ 0 := by simpa [hn.source] using hx
  have hy' : rawDelta y ≠ 0 := by simpa [hn.source] using hy
  have hm := tj_rawMultiply_mem_source h hn x y hx hy hxy
  have hm' : rawDelta (rawMultiply (x, y)) ≠ 0 := by simpa [hn.source] using hm
  set_option backward.isDefEq.respectTransparency false in
    simp only [hn.displayed _ hm', hn.displayed _ hx', hn.displayed _ hy']
  rw [← map_mul Matrix.ProjGenLinGroup.mk]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  have h00 : (rawMatrix x * rawMatrix y) 0 0 =
      1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, rawMatrix]
  have hnz : (rawMatrix x * rawMatrix y) 0 0 ≠ 0 := h00 ▸ hxy
  refine ⟨Units.mk0 ((rawMatrix x * rawMatrix y) 0 0) hnz, Units.ext ?_⟩
  change rawMatrix (rawMultiply (x,y)) *
    Matrix.scalar (Fin 2) ((rawMatrix x * rawMatrix y) 0 0) = rawMatrix x * rawMatrix y
  rw [rawMultiply, tj_rawMatrix_rawRatios _ hnz]
  ext i j
  simp [Matrix.mul_diagonal, smul_eq_mul, hnz]
  field_simp

private theorem tj_rawMultiply_inverse_chart
    (h : OpenPartialHomeomorph RawCoordinates RawGroup) (hn : NormalizedChart h)
    (x y : RawCoordinates) (hx : x ∈ h.source) (hy : y ∈ h.source)
    (hxy : 1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0) :
    h.symm (h x * h y) = rawMultiply (x, y) := by
  rw [← tj_rawMultiply_chart h hn x y hx hy hxy]
  exact h.left_inv (tj_rawMultiply_mem_source h hn x y hx hy hxy)

private theorem tj_zero_mem (h : OpenPartialHomeomorph RawCoordinates RawGroup)
    (hn : NormalizedChart h) : (0 : RawCoordinates) ∈ h.source := by
  simp [hn.source, rawDelta, rawComplexCoordinates, Complex.mk_eq_add_mul_I]

private theorem tj_chart_zero (h : OpenPartialHomeomorph RawCoordinates RawGroup)
    (hn : NormalizedChart h) : h 0 = 1 := by
  set_option backward.isDefEq.respectTransparency false in
    rw [hn.displayed 0 (by simp [rawDelta, rawComplexCoordinates, Complex.mk_eq_add_mul_I])]
  rw [← map_one Matrix.ProjGenLinGroup.mk]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rawMatrix, rawComplexCoordinates, Complex.mk_eq_add_mul_I]

private theorem tj_multiply_zero (x : RawCoordinates) : rawMultiply (x, 0) = x := by
  ext i
  fin_cases i <;> simp [rawMultiply, rawRatios, rawMatrix, rawComplexCoordinates,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.mk_eq_add_mul_I]

private theorem tj_eventually_chart (h : OpenPartialHomeomorph RawCoordinates RawGroup)
    (hn : NormalizedChart h) (x : RawCoordinates) (hx : x ∈ h.source) :
    (fun y => h.symm (h x * h y)) =ᶠ[𝓝 (0 : RawCoordinates)]
      (fun y => rawMultiply (x, y)) := by
  have hc : Continuous (fun y : RawCoordinates =>
      1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2) := by
    simp [rawComplexCoordinates, Complex.mk_eq_add_mul_I]
    fun_prop
  have he : ∀ᶠ y in 𝓝 (0 : RawCoordinates),
      1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0 :=
    hc.continuousAt.eventually_ne (by simp [rawComplexCoordinates, Complex.mk_eq_add_mul_I])
  filter_upwards [he, h.open_source.mem_nhds (tj_zero_mem h hn)] with y hy hy'
  exact tj_rawMultiply_inverse_chart h hn x y hx hy' hy

private theorem tj_eventually_comp (h : OpenPartialHomeomorph RawCoordinates RawGroup)
    (hn : NormalizedChart h) (g : RawGroup) (x z : RawCoordinates)
    (hx : x ∈ h.source) (hz : z ∈ h.source) (hgz : h z = g * h x) :
    (fun y => h.symm (g * h (rawMultiply (x, y)))) =ᶠ[𝓝 (0 : RawCoordinates)]
      (fun y => rawMultiply (z, y)) := by
  have he (a : RawCoordinates) : ∀ᶠ y in 𝓝 (0 : RawCoordinates),
      1 + rawComplexCoordinates a 1 * rawComplexCoordinates y 2 ≠ 0 := by
    have hc : Continuous (fun y : RawCoordinates =>
        1 + rawComplexCoordinates a 1 * rawComplexCoordinates y 2) := by
      simp [rawComplexCoordinates, Complex.mk_eq_add_mul_I]
      fun_prop
    exact hc.continuousAt.eventually_ne (by simp [rawComplexCoordinates,
      Complex.mk_eq_add_mul_I])
  filter_upwards [he x, he z, h.open_source.mem_nhds (tj_zero_mem h hn)] with y hyx hyz hy
  rw [tj_rawMultiply_chart h hn x y hx hy hyx, ← mul_assoc, ← hgz]
  exact tj_rawMultiply_inverse_chart h hn z y hz hy hyz

private theorem tj_translation_diff
    (h : OpenPartialHomeomorph RawCoordinates RawGroup)
    [C : ChartedSpace RawCoordinates RawGroup]
    [LieGroup (𝓘(ℝ, RawCoordinates)) (↑(⊤ : ℕ∞) : ℕ∞ω) RawGroup]
    (hchart : ∀ g, C.chartAt g =
      (h.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm)
    (g : RawGroup) (x : RawCoordinates) (hx : x ∈ h.source)
    (hgx : g * h x ∈ h.target) :
    DifferentiableAt ℝ (fun y => h.symm (g * h y)) x := by
  let e := (chartAt RawCoordinates g).symm.trans (chartAt RawCoordinates (1 : RawGroup))
  have he : e ∈ contDiffGroupoid (↑(⊤ : ℕ∞) : ℕ∞ω) (𝓘(ℝ, RawCoordinates)) :=
    StructureGroupoid.compatible _ (chart_mem_atlas _ g) (chart_mem_atlas _ 1)
  have hs : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (⇑e) e.source := by
    simpa [contDiffGroupoid, contDiffPregroupoid, Function.comp_def] using
      (mem_groupoid_of_pregroupoid.mp he).1
  have hx' : x ∈ e.source := by
    simpa [e, Homeomorph.mulLeft_symm, hchart, OpenPartialHomeomorph.trans_source, hx] using hgx
  have hd := (hs.contDiffAt (e.open_source.mem_nhds hx')).differentiableAt (by simp)
  simpa [e, Homeomorph.mulLeft_symm, hchart, Function.comp_def] using hd

theorem normalized_chart_translation_jacobian
    (h : OpenPartialHomeomorph RawCoordinates RawGroup) (hn : NormalizedChart h)
    [C : ChartedSpace RawCoordinates RawGroup]
    [LieGroup (𝓘(ℝ, RawCoordinates)) (↑(⊤ : ℕ∞) : ℕ∞ω) RawGroup]
    (hchart : ∀ g, C.chartAt g =
      (h.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm)
    (F : RawCoordinates → RawCoordinates →L[ℝ] RawCoordinates)
    (hderiv : ∀ x, HasFDerivAt (fun y => rawMultiply (x, y)) (F x) 0)
    (hdet : ∀ x, (F x).toLinearMap.det = ‖rawDelta x‖ ^ 4)
    (g : RawGroup) :
    ∃ J : RawCoordinates → RawCoordinates →L[ℝ] RawCoordinates,
      ∀ x ∈ h.source, g * h x ∈ h.target →
        HasFDerivAt (fun y => h.symm (g * h y)) (J x) x ∧
        (1 / ‖rawDelta (h.symm (g * h x))‖ ^ 4) * |(J x).toLinearMap.det| =
          1 / ‖rawDelta x‖ ^ 4 := by
  classical
  let T : RawCoordinates → RawCoordinates := fun y => h.symm (g * h y)
  refine ⟨fun x => fderiv ℝ T x, ?_⟩
  intro x hx hgx
  have hd : HasFDerivAt T (fderiv ℝ T x) x :=
    (tj_translation_diff h hchart g x hx hgx).hasFDerivAt
  refine ⟨hd, ?_⟩
  let z := T x
  have hz : z ∈ h.source := h.symm.map_source hgx
  have hgz : h z = g * h x := h.right_inv hgx
  have hcomp : HasFDerivAt (fun y => rawMultiply (z, y))
      ((fderiv ℝ T x).comp (F x)) 0 := by
    have hd' : HasFDerivAt T (fderiv ℝ T x) (rawMultiply (x, 0)) := by
      simpa only [tj_multiply_zero] using hd
    have H := hd'.comp 0 (hderiv x)
    exact H.congr_of_eventuallyEq (tj_eventually_comp h hn g x z hx hz hgz).symm
  have hmaps := hcomp.unique (hderiv z)
  have heq : (fderiv ℝ T x).toLinearMap.det * ‖rawDelta x‖ ^ 4 =
      ‖rawDelta z‖ ^ 4 := by
    have H := congrArg (fun A : RawCoordinates →L[ℝ] RawCoordinates =>
      A.toLinearMap.det) hmaps
    simpa only [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, hdet] using H
  have hxpos : 0 < ‖rawDelta x‖ ^ 4 := pow_pos (norm_pos_iff.mpr
    (by simpa only [hn.source, mem_setOf_eq] using hx)) 4
  have hzpos : 0 < ‖rawDelta z‖ ^ 4 := pow_pos (norm_pos_iff.mpr
    (by simpa only [hn.source, mem_setOf_eq] using hz)) 4
  have hJpos : 0 < (fderiv ℝ T x).toLinearMap.det := by
    nlinarith
  change (1 / ‖rawDelta z‖ ^ 4) * |(fderiv ℝ T x).toLinearMap.det| =
    1 / ‖rawDelta x‖ ^ 4
  rw [abs_of_pos hJpos]
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_eq_div_iff hzpos.ne' hxpos.ne').mpr
  simpa only [one_mul] using heq

end DedekindZetaZeroFree.PGLComplex.AffineLie

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AffineLie
local instance secondCountableQuotientTopology : TopologicalSpace RawGroup := inferInstanceAs
  (TopologicalSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology ((Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

local instance : SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  Units.isInducing_embedProduct.secondCountableTopology

theorem rawGroup_secondCountableTopology : SecondCountableTopology RawGroup :=
  inferInstanceAs (SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

end DedekindZetaZeroFree.PGLComplex.AffineLie

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AffineLie
open MeasureTheory Topology Set

private lemma preimage_inter_source {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Nonempty Y] (f : X → Y) (U : Set X) (hf : ContinuousOn f U)
    (hU : MeasurableSet U) (s : Set Y) (hs : MeasurableSet s) :
    MeasurableSet (f ⁻¹' s ∩ U) := by
  classical
  let c : Y := Classical.choice inferInstance
  have hm := hf.measurable_piecewise (g := fun _ => c) continuousOn_const hU
  have he : f ⁻¹' s ∩ U = (U.piecewise f (fun _ => c)) ⁻¹' s ∩ U := by
    ext x
    by_cases hx : x ∈ U <;> simp [hx]
  rw [he]
  exact (hm hs).inter hU

theorem translated_chart_measures_compatible_of_jacobian
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {n : ℕ}
    (h : OpenPartialHomeomorph (Fin n → ℝ) G)
    (w : (Fin n → ℝ) → ℝ) (hw : ContinuousOn w h.source)
    (hp : ∀ x ∈ h.source, 0 < w x) (hm : Measurable w)
    (hjac : ∀ g : G, ∃ J : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
      ∀ x ∈ h.source, g * h x ∈ h.target →
        HasFDerivAt (fun y => h.symm (g * h y)) (J x) x ∧
        w (h.symm (g * h x)) * |(J x).toLinearMap.det| = w x) :
    ∀ g k : G,
      (Measure.map (g * ·) (Measure.map h
        ((volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source))).restrict
        ({x | g⁻¹ * x ∈ h.target} ∩ {x | k⁻¹ * x ∈ h.target}) =
      (Measure.map (k * ·) (Measure.map h
        ((volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source))).restrict
        ({x | g⁻¹ * x ∈ h.target} ∩ {x | k⁻¹ * x ∈ h.target}) := by
  classical
  intro g k
  let ρ : Measure (Fin n → ℝ) := volume.withDensity (fun x => ENNReal.ofReal (w x))
  let p (a : G) : (Fin n → ℝ) → G := fun x => a * h x
  have hc (a : G) : ContinuousOn (p a) h.source :=
    continuousOn_const.mul h.continuousOn
  have ha (a : G) : AEMeasurable (p a) (ρ.restrict h.source) :=
    (hc a).aemeasurable h.open_source.measurableSet
  have hh : AEMeasurable h (ρ.restrict h.source) :=
    h.continuousOn.aemeasurable h.open_source.measurableSet
  have hmmap (a : G) : Measure.map (a * ·) (Measure.map h (ρ.restrict h.source)) =
      Measure.map (p a) (ρ.restrict h.source) :=
    AEMeasurable.map_map_of_aemeasurable
      (measurable_id.const_mul a).aemeasurable hh
  change (Measure.map (g * ·) (Measure.map h (ρ.restrict h.source))).restrict _ =
    (Measure.map (k * ·) (Measure.map h (ρ.restrict h.source))).restrict _
  rw [hmmap g, hmmap k]
  let O : Set G := {x | g⁻¹ * x ∈ h.target} ∩ {x | k⁻¹ * x ∈ h.target}
  have hO : MeasurableSet O :=
    (h.open_target.preimage (continuous_const.mul continuous_id)).measurableSet.inter
      (h.open_target.preimage (continuous_const.mul continuous_id)).measurableSet
  apply Measure.ext
  intro t ht
  let s := t ∩ O
  have hs : MeasurableSet s := ht.inter hO
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  change Measure.map (p g) (ρ.restrict h.source) s =
    Measure.map (p k) (ρ.restrict h.source) s
  rw [Measure.map_apply_of_aemeasurable (ha g) hs,
      Measure.map_apply_of_aemeasurable (ha k) hs,
      Measure.restrict_apply' h.open_source.measurableSet,
      Measure.restrict_apply' h.open_source.measurableSet]
  let D (a : G) := p a ⁻¹' s ∩ h.source
  have hD (a : G) : MeasurableSet (D a) :=
    preimage_inter_source (p a) h.source (hc a) h.open_source.measurableSet s hs
  change ρ (D g) = ρ (D k)
  change (volume.withDensity (fun x => ENNReal.ofReal (w x))) (D g) =
    (volume.withDensity (fun x => ENNReal.ofReal (w x))) (D k)
  rw [withDensity_apply _ (hD g), withDensity_apply _ (hD k)]
  let F : (Fin n → ℝ) → (Fin n → ℝ) := fun x => h.symm (k⁻¹ * (g * h x))
  obtain ⟨J, hJ⟩ := hjac (k⁻¹ * g)
  have htarget (x : Fin n → ℝ) (hx : x ∈ D g) : k⁻¹ * (g * h x) ∈ h.target :=
    hx.1.2.2
  have hFx (x : Fin n → ℝ) (hx : x ∈ D g) :
      h (F x) = k⁻¹ * (g * h x) := h.right_inv (htarget x hx)
  have himage : F '' D g = D k := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, h.map_target (htarget x hx)⟩
      change k * h (F x) ∈ s
      rw [hFx x hx, mul_inv_cancel_left]
      exact hx.1
    · intro hy
      let x := h.symm (g⁻¹ * (k * h y))
      have hxt : g⁻¹ * (k * h y) ∈ h.target := hy.1.2.1
      have hxs : x ∈ h.source := h.map_target hxt
      have hxh : h x = g⁻¹ * (k * h y) := h.right_inv hxt
      have hx : x ∈ D g := by
        refine ⟨?_, hxs⟩
        change g * h x ∈ s
        rw [hxh, mul_inv_cancel_left]
        exact hy.1
      refine ⟨x, hx, ?_⟩
      change h.symm (k⁻¹ * (g * h x)) = y
      rw [hxh, mul_inv_cancel_left, inv_mul_cancel_left, h.left_inv hy.2]
  have hd : ∀ x ∈ D g, HasFDerivWithinAt F (J x) (D g) x := by
    intro x hx
    have H := (hJ x hx.2 (by simpa only [mul_assoc] using htarget x hx)).1
    exact (show HasFDerivAt F (J x) x by simpa only [F, mul_assoc] using H).hasFDerivWithinAt
  have hinj : InjOn F (D g) := by
    intro x hx y hy he
    apply h.injOn hx.2 hy.2
    exact mul_left_cancel (mul_left_cancel (by simpa only [hFx x hx, hFx y hy] using congrArg h he))
  have heq : ∀ x ∈ D g,
      ENNReal.ofReal |(J x).toLinearMap.det| * ENNReal.ofReal (w (F x)) =
        ENNReal.ofReal (w x) := by
    intro x hx
    rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
    exact congrArg ENNReal.ofReal
      (by simpa only [F, mul_assoc] using
        (hJ x hx.2 (by simpa only [mul_assoc] using htarget x hx)).2)
  rw [← himage, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hD g) hd hinj]
  exact setLIntegral_congr_fun (hD g) (fun x hx => (heq x hx).symm)

end DedekindZetaZeroFree.PGLComplex.AffineLie

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AffineLie
open MeasureTheory Topology Set
open scoped Matrix.Norms.Operator Manifold ContDiff
local instance affineTopology : TopologicalSpace RawGroup := inferInstanceAs
  (TopologicalSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))
local instance affineTopologicalGroup : IsTopologicalGroup RawGroup := inferInstanceAs
  (IsTopologicalGroup (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

theorem glue_measures {X : Type*} [MeasurableSpace X]
    (s : ℕ → Set X) (hs : ∀ i, MeasurableSet (s i)) (hcover : ⋃ i, s i = univ)
    (μ : ℕ → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (s i ∩ s j) = (μ j).restrict (s i ∩ s j)) :
    ∃ ν : Measure X, ∀ i, ν.restrict (s i) = (μ i).restrict (s i) := by
  classical
  let d := disjointed s
  have hd : ∀ i, MeasurableSet (d i) := fun i => MeasurableSet.disjointed hs i
  have hdc : ⋃ i, d i = univ := by rw [iUnion_disjointed, hcover]
  refine ⟨Measure.sum (fun i => (μ i).restrict (d i)), fun j => ?_⟩
  rw [Measure.restrict_sum _ (hs j)]
  calc
    Measure.sum (fun i => ((μ i).restrict (d i)).restrict (s j)) =
        Measure.sum (fun i => ((μ j).restrict (s j)).restrict (d i)) := by
      apply Measure.sum_congr
      intro i
      rw [Measure.restrict_restrict (hs j), Measure.restrict_restrict (hd i)]
      have hi : s j ∩ d i ⊆ s i ∩ s j := by
        intro x hx
        exact ⟨disjointed_subset s i hx.2, hx.1⟩
      have H := congrArg (fun ν : Measure X => ν.restrict (s j ∩ d i)) (hcompat i j)
      rw [Measure.restrict_restrict ((hs j).inter (hd i)),
        Measure.restrict_restrict ((hs j).inter (hd i)), inter_eq_left.mpr hi] at H
      simpa only [inter_comm] using H
    _ = (μ j).restrict (s j) := by
      rw [← Measure.restrict_iUnion (disjoint_disjointed s) hd, hdc, Measure.restrict_univ]

theorem glue_open_measures {X I : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty I]
    (s : I → Set X) (hs : ∀ i, IsOpen (s i)) (hcover : ⋃ i, s i = univ)
    (μ : I → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (s i ∩ s j) = (μ j).restrict (s i ∩ s j)) :
    ∃ ν : Measure X, ∀ i, ν.restrict (s i) = (μ i).restrict (s i) := by
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover s hs (by rw [hcover])
  have hc : ⋃ j, s (f j) = univ := univ_subset_iff.mp hf
  obtain ⟨ν, hν⟩ := glue_measures (s ∘ f) (fun j => (hs (f j)).measurableSet) hc
    (μ ∘ f) (fun i j => hcompat (f i) (f j))
  simp only [Function.comp_apply] at hν
  refine ⟨ν, fun i => ?_⟩
  apply Measure.ext_of_iUnion_eq_univ hc
  intro j
  rw [Measure.restrict_restrict (hs (f j)).measurableSet]
  rw [inter_comm, ← Measure.restrict_restrict (hs i).measurableSet,
    hν j, Measure.restrict_restrict (hs i).measurableSet]
  rw [Measure.restrict_restrict (hs (f j)).measurableSet]
  simpa only [inter_comm] using hcompat (f j) i

theorem rawDelta_continuous : Continuous rawDelta := by
  have hu : ∀ i, Continuous (fun x : RawCoordinates => rawComplexCoordinates x i) := by
    intro i
    fin_cases i <;> simp [rawComplexCoordinates, Complex.mk_eq_add_mul_I] <;> fun_prop
  exact continuous_const.add (hu 0) |>.sub ((hu 1).mul (hu 2))
theorem rawDensity_measurable : Measurable (fun x : RawCoordinates =>
    ENNReal.ofReal (1 / ‖rawDelta x‖ ^ 4)) := by
  exact (measurable_const.div (rawDelta_continuous.measurable.norm.pow_const 4)).ennreal_ofReal
theorem rawDensity_positive (h : OpenPartialHomeomorph RawCoordinates RawGroup)
    (hn : NormalizedChart h) (x : RawCoordinates) (hx : x ∈ h.source) :
    0 < 1 / ‖rawDelta x‖ ^ 4 := by
  have hd : rawDelta x ≠ 0 := by simpa only [hn.source, Set.mem_setOf_eq] using hx
  exact one_div_pos.mpr (pow_pos (norm_pos_iff.mpr hd) 4)
theorem rawDensity_continuousOn (h : OpenPartialHomeomorph RawCoordinates RawGroup)
    (hn : NormalizedChart h) : ContinuousOn (fun x : RawCoordinates =>
    1 / ‖rawDelta x‖ ^ 4) h.source := by
  apply continuousOn_const.div (rawDelta_continuous.norm.pow 4).continuousOn
  intro x hx
  apply pow_ne_zero
  apply norm_ne_zero_iff.mpr
  simpa only [hn.source, Set.mem_setOf_eq] using hx

theorem partial_homeomorph_local_map {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (h : OpenPartialHomeomorph X Y) (μ : Measure X) :
    Measure.map h.symm ((Measure.map h (μ.restrict h.source)).restrict h.target) =
      μ.restrict h.source := by
  have hf : AEMeasurable (⇑h) (μ.restrict h.source) :=
    h.continuousOn_toFun.aemeasurable h.open_source.measurableSet
  have hm : (Measure.map h (μ.restrict h.source)).restrict h.target =
      Measure.map h (μ.restrict h.source) := by
    rw [Measure.restrict_map_of_aemeasurable hf h.open_target.measurableSet]
    congr 1
    apply (Measure.restrict_eq_self_of_ae_mem ?_)
    filter_upwards [ae_restrict_mem h.open_source.measurableSet] with x hx
    exact h.mapsTo hx
  have hi : AEMeasurable (⇑h.symm) (Measure.map h (μ.restrict h.source)) := by
    rw [← hm]
    exact h.continuousOn_invFun.aemeasurable h.open_target.measurableSet
  rw [hm, AEMeasurable.map_map_of_aemeasurable hi hf]
  calc
    Measure.map (h.symm ∘ h) (μ.restrict h.source) =
        Measure.map id (μ.restrict h.source) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem h.open_source.measurableSet] with x hx
      exact h.left_inv hx
    _ = μ.restrict h.source := Measure.map_id

theorem translated_local_measure_extension
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (U : Set G) (hU : IsOpen U) (hne : U.Nonempty) (μ : Measure G)
    (hcompat : ∀ g k : G,
      (Measure.map (g * ·) μ).restrict ({x | g⁻¹ * x ∈ U} ∩ {x | k⁻¹ * x ∈ U}) =
      (Measure.map (k * ·) μ).restrict ({x | g⁻¹ * x ∈ U} ∩ {x | k⁻¹ * x ∈ U})) :
    ∃ ν : Measure G, ν.IsMulLeftInvariant ∧
      ∀ g : G, ν.restrict {x | g⁻¹ * x ∈ U} =
        (Measure.map (g * ·) μ).restrict {x | g⁻¹ * x ∈ U} := by
  let s : G → Set G := fun g => {x | g⁻¹ * x ∈ U}
  have hs : ∀ g, IsOpen (s g) := fun g => hU.preimage (continuous_const.mul continuous_id)
  have hcover : ⋃ g, s g = univ := by
    apply univ_subset_iff.mp
    intro x _
    obtain ⟨u, hu⟩ := hne
    apply mem_iUnion.mpr
    refine ⟨x * u⁻¹, ?_⟩
    simpa [s, mul_inv_rev, mul_assoc] using hu
  obtain ⟨ν, hν⟩ := glue_open_measures s hs hcover (fun g => Measure.map (g * ·) μ) hcompat
  refine ⟨ν, ⟨fun k => ?_⟩, hν⟩
  have hpre : ∀ g, (fun x => k * x) ⁻¹' s g = s (k⁻¹ * g) := by
    intro g
    ext x
    simp [s, mul_inv_rev, mul_assoc]
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover s hs (by rw [hcover])
  apply Measure.ext_of_iUnion_eq_univ (univ_subset_iff.mp hf)
  intro i
  let g := f i
  have hk : Measurable (fun x : G => k * x) := (continuous_const.mul continuous_id).measurable
  rw [Measure.restrict_map hk (hs g).measurableSet, hpre, hν]
  rw [← hpre, ← Measure.restrict_map hk (hs g).measurableSet,
    Measure.map_map hk (show Measurable (fun x : G => (k⁻¹ * g) * x) from
      (continuous_const.mul continuous_id).measurable)]
  have hfun : (fun x : G => k * x) ∘ (fun x => (k⁻¹ * g) * x) = (fun x => g * x) := by
    funext x
    simp [Function.comp_def, mul_assoc]
  rw [hfun, hν]

theorem chart_measure_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (h : OpenPartialHomeomorph X Y) (μ : Measure X) (ν : Measure Y)
    (hd : Measure.map h.symm (ν.restrict h.target) = μ.restrict h.source)
    {s : Set X} (hs : MeasurableSet s) (hsub : s ⊆ h.source) : ν (h '' s) = μ s := by
  have hm : AEMeasurable (⇑h.symm) (ν.restrict h.target) :=
    h.continuousOn_invFun.aemeasurable h.open_target.measurableSet
  have himage : h.symm ⁻¹' s ∩ h.target = h '' s := by
    ext y
    constructor
    · rintro ⟨hy, hyt⟩
      exact ⟨h.symm y, hy, h.right_inv hyt⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simpa only [mem_preimage, h.left_inv (hsub hx)] using hx,
        h.map_source (hsub hx)⟩
  have H := congrArg (fun m : Measure X => m s) hd
  rw [Measure.map_apply_of_aemeasurable hm hs,
    Measure.restrict_apply₀ (hm.nullMeasurableSet_preimage hs),
    himage, Measure.restrict_apply hs, inter_eq_left.mpr hsub] at H
  exact H

theorem invariant_measure_isHaar_of_local_data
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant]
    (U : Set G) (hU : IsOpen U) (hne : U.Nonempty) (hfinite : ν U ≠ ⊤)
    (K : Set G) (hK : IsCompact K) (hpos : ν K ≠ 0) : ν.IsHaarMeasure := by
  letI : IsFiniteMeasureOnCompacts ν := ⟨fun L hL =>
    measure_lt_top_of_isCompact_of_isMulLeftInvariant U hU hne hfinite hL⟩
  letI : ν.IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK hpos
  exact ⟨⟩

theorem invariant_measure_isHaar_of_chart_density
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {n : ℕ}
    (ν : Measure G) [ν.IsMulLeftInvariant]
    (h : OpenPartialHomeomorph (Fin n → ℝ) G) (hne : h.source.Nonempty)
    (w : (Fin n → ℝ) → ℝ) (hw : ContinuousOn w h.source)
    (hp : ∀ x ∈ h.source, 0 < w x) (hm : Measurable w)
    (hd : Measure.map h.symm (ν.restrict h.target) =
      (volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source) :
    ν.IsHaarMeasure := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp h.open_source x hx
  let K := Metric.closedBall x (r / 2)
  let U := Metric.ball x (r / 2)
  have hK : IsCompact K := isCompact_closedBall x (r / 2)
  have hKU : K ⊆ h.source :=
    (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hsub
  have hUK : U ⊆ K := Metric.ball_subset_closedBall
  have hUs : U ⊆ h.source := hUK.trans hKU
  have hi : IntegrableOn w K volume := (hw.mono hKU).integrableOn_compact hK
  have hnonneg : 0 ≤ᵐ[volume.restrict K] w := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact (hp y (hKU hy)).le
  have hfinite : (volume.withDensity (fun y => ENNReal.ofReal (w y))) K ≠ ⊤ := by
    rw [withDensity_apply _ hK.measurableSet]
    exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hnonneg).mpr hi
  have hKpos : 0 < (volume.withDensity (fun y => ENNReal.ofReal (w y))) K := by
    rw [withDensity_apply _ hK.measurableSet, lintegral_pos_iff_support hm.ennreal_ofReal]
    apply lt_of_lt_of_le (show 0 < volume U from
      Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr (by linarith)))
    have hsupport : MeasurableSet (Function.support (fun y => ENNReal.ofReal (w y))) := by
      convert (hm.ennreal_ofReal (measurableSet_singleton 0)).compl using 1
      ext y
      simp [Function.support]
    rw [Measure.restrict_apply hsupport]
    apply measure_mono
    intro y hy
    exact ⟨(ENNReal.ofReal_pos.mpr (hp y (hUs hy))).ne', hUK hy⟩
  apply invariant_measure_isHaar_of_local_data ν (h '' U)
    (h.isOpen_image_of_subset_source Metric.isOpen_ball hUs)
    ((Metric.nonempty_ball.mpr (by linarith)).image h) (K := h '' K)
  · have H := chart_measure_image h _ ν hd Metric.isOpen_ball.measurableSet hUs
    rw [H]
    exact ne_top_of_le_ne_top hfinite (measure_mono hUK)
  · exact hK.image_of_continuousOn (h.continuousOn_toFun.mono hKU)
  · rw [chart_measure_image h _ ν hd hK.measurableSet hKU]
    exact hKpos.ne'
theorem rawMatrix_rawRatios (a : Matrix (Fin 2) (Fin 2) ℂ) (ha : a 0 0 ≠ 0) :
    rawMatrix (rawRatios a) = (a 0 0)⁻¹ • a := by
  have h0 : rawComplexCoordinates (rawRatios a) 0 = a 1 1 / a 0 0 - 1 := by
    apply Complex.ext <;> simp [rawComplexCoordinates, rawRatios]
  have h1 : rawComplexCoordinates (rawRatios a) 1 = a 0 1 / a 0 0 := by
    apply Complex.ext <;> simp [rawComplexCoordinates, rawRatios]
  have h2 : rawComplexCoordinates (rawRatios a) 2 = a 1 0 / a 0 0 := by
    apply Complex.ext <;> simp [rawComplexCoordinates, rawRatios]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawMatrix, h0, h1, h2, Matrix.smul_apply, ha, div_eq_mul_inv, mul_comm]

theorem rawDelta_rawRatios (a : Matrix (Fin 2) (Fin 2) ℂ) (ha : a 0 0 ≠ 0) :
    rawDelta (rawRatios a) = a.det / (a 0 0) ^ 2 := by
  rw [← rawMatrix_det, rawMatrix_rawRatios a ha, Matrix.det_smul]
  simp [Fintype.card_fin, div_eq_mul_inv, mul_comm]

theorem rawDelta_multiply (x y : RawCoordinates)
    (hxy : 1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0) :
    rawDelta (rawMultiply (x, y)) = rawDelta x * rawDelta y /
      (1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2) ^ 2 := by
  have h00 : (rawMatrix x * rawMatrix y) 0 0 =
      1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, rawMatrix]
  rw [rawMultiply, rawDelta_rawRatios _ (h00 ▸ hxy), Matrix.det_mul,
    rawMatrix_det, rawMatrix_det, h00]

theorem normalized_chart_haar_of_compatible_translates
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] {n : ℕ}
    (h : OpenPartialHomeomorph (Fin n → ℝ) G) (hne : h.source.Nonempty)
    (w : (Fin n → ℝ) → ℝ) (hw : ContinuousOn w h.source)
    (hp : ∀ x ∈ h.source, 0 < w x) (hm : Measurable w)
    (hcompat : ∀ g k : G,
        (Measure.map (g * ·) (Measure.map h
          ((volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source))).restrict
          ({x | g⁻¹ * x ∈ h.target} ∩ {x | k⁻¹ * x ∈ h.target}) =
        (Measure.map (k * ·) (Measure.map h
          ((volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source))).restrict
          ({x | g⁻¹ * x ∈ h.target} ∩ {x | k⁻¹ * x ∈ h.target})) :
    ∃ ν : Measure G, ν.IsHaarMeasure ∧
      Measure.map h.symm (ν.restrict h.target) =
        (volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source := by
  let μ := Measure.map h
      ((volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source)
  have ht : h.target.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨h x, h.map_source hx⟩
  obtain ⟨ν, hν, hlocal⟩ := translated_local_measure_extension
    h.target h.open_target ht μ hcompat
  letI := hν
  have hid : ν.restrict h.target = μ.restrict h.target := by
    simpa using hlocal 1
  have hd : Measure.map h.symm (ν.restrict h.target) =
      (volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source := by
    rw [hid]
    exact partial_homeomorph_local_map h _
  exact ⟨ν, invariant_measure_isHaar_of_chart_density ν h hne w hw hp hm hd, hd⟩
theorem rawMultiply_mem_source
    (h : OpenPartialHomeomorph RawCoordinates RawGroup) (hn : NormalizedChart h)
    (x y : RawCoordinates) (hx : x ∈ h.source) (hy : y ∈ h.source)
    (hxy : 1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0) :
    rawMultiply (x, y) ∈ h.source := by
  rw [hn.source] at hx hy ⊢
  change rawDelta (rawMultiply (x,y)) ≠ 0
  rw [rawDelta_multiply x y hxy]
  exact div_ne_zero (mul_ne_zero hx hy) (pow_ne_zero 2 hxy)

theorem rawMultiply_chart
    (h : OpenPartialHomeomorph RawCoordinates RawGroup) (hn : NormalizedChart h)
    (x y : RawCoordinates) (hx : x ∈ h.source) (hy : y ∈ h.source)
    (hxy : 1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0) :
    h (rawMultiply (x, y)) = h x * h y := by
  have hx' : rawDelta x ≠ 0 := by simpa [hn.source] using hx
  have hy' : rawDelta y ≠ 0 := by simpa [hn.source] using hy
  have hm := rawMultiply_mem_source h hn x y hx hy hxy
  have hm' : rawDelta (rawMultiply (x, y)) ≠ 0 := by simpa [hn.source] using hm
  set_option backward.isDefEq.respectTransparency false in
    simp only [hn.displayed _ hm', hn.displayed _ hx', hn.displayed _ hy']
  rw [← map_mul Matrix.ProjGenLinGroup.mk]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  have h00 : (rawMatrix x * rawMatrix y) 0 0 =
      1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, rawMatrix]
  have hnz : (rawMatrix x * rawMatrix y) 0 0 ≠ 0 := h00 ▸ hxy
  refine ⟨Units.mk0 ((rawMatrix x * rawMatrix y) 0 0) hnz, Units.ext ?_⟩
  change rawMatrix (rawMultiply (x,y)) *
    Matrix.scalar (Fin 2) ((rawMatrix x * rawMatrix y) 0 0) = rawMatrix x * rawMatrix y
  rw [rawMultiply, rawMatrix_rawRatios _ hnz]
  ext i j
  simp [Matrix.mul_diagonal, smul_eq_mul, hnz]
  field_simp

theorem rawMultiply_inverse_chart
    (h : OpenPartialHomeomorph RawCoordinates RawGroup) (hn : NormalizedChart h)
    (x y : RawCoordinates) (hx : x ∈ h.source) (hy : y ∈ h.source)
    (hxy : 1 + rawComplexCoordinates x 1 * rawComplexCoordinates y 2 ≠ 0) :
    h.symm (h x * h y) = rawMultiply (x, y) := by
  rw [← rawMultiply_chart h hn x y hx hy hxy]
  exact h.left_inv (rawMultiply_mem_source h hn x y hx hy hxy)

section RawSmooth
open scoped Matrix.Norms.Elementwise

theorem contDiffAt_rawRatios (a : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : a 0 0 ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) rawRatios a := by
  have hd (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : Matrix (Fin 2) (Fin 2) ℂ => x i j / x 0 0) a := by
    have he (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Matrix (Fin 2) (Fin 2) ℂ => x i j) :=
      (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)
    simpa only [div_eq_mul_inv] using!
      (he i j).contDiffAt.mul ((he 0 0).contDiffAt.inv ha)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> simp only [rawRatios, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  · exact (Complex.reCLM.contDiff.comp_contDiffAt a (hd 1 1)).sub contDiffAt_const
  · exact Complex.imCLM.contDiff.comp_contDiffAt a (hd 1 1)
  · exact Complex.reCLM.contDiff.comp_contDiffAt a (hd 0 1)
  · exact Complex.imCLM.contDiff.comp_contDiffAt a (hd 0 1)
  · exact Complex.reCLM.contDiff.comp_contDiffAt a (hd 1 0)
  · exact Complex.imCLM.contDiff.comp_contDiffAt a (hd 1 0)

theorem contDiff_rawComplexCoordinates : ContDiff ℝ (⊤ : ℕ∞) rawComplexCoordinates := by
  apply contDiff_pi.mpr
  intro i
  have hc (j k : Fin 6) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : RawCoordinates => (x j : ℂ) + (x k : ℂ) * Complex.I) :=
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ j)).add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)).mul contDiff_const))
  fin_cases i <;> simp [rawComplexCoordinates, Complex.mk_eq_add_mul_I] <;> exact hc _ _

theorem contDiff_rawMatrix : ContDiff ℝ (⊤ : ℕ∞) rawMatrix := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [rawMatrix]
  · exact contDiff_const
  · exact (contDiff_pi.mp contDiff_rawComplexCoordinates) 1
  · exact (contDiff_pi.mp contDiff_rawComplexCoordinates) 2
  · exact contDiff_const.add ((contDiff_pi.mp contDiff_rawComplexCoordinates) 0)

theorem contDiffAt_rawMultiply (p : RawCoordinates × RawCoordinates)
    (hp : 1 + rawComplexCoordinates p.1 1 * rawComplexCoordinates p.2 2 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) rawMultiply p := by
  have hm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : RawCoordinates × RawCoordinates => rawMatrix p.1 * rawMatrix p.2) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    have he (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : RawCoordinates => rawMatrix x i j) :=
      (contDiff_pi.mp ((contDiff_pi.mp contDiff_rawMatrix) i)) j
    exact ((he i 0).comp contDiff_fst |>.mul ((he 0 j).comp contDiff_snd)).add
      ((he i 1).comp contDiff_fst |>.mul ((he 1 j).comp contDiff_snd))
  apply (contDiffAt_rawRatios _ ?_).comp p hm.contDiffAt
  simpa [Matrix.mul_apply, Fin.sum_univ_two, rawMatrix] using hp
end RawSmooth

theorem normalized_frame_haar
    [MeasurableSpace RawGroup] [BorelSpace RawGroup]
    (h : OpenPartialHomeomorph RawCoordinates RawGroup) (hn : NormalizedChart h)
    [C : ChartedSpace RawCoordinates RawGroup]
    [LieGroup (𝓘(ℝ, RawCoordinates)) (↑(⊤ : ℕ∞) : ℕ∞ω) RawGroup]
    (hchart : ∀ g, C.chartAt g =
      (h.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm)
    (F : RawCoordinates → RawCoordinates →L[ℝ] RawCoordinates)
    (hderiv : ∀ x, HasFDerivAt (fun y => rawMultiply (x, y)) (F x) 0)
    (hdet : ∀ x, (F x).toLinearMap.det = ‖rawDelta x‖ ^ 4) :
    ∃ ν : Measure RawGroup, ν.IsHaarMeasure ∧
      Measure.map h.symm (ν.restrict h.target) =
        (volume.withDensity (fun x : RawCoordinates =>
          ENNReal.ofReal (1 / ‖rawDelta x‖ ^ 4))).restrict h.source := by
  letI : SecondCountableTopology RawGroup := rawGroup_secondCountableTopology
  have hne : h.source.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hn.source]
    have hz : rawDelta 0 = 1 := by
      apply Complex.ext <;> simp [rawDelta, rawComplexCoordinates]
    simpa only [Set.mem_setOf_eq, hz] using (one_ne_zero : (1 : ℂ) ≠ 0)
  have hm : Measurable (fun x : RawCoordinates => 1 / ‖rawDelta x‖ ^ 4) :=
    measurable_const.div (rawDelta_continuous.measurable.norm.pow_const 4)
  apply normalized_chart_haar_of_compatible_translates h hne
    (fun x => 1 / ‖rawDelta x‖ ^ 4) (rawDensity_continuousOn h hn)
    (rawDensity_positive h hn) hm
  apply translated_chart_measures_compatible_of_jacobian h
    (fun x => 1 / ‖rawDelta x‖ ^ 4) (rawDensity_continuousOn h hn)
    (rawDensity_positive h hn) hm
  set_option backward.isDefEq.respectTransparency false in
    exact normalized_chart_translation_jacobian h hn (C := C) hchart F hderiv hdet

end DedekindZetaZeroFree.PGLComplex.AffineLie

end

end
