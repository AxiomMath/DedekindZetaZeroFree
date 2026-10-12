module

public import Mathlib

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace DedekindZetaZeroFree
namespace KPChartL2

noncomputable def weightedMeasure (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict Ω).withDensity (fun x => ENNReal.ofReal (w x))

def equivariantL2 (n r : ℕ) (Γ : Type*)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (act : Γ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (R : Γ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r))) :
    Set (Lp (EuclideanSpace ℂ (Fin r)) 2 μ) :=
  {f | ∀ γ : Γ, ∀ᵐ x ∂μ, f (act γ x) = R γ x (f x)}

noncomputable def average (n r : ℕ) (Γ : Type*) [Group Γ] [Fintype Γ]
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (act : Γ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (R : Γ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r)))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r) :=
  Ω.indicator (fun x => (Fintype.card Γ : ℂ)⁻¹ •
    ∑ γ : Γ, (R γ x).symm (h (act γ x)))

structure Data (n r : ℕ) (Γ : Type*) [Group Γ] where
  chart : Set (EuclideanSpace ℝ (Fin n))
  open_chart : IsOpen chart
  weight : EuclideanSpace ℝ (Fin n) → ℝ
  smooth_weight : ContDiffOn ℝ ∞ weight chart
  positive_weight : ∀ x ∈ chart, 0 < weight x
  locally_integrable_weight : LocallyIntegrableOn weight chart volume
  act : Γ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  act_mem : ∀ γ x, x ∈ chart → act γ x ∈ chart
  act_one : ∀ x ∈ chart, act 1 x = x
  act_mul : ∀ γ δ x, x ∈ chart → act (γ * δ) x = act γ (act δ x)
  smooth_action : ∀ γ, ContDiffOn ℝ ∞ (act γ) chart
  invariant_measure : ∀ γ, MeasurePreserving (act γ)
    (weightedMeasure n chart weight) (weightedMeasure n chart weight)
  cocycle : Γ → EuclideanSpace ℝ (Fin n) →
    (EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r))
  cocycle_one : ∀ x ∈ chart, cocycle 1 x = LinearIsometryEquiv.refl ℂ _
  cocycle_mul : ∀ γ δ x, x ∈ chart → ∀ v,
    cocycle (γ * δ) x v = cocycle γ (act δ x) (cocycle δ x v)
  smooth_cocycle : ∀ γ, ContDiffOn ℝ ∞
    (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℂ (Fin r) =>
      cocycle γ p.1 p.2) (chart ×ˢ Set.univ)

private theorem inverse_action (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ) (γ : Γ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D.chart) : D.act γ⁻¹ (D.act γ x) = x := by
  rw [← D.act_mul γ⁻¹ γ x hx, inv_mul_cancel, D.act_one x hx]

private theorem inverse_cocycle (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ) (γ : Γ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D.chart) (v : EuclideanSpace ℂ (Fin r)) :
    (D.cocycle γ x).symm v = D.cocycle γ⁻¹ (D.act γ x) v := by
  have hc := D.cocycle_mul γ⁻¹ γ x hx ((D.cocycle γ x).symm v)
  simpa [D.cocycle_one x hx] using hc

private theorem shifted_inverse_cocycle (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ) (γ δ : Γ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D.chart) (v : EuclideanSpace ℂ (Fin r)) :
    (D.cocycle γ (D.act δ x)).symm v =
      D.cocycle δ x ((D.cocycle (γ * δ) x).symm v) := by
  apply (D.cocycle γ (D.act δ x)).injective
  rw [LinearIsometryEquiv.apply_symm_apply,
    ← D.cocycle_mul γ δ x hx, LinearIsometryEquiv.apply_symm_apply]

private theorem average_equivariant (n r : ℕ) (Γ : Type*) [Group Γ] [Fintype Γ]
    (D : Data n r Γ) (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (δ : Γ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D.chart) :
    average n r Γ D.chart D.act D.cocycle h (D.act δ x) =
      D.cocycle δ x (average n r Γ D.chart D.act D.cocycle h x) := by
  classical
  simp only [average, Set.indicator_of_mem hx,
    Set.indicator_of_mem (D.act_mem δ x hx), LinearIsometryEquiv.map_smul]
  congr 1
  rw [map_sum]
  apply Fintype.sum_equiv (Equiv.mulRight δ)
  intro γ
  rw [shifted_inverse_cocycle n r Γ D γ δ x hx, ← D.act_mul γ δ x hx]
  rfl

 theorem ae_chart (n r : ℕ) (Γ : Type*) [Group Γ] (D : Data n r Γ) :
    ∀ᵐ x ∂weightedMeasure n D.chart D.weight, x ∈ D.chart :=
  (ae_restrict_mem D.open_chart.measurableSet).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

 noncomputable def term (n r : ℕ) (Γ : Type*) [Group Γ] (D : Data n r Γ) (γ : Γ)
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r)) :=
  D.chart.indicator (fun x => (D.cocycle γ x).symm (h (D.act γ x)))

 theorem term_memLp (n r : ℕ) (Γ : Type*) [Group Γ] (D : Data n r Γ)
    (γ : Γ) (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (hh : MemLp h 2 (weightedMeasure n D.chart D.weight)) :
    MemLp (term n r Γ D γ h) 2 (weightedMeasure n D.chart D.weight) := by
  classical
  let B := (D.chart ×ˢ Set.univ).indicator
    (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℂ (Fin r) =>
      D.cocycle γ⁻¹ (D.act γ p.1) p.2)
  have hB : Measurable B := by
    dsimp only [B]
    rw [← Set.piecewise_eq_indicator]
    apply ContinuousOn.measurable_piecewise ?_ continuousOn_const
      (D.open_chart.measurableSet.prod MeasurableSet.univ)
    exact ((D.smooth_cocycle γ⁻¹).comp
      (((D.smooth_action γ).comp contDiffOn_fst (fun p hp => hp.1)).prodMk
        contDiffOn_snd) (fun p hp => ⟨D.act_mem γ p.1 hp.1, Set.mem_univ _⟩)).continuousOn
  have hcomp := hh.comp_measurePreserving (D.invariant_measure γ)
  have ht : AEStronglyMeasurable (term n r Γ D γ h)
      (weightedMeasure n D.chart D.weight) := by
    have hm := (hB.comp_aemeasurable
      (aestronglyMeasurable_id.prodMk hcomp.aestronglyMeasurable).aemeasurable).aestronglyMeasurable
    apply hm.congr
    filter_upwards [ae_chart n r Γ D] with x hx
    simp only [term, B, Function.comp_apply, id_eq, Set.indicator_of_mem hx,
      Set.indicator_of_mem (show (x, h (D.act γ x)) ∈ D.chart ×ˢ Set.univ from ⟨hx, Set.mem_univ _⟩)]
    exact (inverse_cocycle n r Γ D γ x hx _).symm
  apply hcomp.of_le ht
  filter_upwards [ae_chart n r Γ D] with x hx
  simp [term, Set.indicator_of_mem hx]

 noncomputable def termLp (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ) (γ : Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight)) :=
  (term_memLp n r Γ D γ f (Lp.memLp f)).toLp (term n r Γ D γ f)

 theorem termLp_norm (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ) (γ : Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight)) :
    ‖termLp n r Γ D γ f‖ = ‖f‖ := by
  rw [termLp, Lp.norm_toLp, Lp.norm_def]
  congr 1
  calc
    eLpNorm (term n r Γ D γ f) 2 (weightedMeasure n D.chart D.weight) =
        eLpNorm (f ∘ D.act γ) 2 (weightedMeasure n D.chart D.weight) := by
      apply eLpNorm_congr_norm_ae (term_memLp n r Γ D γ f (Lp.memLp f)).aestronglyMeasurable
        ((Lp.memLp f).comp_measurePreserving (D.invariant_measure γ)).aestronglyMeasurable
      filter_upwards [ae_chart n r Γ D] with x hx
      simp [term, Set.indicator_of_mem hx]
    _ = _ := eLpNorm_comp_measurePreserving (Lp.memLp f).aestronglyMeasurable
      (D.invariant_measure γ)

 theorem termLp_coe (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ) (γ : Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight)) :
    termLp n r Γ D γ f =ᵐ[weightedMeasure n D.chart D.weight]
      term n r Γ D γ f := MemLp.coeFn_toLp _

 noncomputable def termCLM (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ) (γ : Γ) :
    Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight) :=
  LinearMap.mkContinuous
    { toFun := termLp n r Γ D γ
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [termLp_coe n r Γ D γ (f + g),
          Lp.coeFn_add (termLp n r Γ D γ f) (termLp n r Γ D γ g),
          termLp_coe n r Γ D γ f, termLp_coe n r Γ D γ g,
          (D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_add f g),
          ae_chart n r Γ D] with x ha hb hc hd he hx
        rw [ha, hb, Pi.add_apply, hc, hd]
        simp only [term, Set.indicator_of_mem hx]
        simp only [Function.comp_apply, Pi.add_apply] at he
        rw [he, map_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [termLp_coe n r Γ D γ (c • f),
          Lp.coeFn_smul c (termLp n r Γ D γ f), termLp_coe n r Γ D γ f,
          (D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c f),
          ae_chart n r Γ D] with x ha hb hc hd hx
        simp only [RingHom.id_apply]
        rw [ha, hb, Pi.smul_apply, hc]
        simp only [term, Set.indicator_of_mem hx]
        simp only [Function.comp_apply, Pi.smul_apply] at hd
        rw [hd, LinearIsometryEquiv.map_smul] }
    1 (fun f => by simp [termLp_norm])

 noncomputable def averageCLM (n r : ℕ) (Γ : Type*) [Group Γ] [Fintype Γ]
    (D : Data n r Γ) :
    Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight) :=
  (Fintype.card Γ : ℂ)⁻¹ • ∑ γ : Γ, termCLM n r Γ D γ

private theorem averageCLM_coe (n r : ℕ) (Γ : Type*) [Group Γ] [Fintype Γ]
    (D : Data n r Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight)) :
    averageCLM n r Γ D f =ᵐ[weightedMeasure n D.chart D.weight]
      average n r Γ D.chart D.act D.cocycle f := by
  classical
  simp only [averageCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  have ht : ∀ᵐ x ∂weightedMeasure n D.chart D.weight,
      ∀ γ : Γ, termCLM n r Γ D γ f x = term n r Γ D γ f x := by
    rw [Filter.eventually_all]
    exact fun γ => termLp_coe n r Γ D γ f
  filter_upwards [Lp.coeFn_smul (Fintype.card Γ : ℂ)⁻¹
    (∑ γ : Γ, termCLM n r Γ D γ f), Lp.coeFn_finsetSum Finset.univ
    (fun γ => termCLM n r Γ D γ f), ht, ae_chart n r Γ D] with x ha hb hc hx
  simp only [ha, Pi.smul_apply, hb, Finset.sum_apply, hc, term, average,
    Set.indicator_of_mem hx]

private theorem averageCLM_norm (n r : ℕ) (Γ : Type*) [Group Γ] [Fintype Γ]
    (D : Data n r Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight)) :
    ‖averageCLM n r Γ D f‖ ≤ ‖f‖ := by
  classical
  simp only [averageCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    norm_smul, norm_inv, Complex.norm_natCast]
  calc
    (↑(Fintype.card Γ) : ℝ)⁻¹ * ‖∑ γ : Γ, termCLM n r Γ D γ f‖ ≤
        (↑(Fintype.card Γ) : ℝ)⁻¹ * ∑ γ : Γ, ‖termCLM n r Γ D γ f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ‖f‖ := by
      change (↑(Fintype.card Γ) : ℝ)⁻¹ * ∑ γ : Γ, ‖termLp n r Γ D γ f‖ = ‖f‖
      simp only [termLp_norm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

private theorem averageCLM_mem (n r : ℕ) (Γ : Type*) [Group Γ] [Fintype Γ]
    (D : Data n r Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight)) :
    averageCLM n r Γ D f ∈ equivariantL2 n r Γ
      (weightedMeasure n D.chart D.weight) D.act D.cocycle := by
  intro γ
  filter_upwards [averageCLM_coe n r Γ D f,
    (D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp (averageCLM_coe n r Γ D f),
    ae_chart n r Γ D] with x ha hb hx
  simp only [Function.comp_apply] at hb
  rw [ha, hb]
  exact average_equivariant n r Γ D f γ x hx

private theorem averageCLM_fixed (n r : ℕ) (Γ : Type*) [Group Γ] [Fintype Γ]
    (D : Data n r Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight))
    (hf : f ∈ equivariantL2 n r Γ (weightedMeasure n D.chart D.weight) D.act D.cocycle) :
    averageCLM n r Γ D f = f := by
  classical
  have he : ∀ᵐ x ∂weightedMeasure n D.chart D.weight,
      ∀ γ : Γ, f (D.act γ x) = D.cocycle γ x (f x) := by
    rw [Filter.eventually_all]
    exact hf
  apply Lp.ext
  filter_upwards [averageCLM_coe n r Γ D f, he, ae_chart n r Γ D] with x ha hb hx
  rw [ha]
  simp only [average, Set.indicator_of_mem hx, hb,
    LinearIsometryEquiv.symm_apply_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp [Fintype.card_ne_zero]

private theorem interior_finite (n r : ℕ) (Γ : Type*) [Group Γ] (D : Data n r Γ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKD : K ⊆ D.chart) :
    weightedMeasure n D.chart D.weight K < ⊤ := by
  rw [weightedMeasure, withDensity_apply _ hK.measurableSet,
    Measure.restrict_restrict hK.measurableSet, Set.inter_eq_left.mpr hKD]
  have hi := (D.locally_integrable_weight.mono_set hKD).integrableOn_isCompact hK
  apply lt_of_le_of_lt _ hi.hasFiniteIntegral
  apply lintegral_mono
  intro x
  dsimp only
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

private theorem continuous_interior_approx (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r),
      Continuous h ∧ HasCompactSupport h ∧ tsupport h ⊆ D.chart ∧
      MemLp h 2 (weightedMeasure n D.chart D.weight) ∧
      eLpNorm (fun x => f x - h x) 2 (weightedMeasure n D.chart D.weight) ≤ ENNReal.ofReal ε := by
  let μ := weightedMeasure n D.chart D.weight
  let ν := μ.comap (Subtype.val : D.chart → EuclideanSpace ℝ (Fin n))
  letI : LocallyCompactSpace D.chart := D.open_chart.locallyCompactSpace
  have hme := MeasurableEmbedding.subtype_coe D.open_chart.measurableSet
  letI : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hme.comap_apply]
    exact interior_finite n r Γ D (hK.image continuous_subtype_val)
      (Subtype.coe_image_subset _ _)⟩
  haveI : ν.Regular := inferInstance
  have hmap : Measure.map (Subtype.val : D.chart → EuclideanSpace ℝ (Fin n)) ν = μ := by
    rw [hme.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem D.open_chart.measurableSet).filter_mono
        (withDensity_absolutelyContinuous _ _).ae_le)
  have hfsub : MemLp (fun x : D.chart => f x.1) 2 ν := by
    have hh := (Lp.memLp f : MemLp (f : EuclideanSpace ℝ (Fin n) → _) 2 μ)
    change MemLp (f : EuclideanSpace ℝ (Fin n) → _) 2 μ at hh
    rw [← hmap] at hh
    exact (hme.memLp_map_measure_iff).mp hh
  obtain ⟨c, hccomp, hcerror, hccont, hcmem⟩ :=
    hfsub.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
      (show (ENNReal.ofReal ε) ≠ 0 by positivity)
  let h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r) :=
    Function.extend Subtype.val c 0
  have hext (x : D.chart) : h x.1 = c x := Subtype.val_injective.extend_apply c 0 x
  have hcont : Continuous h := hccomp.continuous_extend_zero D.open_chart hccont
  have hsupp : HasCompactSupport h := hccomp.extend_zero continuous_subtype_val
  have hts : tsupport h ⊆ D.chart :=
    (hccomp.tsupport_extend_zero_subset continuous_subtype_val).trans
      (Subtype.coe_image_subset _ _)
  have hmem : MemLp h 2 μ := by
    rw [← hmap]
    apply hme.memLp_map_measure_iff.mpr
    exact hcmem.ae_eq (Filter.Eventually.of_forall fun x => (hext x).symm)
  refine ⟨h, hcont, hsupp, hts, hmem, ?_⟩
  change eLpNorm (fun x => f x - h x) 2 μ ≤ ENNReal.ofReal ε
  have hm : AEStronglyMeasurable (fun x => f x - h x) μ :=
    ((Lp.memLp f).sub hmem).aestronglyMeasurable
  rw [← hmap] at hm ⊢
  rw [eLpNorm_map_measure hm hme.measurable.aemeasurable]
  convert hcerror using 1
  congr 1
  funext x
  exact congrArg (fun v => f x.1 - v) (hext x)

private theorem smooth_interior_approx (n r : ℕ) (Γ : Type*) [Group Γ]
    (D : Data n r Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (weightedMeasure n D.chart D.weight))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (hg : MemLp g 2 (weightedMeasure n D.chart D.weight)),
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ D.chart ∧
      ‖f - hg.toLp g‖ < ε := by
  obtain ⟨h, hcont, hcomp, hts, hmem, herr⟩ :=
    continuous_interior_approx n r Γ D f (ε / 2) (by positivity)
  let μ := weightedMeasure n D.chart D.weight
  have hfin : μ (tsupport h) < ⊤ := interior_finite n r Γ D hcomp hts
  obtain ⟨N, hN, hb⟩ := ENNReal.exists_nat_pos_inv_mul_lt
    (ENNReal.rpow_ne_top_of_nonneg (show 0 ≤ (1 : ℝ) / (2 : ENNReal).toReal by positivity) hfin.ne)
    (show ENNReal.ofReal (ε / 2) ≠ 0 by positivity)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨g, hgd, hgapprox, hgsupp⟩ := hcont.exists_contDiff_approx ⊤
    (ε := fun _ => (N : ℝ)⁻¹) continuous_const (fun _ => by positivity)
  have hgcomp := hcomp.mono hgsupp
  have hgts : tsupport g ⊆ D.chart := (closure_mono hgsupp).trans hts
  have hgm : MemLp g 2 μ := by
    letI : IsFiniteMeasure (μ.restrict (tsupport h)) := isFiniteMeasure_restrict.mpr hfin.ne
    have hr : MemLp g 2 (μ.restrict (tsupport h)) := by
      have hfincomp : IsFiniteMeasureOnCompacts (μ.restrict (tsupport h)) := inferInstance
      exact hgd.continuous.memLp_of_hasCompactSupport hgcomp
    have heq : (tsupport h).indicator g = g := Set.indicator_eq_self.mpr
      (hgsupp.trans (subset_tsupport h))
    rw [← heq]
    exact memLp_indicator_iff_restrict isClosed_closure.measurableSet.nullMeasurableSet |>.mpr hr
  have herrg : eLpNorm (h - g) 2 μ < ENNReal.ofReal (ε / 2) := by
    apply lt_of_le_of_lt (eLpNorm_sub_le_of_dist_bdd μ (by norm_num)
      isClosed_closure.measurableSet.nullMeasurableSet
      (show 0 ≤ (N : ℝ)⁻¹ by positivity)
      (hmem.sub hgm).aestronglyMeasurable (fun x => by
        simpa only [dist_comm] using (hgapprox x).le)
      (subset_tsupport h) (hgsupp.trans (subset_tsupport h)))
    convert hb using 1
    rw [ENNReal.ofReal_inv_of_pos hNr, ENNReal.ofReal_natCast]
    rfl
  have herrall : eLpNorm (fun x => f x - g x) 2 μ < ENNReal.ofReal ε := by
    have heq : (fun x => f x - g x) = (fun x => f x - h x) + (h - g) := by
      funext x
      simp
    rw [heq]
    calc
      eLpNorm ((fun x => f x - h x) + (h - g)) 2 μ ≤
          eLpNorm (fun x => f x - h x) 2 μ + eLpNorm (h - g) 2 μ :=
        eLpNorm_add_le (by norm_num)
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_of_le_of_lt ((Lp.memLp f).sub hmem).eLpNorm_ne_top herr herrg
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  refine ⟨g, hgm, hgd, hgcomp, hgts, ?_⟩
  rw [← dist_eq_norm, Lp.dist_def]
  change (eLpNorm ((f : EuclideanSpace ℝ (Fin n) → _) -
    (hgm.toLp g : EuclideanSpace ℝ (Fin n) → _)) 2 μ).toReal < ε
  have heq : eLpNorm ((f : EuclideanSpace ℝ (Fin n) → _) -
      (hgm.toLp g : EuclideanSpace ℝ (Fin n) → _)) 2 μ =
      eLpNorm (fun x => f x - g x) 2 μ := by
    apply eLpNorm_congr_ae
    filter_upwards [hgm.coeFn_toLp] with x hx
    simp [hx]
  rw [heq]
  exact (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mpr herrall |>
    (fun h => by simpa [ENNReal.toReal_ofReal hε.le] using h)

private theorem average_congr_ae (n r : ℕ) (Γ : Type*) [Group Γ] [Fintype Γ]
    (D : Data n r Γ) (a b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (hab : a =ᵐ[weightedMeasure n D.chart D.weight] b) :
    average n r Γ D.chart D.act D.cocycle a =ᵐ[weightedMeasure n D.chart D.weight]
      average n r Γ D.chart D.act D.cocycle b := by
  classical
  have ht : ∀ᵐ x ∂weightedMeasure n D.chart D.weight,
      ∀ γ : Γ, a (D.act γ x) = b (D.act γ x) := by
    rw [Filter.eventually_all]
    exact fun γ => (D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp hab
  filter_upwards [ht] with x hx
  simp only [average]
  by_cases hxc : x ∈ D.chart
  · simp only [Set.indicator_of_mem hxc, hx]
  · simp [Set.indicator_of_notMem hxc]

end KPChartL2

theorem kp_cont_chart_equivariant_l2_projection
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (Γ : Type*) [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ) :
    IsClosed (KPChartL2.equivariantL2 n r Γ
      (KPChartL2.weightedMeasure n D.chart D.weight) D.act D.cocycle) ∧
    ∃ P : Lp (EuclideanSpace ℂ (Fin r)) 2
        (KPChartL2.weightedMeasure n D.chart D.weight) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin r)) 2
        (KPChartL2.weightedMeasure n D.chart D.weight),
      (∀ f, ‖P f‖ ≤ ‖f‖) ∧ (∀ f, P (P f) = P f) ∧
      Set.range P = KPChartL2.equivariantL2 n r Γ
        (KPChartL2.weightedMeasure n D.chart D.weight) D.act D.cocycle ∧
      (∀ f, ∀ᵐ x ∂(KPChartL2.weightedMeasure n D.chart D.weight),
        (P f) x = KPChartL2.average n r Γ D.chart D.act D.cocycle f x) := by
  let P := KPChartL2.averageCLM n r Γ D
  have hmem := KPChartL2.averageCLM_mem n r Γ D
  have hfix := KPChartL2.averageCLM_fixed n r Γ D
  have hset : KPChartL2.equivariantL2 n r Γ
      (KPChartL2.weightedMeasure n D.chart D.weight) D.act D.cocycle =
      {f | P f = f} := by
    ext f
    exact ⟨hfix f, fun hf => hf ▸ hmem f⟩
  refine ⟨?_, P, KPChartL2.averageCLM_norm n r Γ D,
    fun f => hfix (P f) (hmem f), ?_, KPChartL2.averageCLM_coe n r Γ D⟩
  · rw [hset]
    exact isClosed_eq P.continuous continuous_id
  · ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact hmem g
    · intro hf
      exact ⟨f, hfix f hf⟩

theorem kp_cont_chart_equivariant_average_smooth
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (Γ : Type*) [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ)
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (hsmooth : ContDiffOn ℝ ∞ h D.chart)
    (hcompact : HasCompactSupport h) (hsupport : tsupport h ⊆ D.chart) :
    let g := KPChartL2.average n r Γ D.chart D.act D.cocycle h
    ContDiffOn ℝ ∞ g D.chart ∧ HasCompactSupport g ∧ tsupport g ⊆ D.chart ∧
      (∀ γ x, x ∈ D.chart → g (D.act γ x) = D.cocycle γ x (g x)) := by
  classical
  dsimp only
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    ⋃ γ : Γ, D.act γ⁻¹ '' tsupport h
  have hKcompact : IsCompact K := isCompact_iUnion fun γ =>
    hcompact.image_of_continuousOn ((D.smooth_action γ⁻¹).continuousOn.mono hsupport)
  have hKchart : K ⊆ D.chart := by
    intro x hx
    obtain ⟨γ, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    exact D.act_mem γ⁻¹ y (hsupport hy)
  have hzero : ∀ x ∉ K,
      KPChartL2.average n r Γ D.chart D.act D.cocycle h x = 0 := by
    intro x hx
    by_cases hxc : x ∈ D.chart
    · simp only [KPChartL2.average, Set.indicator_of_mem hxc]
      have hz : ∀ γ : Γ, h (D.act γ x) = 0 := by
        intro γ
        by_contra hnz
        apply hx
        apply Set.mem_iUnion.mpr
        exact ⟨γ, D.act γ x, subset_closure hnz,
          KPChartL2.inverse_action n r Γ D γ x hxc⟩
      simp [hz]
    · simp [KPChartL2.average, Set.indicator_of_notMem hxc]
  have hts : tsupport (KPChartL2.average n r Γ D.chart D.act D.cocycle h) ⊆ K := by
    apply closure_minimal _ hKcompact.isClosed
    intro x hx
    by_contra hxK
    exact hx (hzero x hxK)
  refine ⟨?_, hKcompact.of_isClosed_subset isClosed_closure hts,
    hts.trans hKchart, KPChartL2.average_equivariant n r Γ D h⟩
  have hterm : ∀ γ : Γ, ContDiffOn ℝ ∞
      (fun x => (D.cocycle γ x).symm (h (D.act γ x))) D.chart := by
    intro γ
    have hp := (D.smooth_action γ).prodMk
      (hsmooth.comp (D.smooth_action γ) (D.act_mem γ))
    have hc := (D.smooth_cocycle γ⁻¹).comp hp (fun x hx =>
      ⟨D.act_mem γ x hx, Set.mem_univ _⟩)
    exact hc.congr (fun x hx => KPChartL2.inverse_cocycle n r Γ D γ x hx _)
  have hs := (ContDiffOn.sum (fun γ (_ : γ ∈ Finset.univ) => hterm γ)).const_smul
    (Fintype.card Γ : ℂ)⁻¹
  exact hs.congr (fun x hx => Set.indicator_of_mem hx _)

theorem kp_cont_chart_equivariant_l2_density
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (Γ : Type*) [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (KPChartL2.weightedMeasure n D.chart D.weight))
    (hf : f ∈ KPChartL2.equivariantL2 n r Γ
      (KPChartL2.weightedMeasure n D.chart D.weight) D.act D.cocycle)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (hg : MemLp g 2 (KPChartL2.weightedMeasure n D.chart D.weight)),
      ContDiffOn ℝ ∞ g D.chart ∧ HasCompactSupport g ∧ tsupport g ⊆ D.chart ∧
      (∀ γ x, x ∈ D.chart → g (D.act γ x) = D.cocycle γ x (g x)) ∧
      ‖f - hg.toLp g‖ < ε := by
  obtain ⟨h, hmem, hsmooth, hcompact, hsupport, herr⟩ :=
    KPChartL2.smooth_interior_approx n r Γ D f ε hε
  let g := KPChartL2.average n r Γ D.chart D.act D.cocycle h
  have havg := kp_cont_chart_equivariant_average_smooth n r hn hr Γ D
    h hsmooth.contDiffOn hcompact hsupport
  have hrep : KPChartL2.averageCLM n r Γ D (hmem.toLp h) =ᵐ[
      KPChartL2.weightedMeasure n D.chart D.weight] g :=
    (KPChartL2.averageCLM_coe n r Γ D (hmem.toLp h)).trans
      (KPChartL2.average_congr_ae n r Γ D _ h hmem.coeFn_toLp)
  have hg : MemLp g 2 (KPChartL2.weightedMeasure n D.chart D.weight) :=
    (Lp.memLp (KPChartL2.averageCLM n r Γ D (hmem.toLp h))).ae_eq hrep
  have heq : hg.toLp g = KPChartL2.averageCLM n r Γ D (hmem.toLp h) := by
    apply Lp.ext
    exact hg.coeFn_toLp.trans hrep.symm
  refine ⟨g, hg, havg.1, havg.2.1, havg.2.2.1, havg.2.2.2, ?_⟩
  rw [heq, ← KPChartL2.averageCLM_fixed n r Γ D f hf,
    ← map_sub]
  exact lt_of_le_of_lt (KPChartL2.averageCLM_norm n r Γ D _) herr

end DedekindZetaZeroFree
