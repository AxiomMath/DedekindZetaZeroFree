module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.ModulatedGramSymmetry
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.RadialEnvelopeNormSheetBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LogarithmicDerivativeContinuity

@[expose] public section

section
set_option maxHeartbeats 1500000

namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds.SheetContinuityAtoms.Regularity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]
local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _
local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

private theorem compact_phase_integral_contDiff
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (W d : X → ℂ) (c : X → ℝ) (hW : Continuous W) (hd : Continuous d)
    (hc : Continuous c) (hK : HasCompactSupport W) :
    ContDiff ℝ 1 (fun r : ℝ => ∫ x, W x * d x *
      Complex.exp ((c x * r : ℝ) * Complex.I) ∂μ) := by
  let f : ℝ → X → ℂ := fun r x => W x * d x *
    Complex.exp ((c x * r : ℝ) * Complex.I)
  let f' : ℝ → X → ℂ := fun r x => f r x * ((c x : ℂ) * Complex.I)
  have hf : Continuous (Function.uncurry f) := by
    dsimp [f]; fun_prop
  have hf' : Continuous (Function.uncurry f') := by
    dsimp [f', f]; fun_prop
  have hfs (r : ℝ) (x : X) (hx : x ∉ tsupport W) : f r x = 0 := by
    simp [f, image_eq_zero_of_notMem_tsupport hx]
  have hfs' (r : ℝ) (x : X) (hx : x ∉ tsupport W) : f' r x = 0 := by
    simp [f', hfs r x hx]
  have hi (r : ℝ) : Integrable (f r) μ := by
    apply (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    exact hK.mul_right.mul_right
  have hder (r : ℝ) (x : X) : HasDerivAt (fun r => f r x) (f' r x) r := by
    convert (((hasDerivAt_id r).const_mul (c x)).ofReal_comp.mul_const
      Complex.I).cexp.const_mul (W x * d x) using 1 <;> simp [f', f, mul_assoc]
  have hbound : Integrable (fun x => ‖W x‖ * ‖d x‖ * |c x|) μ := by
    apply (hW.norm.mul hd.norm |>.mul hc.abs).integrable_of_hasCompactSupport
    exact hK.norm.mul_right.mul_right
  have hdiff (r : ℝ) : HasDerivAt (fun r => ∫ x, f r x ∂μ) (∫ x, f' r x ∂μ) r := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Set.univ) (bound := fun x => ‖W x‖ * ‖d x‖ * |c x|)
      (Filter.univ_mem)
      (Filter.Eventually.of_forall fun r => (hi r).aestronglyMeasurable)
      (hi r) ((hf'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall ?_) hbound
      (Filter.Eventually.of_forall fun x r _ => hder r x)).2
    intro x r _
    simp only [f', f, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I]
    exact le_rfl
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun r => (hdiff r).differentiableAt, ?_⟩
  have heq : deriv (fun r => ∫ x, f r x ∂μ) = fun r => ∫ x, f' r x ∂μ :=
    funext fun r => (hdiff r).deriv
  rw [heq]
  exact continuousOn_univ.mp (continuousOn_integral_of_compact_support hK
    hf'.continuousOn (fun r x _ hx => hfs' r x hx))

theorem fourier_log_radial_contDiff
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (W0 : SLocalProduct F A.Sf → ℂ) (hW0 : Continuous W0)
    (hcompact : HasCompactSupport W0) (T₀ : ℝ) (hT₀ : 0 < T₀) (t : A.G1) :
    ContDiff ℝ 1 (fun u : ℝ =>
      ProbeWeight.fourier F A.Sf e μ W0
        (sheetPointRaw A (T₀ * Real.exp u) t).val) := by
  letI := hμ
  let p : ℝ := 1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))
  let r : ℝ → ℝ := fun u => Real.exp ((Real.log T₀ + u) * p)
  let c : SLocalProduct F A.Sf → ℝ := fun x => 2 * Real.pi *
    ∑ w : InfinitePlace F, 2 *
      (InfinitePlace.Completion.extensionEmbedding w (-x.1 w * (t.val.1 w).val)).re
  let d : SLocalProduct F A.Sf → ℂ := fun x =>
    ∏ v : ↥A.Sf, (e v (-x.2 v * (t.val.2 v).val) : ℂ)
  have hc : Continuous c := by
    dsimp [c]
    apply continuous_const.mul
    apply continuous_finset_sum
    intro w _
    apply continuous_const.mul
    apply Complex.continuous_re.comp
    apply (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    fun_prop
  have hd : Continuous d := by
    dsimp [d]
    apply continuous_finset_prod
    intro v _
    exact continuous_subtype_val.comp ((he v).comp (by fun_prop))
  have hr : ContDiff ℝ 1 r := by
    dsimp [r]
    apply Real.contDiff_exp.comp
    exact (contDiff_const.add contDiff_id).mul contDiff_const
  have hscale (u : ℝ) : (T₀ * Real.exp u) ^ p = r u := by
    rw [Real.rpow_def_of_pos (mul_pos hT₀ (Real.exp_pos u)),
      Real.log_mul hT₀.ne' (Real.exp_pos u).ne', Real.log_exp]
  have hyf (u : ℝ) (v : ↥A.Sf) :
      (sheetPointRaw A (T₀ * Real.exp u) t).val.2 v = (t.val.2 v).val := by
    have hpos := mul_pos hT₀ (Real.exp_pos u)
    unfold sheetPointRaw ellRaw
    rw [dif_pos hpos]
    change (t.val.2 v).val * (A.radialSection _ hpos).2 v = _
    simp [SArithmeticData.radialSection]
  have hya (u : ℝ) (w : InfinitePlace F) :
      InfinitePlace.Completion.extensionEmbedding w
        ((sheetPointRaw A (T₀ * Real.exp u) t).val.1 w) =
      InfinitePlace.Completion.extensionEmbedding w ((t.val.1 w).val) * (r u : ℂ) := by
    have hpos := mul_pos hT₀ (Real.exp_pos u)
    unfold sheetPointRaw ellRaw
    rw [dif_pos hpos]
    change InfinitePlace.Completion.extensionEmbedding w
      ((t.val.1 w).val * ((A.radialSection _ hpos).1 w).val) = _
    rw [map_mul]
    congr 1
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
        (((T₀ * Real.exp u) ^ p : ℝ) : ℂ)) = _
    rw [RingEquiv.apply_symm_apply, hscale]
  have hphase (u : ℝ) (x : SLocalProduct F A.Sf) :
      ProbeAdditive.phase F A.Sf e
        (-x * (sheetPointRaw A (T₀ * Real.exp u) t).val) =
      d x * Complex.exp ((c x * r u : ℝ) * Complex.I) := by
    unfold ProbeAdditive.phase ProbeAdditive.archPhase
    have hfin : (∏ v : ↥A.Sf,
        (e v ((-x * (sheetPointRaw A (T₀ * Real.exp u) t).val).2 v) : ℂ)) = d x := by
      apply Finset.prod_congr rfl
      intro v _
      change (e v (-x.2 v * (sheetPointRaw A (T₀ * Real.exp u) t).val.2 v) : ℂ) = _
      rw [hyf]
    rw [hfin, mul_comm]
    congr 1
    have harch (w : InfinitePlace F) :
        (InfinitePlace.Completion.extensionEmbedding w
          ((-x * (sheetPointRaw A (T₀ * Real.exp u) t).val).1 w)).re =
        (InfinitePlace.Completion.extensionEmbedding w
          (-x.1 w * (t.val.1 w).val)).re * r u := by
      change (InfinitePlace.Completion.extensionEmbedding w
        (-x.1 w * (sheetPointRaw A (T₀ * Real.exp u) t).val.1 w)).re = _
      rw [map_mul, hya, ← mul_assoc, ← map_mul]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    simp only [harch]
    congr 1
    dsimp [c]
    push_cast
    simp only [← mul_assoc, ← Finset.sum_mul]
    ring
  have h := (compact_phase_integral_contDiff μ W0 d c hW0 hd hc hcompact).comp hr
  convert h using 1
  funext u
  unfold ProbeWeight.fourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [hphase]
    simp only [mul_assoc]

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds.SheetContinuityAtoms.Regularity

end

section
namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds.SheetContinuityAtoms.Derivative
noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain MeasureTheory Filter
variable {F : Type} [Field F] [NumberField F]
local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _
local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

private theorem compact_integral_deriv {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f d : ℝ → X → ℂ) (K : Set X) (hK : IsCompact K)
    (hf : Continuous (Function.uncurry f)) (hd : Continuous (Function.uncurry d))
    (hs : ∀ v x, x ∉ K → f v x = 0 ∧ d v x = 0)
    (hder : ∀ v x, HasDerivAt (fun v => f v x) (d v x) v) (v : ℝ) :
    Integrable (d v) μ ∧ HasDerivAt (fun v => ∫ x, f v x ∂μ) (∫ x, d v x ∂μ) v := by
  have hcf (v) : HasCompactSupport (f v) := by
    apply HasCompactSupport.intro hK
    intro x hx
    exact (hs v x hx).1
  have hcd (v) : HasCompactSupport (d v) := by
    apply HasCompactSupport.intro hK
    intro x hx
    exact (hs v x hx).2
  obtain ⟨B, hB⟩ := ((isCompact_closedBall v 1).prod hK).exists_bound_of_continuousOn hd.continuousOn
  have hm (v : ℝ) : Continuous (f v) := hf.comp (continuous_const.prodMk continuous_id)
  have hdm (v : ℝ) : Continuous (d v) := hd.comp (continuous_const.prodMk continuous_id)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball v 1) (bound := K.indicator (fun _ => max B 0))
    (Metric.ball_mem_nhds v zero_lt_one)
    (Eventually.of_forall fun v => (hm v).aestronglyMeasurable)
    ((hm v).integrable_of_hasCompactSupport (hcf v))
    (hdm v).aestronglyMeasurable ?_ ?_ ?_)
  · exact Eventually.of_forall fun x a ha => by
      by_cases hx : x ∈ K
      · simpa [Set.indicator_of_mem hx] using
          (hB (a, x) ⟨Metric.ball_subset_closedBall ha, hx⟩).trans (le_max_left B 0)
      · simp [Set.indicator_of_notMem hx, (hs a x hx).2]
  · exact (integrable_indicator_iff hK.measurableSet).2
      (integrableOn_const (C := max B 0) (μ := μ) (s := K) hK.measure_lt_top.ne)
  · exact Eventually.of_forall fun x a _ => hder a x

 def prof (A : SArithmeticData F) (a : InfinitePlace F → ℝ)
    (y : SLocalProduct F A.Sf) : SLocalProduct F A.Sf :=
  (fun w => (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm (a w : ℂ) * y.1 w, y.2)

private theorem prof_phase (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (a : InfinitePlace F → ℝ) (x y : SLocalProduct F A.Sf) :
    ProbeAdditive.phase F A.Sf e (-x * prof A a y) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ w, 2 * a w * (InfinitePlace.Completion.extensionEmbedding w (-x.1 w * y.1 w)).re) : ℂ)) *
        ∏ v : ↥A.Sf, (e v (-x.2 v * y.2 v) : ℂ) := by
  have ht : (∑ w, 2 * (InfinitePlace.Completion.extensionEmbedding w ((-x * prof A a y).1 w)).re) =
      ∑ w, 2 * a w * (InfinitePlace.Completion.extensionEmbedding w (-x.1 w * y.1 w)).re := by
    apply Finset.sum_congr rfl
    intro w _
    have heq : InfinitePlace.Completion.extensionEmbedding w
      (-x.1 w * ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm (a w : ℂ) * y.1 w)) =
        (a w : ℂ) * InfinitePlace.Completion.extensionEmbedding w (-x.1 w * y.1 w) := by
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)) _ = _
      simp only [map_mul, RingEquiv.apply_symm_apply, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
      ring
    change 2 * (InfinitePlace.Completion.extensionEmbedding w (-x.1 w * ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm (a w : ℂ) * y.1 w))).re = _
    rw [heq]
    simp [Complex.mul_re]
    ring
  have ht' := congrArg (fun r : ℝ => (r : ℂ)) ht
  push_cast at ht'
  unfold ProbeAdditive.phase ProbeAdditive.archPhase
  rw [ht']
  rfl

private theorem prof_kernel_deriv (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (a da : ℝ → InfinitePlace F → ℝ) (ha : ∀ v w, HasDerivAt (fun v => a v w) (da v w) v)
    (W : SLocalProduct F A.Sf → ℂ) (x y : SLocalProduct F A.Sf) (v : ℝ) :
    HasDerivAt (fun v => W x * ProbeAdditive.phase F A.Sf e (-x * prof A (a v) y))
      (W x * ProbeAdditive.phase F A.Sf e (-x * prof A (a v) y) *
        (2 * (Real.pi : ℂ) * Complex.I *
          ((∑ w, 2 * da v w * (InfinitePlace.Completion.extensionEmbedding w (-x.1 w * y.1 w)).re) : ℂ))) v := by
  simp_rw [prof_phase]
  have h := ((HasDerivAt.fun_sum (u := Finset.univ) (fun w _ =>
    ((ha v w).const_mul 2).mul_const
      (InfinitePlace.Completion.extensionEmbedding w (-x.1 w * y.1 w)).re)).ofReal_comp.const_mul
        (2 * (Real.pi : ℂ) * Complex.I)).cexp
  convert (h.const_mul (W x)).mul_const
      (∏ v : ↥A.Sf, (e v (-x.2 v * y.2 v) : ℂ)) using 1
  · funext v; push_cast; ring
  · push_cast; ring

 def coeff {A : SArithmeticData F} (da : InfinitePlace F → ℝ) (x y : SLocalProduct F A.Sf) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I *
    ((∑ w, 2 * da w * (InfinitePlace.Completion.extensionEmbedding w (-x.1 w * y.1 w)).re : ℝ) : ℂ)

private theorem prof_fourier_deriv (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle) (he : ∀ v, Continuous (e v))
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (W : SLocalProduct F A.Sf → ℂ) (hW : Continuous W) (hK : HasCompactSupport W)
    (a da : ℝ → InfinitePlace F → ℝ)
    (ha : ∀ v w, HasDerivAt (fun v => a v w) (da v w) v)
    (hca : ∀ w, Continuous (fun v => a v w)) (hcda : ∀ w, Continuous (fun v => da v w))
    (y : SLocalProduct F A.Sf) (v : ℝ) :
    Integrable (fun x => W x * ProbeAdditive.phase F A.Sf e (-x * prof A (a v) y) * coeff (da v) x y) μ ∧
    HasDerivAt (fun v => ProbeWeight.fourier F A.Sf e μ W (prof A (a v) y))
      (∫ x, W x * ProbeAdditive.phase F A.Sf e (-x * prof A (a v) y) * coeff (da v) x y ∂μ) v := by
  letI := hμ
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : A.Sf) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
    (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
  letI : SecondCountableTopology (SLocalProduct F A.Sf) := inferInstance
  have hcont (w : InfinitePlace F) : Continuous (fun p : ℝ × SLocalProduct F A.Sf =>
      (InfinitePlace.Completion.extensionEmbedding w (-p.2.1 w * y.1 w)).re) := by
    exact Complex.continuous_re.comp ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((((continuous_apply w).comp (continuous_fst.comp continuous_snd)).neg).mul continuous_const))
  have hcoord := hca
  have hdcoord := hcda
  have hp : Continuous (fun p : ℝ × SLocalProduct F A.Sf =>
      ProbeAdditive.phase F A.Sf e (-p.2 * prof A (a p.1) y)) := by
    simp_rw [prof_phase]
    apply Continuous.mul
    · apply Continuous.cexp
      apply Continuous.const_mul
      apply continuous_finset_sum
      intro w _
      exact ((Complex.continuous_ofReal.comp ((hcoord w).comp continuous_fst)).const_mul 2).mul
        (Complex.continuous_ofReal.comp (hcont w))
    · apply continuous_finset_prod
      intro v _
      exact continuous_subtype_val.comp ((he v).comp
        ((((continuous_apply v).comp (continuous_snd.comp continuous_snd)).neg).mul continuous_const))
  have hdc : Continuous (fun p : ℝ × SLocalProduct F A.Sf => coeff (da p.1) p.2 y) := by
    unfold coeff
    push_cast
    apply Continuous.const_mul
    apply continuous_finset_sum
    intro w _
    exact ((Complex.continuous_ofReal.comp ((hdcoord w).comp continuous_fst)).const_mul 2).mul
      (Complex.continuous_ofReal.comp (hcont w))
  exact compact_integral_deriv μ
    (fun v x => W x * ProbeAdditive.phase F A.Sf e (-x * prof A (a v) y))
    (fun v x => W x * ProbeAdditive.phase F A.Sf e (-x * prof A (a v) y) * coeff (da v) x y)
    (tsupport W) hK.isCompact
    ((hW.comp continuous_snd).mul hp) (((hW.comp continuous_snd).mul hp).mul hdc)
    (fun v x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    (fun v x => by simpa only [coeff, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_ofNat] using prof_kernel_deriv A e a da ha W x y v) v

set_option backward.isDefEq.respectTransparency false in
private theorem prof_single (A : SArithmeticData F) (w : InfinitePlace F)
    (v : ℝ) (y : SLocalProduct F A.Sf) :
    prof A (fun j => if j = w then Real.exp (v / 2) else 1) y = complexNormFlowRaw A w v y := by
  apply Prod.ext
  · funext j
    by_cases hj : j = w
    · subst j; simp [prof, complexNormFlowRaw, Function.update_self]
    · simp [prof, complexNormFlowRaw, hj, Ne.symm hj, Function.update_of_ne]
  · rfl

private theorem sheet_prof (A : SArithmeticData F) (T : ℝ) (hT : 0 < T)
    (t : A.G1) (u v : ℝ) :
    (sheetPointRaw A (T * Real.exp v) t).val =
      prof A (fun _ => Real.exp ((v-u) / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))))
        (sheetPointRaw A (T * Real.exp u) t).val := by
  have hv : 0 < T * Real.exp v := mul_pos hT (Real.exp_pos _)
  have hu : 0 < T * Real.exp u := mul_pos hT (Real.exp_pos _)
  have hr : (T * Real.exp v) ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) =
      Real.exp ((v-u) / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) *
        (T * Real.exp u) ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) := by
    rw [Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hu, ← Real.exp_add,
      Real.log_mul hT.ne' (Real.exp_ne_zero _), Real.log_mul hT.ne' (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp]
    congr 1
    ring
  apply Prod.ext
  · funext w
    change ((localUnitsRaw A t.val).val * (ellRaw A (T * Real.exp v)).val).1 w = _
    simp only [ellRaw, dif_pos hv, dif_pos hu, prof, localUnitsRaw, sheetPointRaw,
      SArithmeticData.radialSection]
    change (t.val.1 w).val *
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
        (((T * Real.exp v) ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℝ) : ℂ) =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
        (Real.exp ((v-u) / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℂ) *
      ((t.val.1 w).val *
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
          (((T * Real.exp u) ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℝ) : ℂ))
    rw [hr, Complex.ofReal_mul, map_mul]
    ring
  · funext w
    simp only [sheetPointRaw, ellRaw, dif_pos hv, dif_pos hu, prof, localUnitsRaw,
      SArithmeticData.radialSection]
    rfl

set_option backward.isDefEq.respectTransparency false in

theorem fourier_log_radial_deriv
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (W0 : SLocalProduct F A.Sf → ℂ) (hW0 : Continuous W0)
    (hcompact : HasCompactSupport W0) (T₀ : ℝ) (hT₀ : 0 < T₀)
    (t : A.G1) (u : ℝ) :
    deriv (fun v : ℝ => ProbeWeight.fourier F A.Sf e μ W0
      (sheetPointRaw A (T₀ * Real.exp v) t).val) u =
    (InfinitePlace.nrComplexPlaces F : ℂ)⁻¹ *
      ∑ w : InfinitePlace F, logDerivativeRaw A w 1
        (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A (T₀ * Real.exp u) t).val := by
  let r : ℝ := InfinitePlace.nrComplexPlaces F
  let y := (sheetPointRaw A (T₀ * Real.exp u) t).val
  let a : ℝ → InfinitePlace F → ℝ := fun v _ => Real.exp ((v-u) / (2*r))
  let da : ℝ → InfinitePlace F → ℝ := fun v _ => Real.exp ((v-u) / (2*r)) / (2*r)
  have hda : ∀ v w, HasDerivAt (fun v => a v w) (da v w) v := by
    intro v w
    simpa [a, da, div_eq_mul_inv, mul_comm] using
      (((hasDerivAt_id v).sub_const u).div_const (2*r)).exp
  have hca (w) : Continuous (fun v => a v w) := by unfold a; fun_prop
  have hcda (w) : Continuous (fun v => da v w) := by unfold da; fun_prop
  have H := prof_fourier_deriv A e he μ hμ W0 hW0 hcompact a da hda hca hcda y u
  have hprof : ∀ v, prof A (a v) y = (sheetPointRaw A (T₀ * Real.exp v) t).val :=
    fun v => (sheet_prof A T₀ hT₀ t u v).symm
  have hzero : prof A (a u) y = y := by
    apply Prod.ext
    · funext w; simp [prof, a]
    · rfl
  have hd := H.2
  simp_rw [hprof] at hd
  rw [hd.deriv]
  have hsingle (w : InfinitePlace F) :
      Integrable (fun x => W0 x * ProbeAdditive.phase F A.Sf e (-x*y) *
        coeff (fun j => if j = w then (1/2 : ℝ) else 0) x y) μ ∧
      logDerivativeRaw A w 1 (ProbeWeight.fourier F A.Sf e μ W0) y =
        ∫ x, W0 x * ProbeAdditive.phase F A.Sf e (-x*y) *
          coeff (fun j => if j = w then (1/2 : ℝ) else 0) x y ∂μ := by
    let b : ℝ → InfinitePlace F → ℝ := fun v j => if j = w then Real.exp (v/2) else 1
    let db : ℝ → InfinitePlace F → ℝ := fun v j => if j = w then Real.exp (v/2) / 2 else 0
    have hb : ∀ v j, HasDerivAt (fun v => b v j) (db v j) v := by
      intro v j
      by_cases hj : j = w
      · simpa [b, db, hj, div_eq_mul_inv, mul_comm] using ((hasDerivAt_id v).div_const 2).exp
      · simpa [b, db, hj] using hasDerivAt_const v (1 : ℝ)
    have hcb (j) : Continuous (fun v => b v j) := by unfold b; split_ifs <;> fun_prop
    have hcdb (j) : Continuous (fun v => db v j) := by unfold db; split_ifs <;> fun_prop
    obtain ⟨hi, hd⟩ := prof_fourier_deriv A e he μ hμ W0 hW0 hcompact b db hb hcb hcdb y 0
    have hby : prof A (b 0) y = y := by
      apply Prod.ext
      · funext j; simp [prof, b]
      · rfl
    simp only [hby] at hi hd
    have hdb : db 0 = fun j => if j = w then (1/2 : ℝ) else 0 := by
      funext j; simp [db]
    rw [hdb] at hi hd
    refine ⟨hi, ?_⟩
    unfold logDerivativeRaw
    rw [iteratedDeriv_one]
    have heq : (fun v => ProbeWeight.fourier F A.Sf e μ W0 (prof A (b v) y)) =
        (fun v => ProbeWeight.fourier F A.Sf e μ W0 (complexNormFlowRaw A w v y)) := by
      funext v; rw [prof_single]
    rw [heq] at hd
    exact hd.deriv
  change (∫ x, W0 x * ProbeAdditive.phase F A.Sf e (-x * y) * coeff (da u) x y ∂μ) =
    (InfinitePlace.nrComplexPlaces F : ℂ)⁻¹ * ∑ w, logDerivativeRaw A w 1 (ProbeWeight.fourier F A.Sf e μ W0) y
  simp_rw [(hsingle _).2]
  rw [← integral_finset_sum _ (fun w _ => (hsingle w).1), ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have hdau : da u = fun _ => 1 / (2*r) := by funext w; simp [da]
  rw [hdau]
  change W0 x * ProbeAdditive.phase F A.Sf e (-x*y) * coeff (fun _ => 1/(2*r)) x y = _
  simp only [coeff]
  push_cast
  simp only [Finset.mul_sum, ← mul_assoc]
  apply Finset.sum_congr rfl
  intro w _
  simp only [apply_ite Complex.ofReal, mul_ite, ite_mul, mul_zero, zero_mul,
    Complex.ofReal_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  dsimp [r]
  push_cast
  ring

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds.SheetContinuityAtoms.Derivative

end

section
namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds.SheetContinuityAtoms.Integrability
noncomputable section
set_option maxHeartbeats 800000
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

private theorem sheet_continuous (A : SArithmeticData F) :
    Continuous (fun p : {T : ℝ // 0 < T} × A.G1 => (sheetPointRaw A p.1 p.2).val) := by
  have hc : Continuous (localUnitsRaw A) := by
    change Continuous (Homeomorph.prodUnits.symm ∘
      (ContinuousMulEquiv.piUnits.symm.toHomeomorph.prodCongr
        ContinuousMulEquiv.piUnits.symm.toHomeomorph))
    fun_prop
  have he : (fun p : {T : ℝ // 0 < T} × A.G1 => (sheetPointRaw A p.1 p.2).val) =
      fun p => (localUnitsRaw A p.2.val).val *
        (localUnitsRaw A (A.radialSection p.1.val p.1.property)).val := by
    funext p
    simp [sheetPointRaw, ellRaw, p.1.property]
  rw [he]
  exact (Units.continuous_val.comp (hc.comp
    (continuous_subtype_val.comp continuous_snd))).mul
    (Units.continuous_val.comp (hc.comp
      (A.continuous_radialSection.comp continuous_fst)))

private theorem sheet_bounds
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (dt : @Measure A.G1 (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (w : InfinitePlace F) (k : ℕ)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      Integrable (fun t => logDerivativeRaw A w k
        (ProbeWeight.fourier F A.Sf e μ W0) (sheetPointRaw A T t).val) dt ∧
      (∫ t, ‖logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A T t).val‖ ∂dt) ≤ C * T ^ (-1 : ℝ) := by
  obtain ⟨M, R, hM, hR, hbound⟩ :=
    raw_fourier_log_derivative_envelope A e he hne μ hμ w k 2 W0 hW0 hcompact
  obtain ⟨C, hC, hsheet⟩ :=
    raw_radial_envelope_sheet_bounds A dt hdt 1 2 R (by norm_num) (by norm_num) hR
  have hc := raw_fourier_log_derivative_continuous A e he μ hμ w k W0 hW0 hcompact
  refine ⟨M * C, mul_nonneg hM hC, ?_⟩
  intro T hT
  obtain ⟨hB, hBbound⟩ := hsheet T hT
  have hp : Continuous (fun t : A.G1 => ((⟨T, hT⟩ : {T : ℝ // 0 < T}), t)) :=
    continuous_const.prodMk continuous_id
  have hs : Continuous (fun t : A.G1 => (sheetPointRaw A T t).val) :=
    Continuous.comp
      (g := fun p : {T : ℝ // 0 < T} × A.G1 => (sheetPointRaw A p.1 p.2).val)
      (f := fun t : A.G1 => ((⟨T, hT⟩ : {T : ℝ // 0 < T}), t))
      (sheet_continuous A) hp
  have hm : AEStronglyMeasurable (fun t : A.G1 =>
      logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A T t).val) dt := by
    apply Continuous.aestronglyMeasurable
    exact Continuous.comp
      (g := logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0))
      (f := fun t : A.G1 => (sheetPointRaw A T t).val) hc hs
  have hmajorant := hB.const_mul M
  have hb : ∀ᵐ t ∂dt,
      ‖logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A T t).val‖ ≤
      M * radialFiniteEnvelopeRaw A 2 R (sheetPointRaw A T t).val :=
    Filter.Eventually.of_forall fun t => hbound _
  have hi := hmajorant.mono' hm hb
  refine ⟨hi, ?_⟩
  calc
    (∫ t, ‖logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A T t).val‖ ∂dt) ≤
        ∫ t, M * radialFiniteEnvelopeRaw A 2 R (sheetPointRaw A T t).val ∂dt :=
      integral_mono_ae hi.norm hmajorant hb
    _ = M * (∫ t, radialFiniteEnvelopeRaw A 2 R (sheetPointRaw A T t).val ∂dt) :=
      integral_const_mul _ _
    _ ≤ M * (C * T ^ (-1 : ℝ)) := mul_le_mul_of_nonneg_left hBbound hM
    _ = (M * C) * T ^ (-1 : ℝ) := (mul_assoc _ _ _).symm

theorem fourier_log_radial_integrability
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (dt : @Measure A.G1 (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x})
    (T₀ : ℝ) (hT₀ : 0 < T₀) (a b : ℝ) :
    Integrable (fun t => ProbeWeight.fourier F A.Sf e μ W0
      (sheetPointRaw A T₀ t).val) dt ∧
    ∀ w : InfinitePlace F, Integrable (fun p : ℝ × A.G1 =>
      logDerivativeRaw A w 1 (ProbeWeight.fourier F A.Sf e μ W0)
        (sheetPointRaw A (T₀ * Real.exp p.1) p.2).val)
      ((volume.restrict (Set.Ioc a b)).prod dt) := by
  letI := hdt
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : A.Sf) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  letI : SecondCountableTopology A.G := inferInstance
  letI : SecondCountableTopology A.G1 :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI (v : A.Sf) : LocallyCompactSpace (v.val.adicCompletion F) :=
    (PoissonS.finite_components_locallyCompact F A.Sf).1 v
  letI : LocallyCompactSpace A.G := inferInstance
  have hn : Continuous A.norm := by
    unfold SArithmeticData.norm
    fun_prop
  letI : LocallyCompactSpace A.G1 :=
    IsClosed.locallyCompactSpace (isClosed_singleton.preimage hn)
  letI : SFinite dt := inferInstance
  have hp : Continuous (fun p : ℝ × A.G1 =>
      ((⟨T₀ * Real.exp p.1, mul_pos hT₀ (Real.exp_pos _)⟩ :
        {T : ℝ // 0 < T}), p.2)) := by
    fun_prop
  have hs : Continuous (fun p : ℝ × A.G1 =>
      (sheetPointRaw A (T₀ * Real.exp p.1) p.2).val) :=
    Continuous.comp
      (g := fun p : {T : ℝ // 0 < T} × A.G1 => (sheetPointRaw A p.1 p.2).val)
      (f := fun p : ℝ × A.G1 =>
        ((⟨T₀ * Real.exp p.1, mul_pos hT₀ (Real.exp_pos _)⟩ :
          {T : ℝ // 0 < T}), p.2))
      (sheet_continuous A) hp
  constructor
  · let w : InfinitePlace F := Classical.arbitrary _
    obtain ⟨C, hC, hb⟩ := sheet_bounds A e he hne μ dt hμ hdt w 0 W0 hW0 hcompact
    have hz : ∀ x : SLocalProduct F A.Sf, complexNormFlowRaw A w 0 x = x := by
      intro x
      apply Prod.ext
      · funext v
        by_cases hv : v = w
        · subst v
          simp only [complexNormFlowRaw, zero_div, Real.exp_zero,
            Complex.ofReal_one, map_one, one_mul]
          exact Function.update_self _ _ _
        · exact Function.update_of_ne hv _ _
      · rfl
    simpa only [logDerivativeRaw, iteratedDeriv_zero, hz] using (hb T₀ hT₀).1
  · intro w
    obtain ⟨C, hC, hb⟩ := sheet_bounds A e he hne μ dt hμ hdt w 1 W0 hW0 hcompact
    have hc := raw_fourier_log_derivative_continuous A e he μ hμ w 1 W0 hW0 hcompact
    have hm : AEStronglyMeasurable (fun p : ℝ × A.G1 =>
        logDerivativeRaw A w 1 (ProbeWeight.fourier F A.Sf e μ W0)
          (sheetPointRaw A (T₀ * Real.exp p.1) p.2).val)
        ((volume.restrict (Set.Ioc a b)).prod dt) := by
      apply Continuous.aestronglyMeasurable
      exact Continuous.comp
        (g := logDerivativeRaw A w 1 (ProbeWeight.fourier F A.Sf e μ W0))
        (f := fun p : ℝ × A.G1 => (sheetPointRaw A (T₀ * Real.exp p.1) p.2).val)
        hc hs
    apply (integrable_prod_iff hm).mpr
    constructor
    · exact Filter.Eventually.of_forall fun u => (hb _ (mul_pos hT₀ (Real.exp_pos u))).1
    · have hbound : Integrable (fun u : ℝ => C * (T₀ * Real.exp u) ^ (-1 : ℝ))
          (volume.restrict (Set.Ioc a b)) := by
        apply IntegrableOn.mono_set (t := Set.Icc a b) _ Set.Ioc_subset_Icc_self
        apply ContinuousOn.integrableOn_Icc
        apply Continuous.continuousOn
        simp only [Real.rpow_neg_one]
        exact continuous_const.mul
          ((continuous_const.mul Real.continuous_exp).inv₀
            (fun u => ne_of_gt (mul_pos hT₀ (Real.exp_pos u))))
      apply hbound.mono' hm.norm.integral_prod_right'
      apply Filter.Eventually.of_forall
      intro u
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact (hb _ (mul_pos hT₀ (Real.exp_pos u))).2

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds.SheetContinuityAtoms.Integrability

end

section
namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain MeasureTheory Filter
variable {F : Type} [Field F] [NumberField F]
local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _
local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩
local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩
private theorem raw_continuous_localUnits (A : SArithmeticData F) : Continuous (localUnitsRaw A) := by
  change Continuous (Homeomorph.prodUnits.symm ∘
    (ContinuousMulEquiv.piUnits.symm.toHomeomorph.prodCongr
      ContinuousMulEquiv.piUnits.symm.toHomeomorph))
  fun_prop
theorem raw_sheet_continuous (A : SArithmeticData F) :
    Continuous (fun p : {T : ℝ // 0 < T} × A.G1 => (sheetPointRaw A p.1 p.2).val) := by
  have he : (fun p : {T : ℝ // 0 < T} × A.G1 => (sheetPointRaw A p.1 p.2).val) =
      fun p => (localUnitsRaw A p.2.val).val * (localUnitsRaw A (A.radialSection p.1.val p.1.property)).val := by
    funext p
    simp [sheetPointRaw, ellRaw, p.1.property]
  rw [he]
  exact (Units.continuous_val.comp ((raw_continuous_localUnits A).comp
    (continuous_subtype_val.comp continuous_snd))).mul
    (Units.continuous_val.comp ((raw_continuous_localUnits A).comp
      (A.continuous_radialSection.comp continuous_fst)))
private theorem raw_annular_continuous (A : SArithmeticData F)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0) : Continuous W0 := by
  obtain ⟨fr, fc, ff, hr, hc, hf, heq⟩ := hW0
  have hm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  have he : W0 = (fun x =>
      (∏ v, fr v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 v)) *
      (∏ v, fc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
      ∏ v : ↥A.Sf, ff v (x.2 v)) := funext heq
  rw [he]
  apply Continuous.mul
  · apply Continuous.mul
    · apply continuous_finset_prod
      intro v hv
      exact (hr v).1.continuous.comp ((continuous_apply v).comp (continuous_fst.comp (hm.comp continuous_fst)))
    · apply continuous_finset_prod
      intro v hv
      exact (hc v).1.continuous.comp ((continuous_apply v).comp (continuous_snd.comp (hm.comp continuous_fst)))
  · apply continuous_finset_prod
    intro v hv
    exact (hf v).1.continuous.comp ((continuous_apply v).comp continuous_snd)
theorem raw_fourier_continuous (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) : Continuous (ProbeWeight.fourier F A.Sf e μ W0) := by
  letI := hμ
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : A.Sf) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : Countable (InfinitePlace F) := inferInstance
  letI : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
    (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
  letI : SecondCountableTopology (SLocalProduct F A.Sf) := inferInstance
  have hc := raw_annular_continuous A W0 hW0
  have hp : Continuous (ProbeAdditive.phase F A.Sf e) :=
    ProbeAdditiveGramBounds.trace_phase_continuous F A.Sf e he _ (fun _ => rfl)
  have hn : ∀ x, ‖ProbeAdditive.phase F A.Sf e x‖ = 1 :=
    ProbeAdditiveGramBounds.trace_phase_norm F A.Sf e _ (fun _ => rfl)
  exact continuous_of_dominated
    (fun y => (hc.mul (hp.comp (continuous_neg.mul continuous_const))).aestronglyMeasurable)
    (fun y => Filter.Eventually.of_forall fun x => by simp [norm_mul, hn])
    (hc.integrable_of_hasCompactSupport hcompact).norm
    (Filter.Eventually.of_forall fun x =>
      (continuous_const.mul (hp.comp (continuous_const.mul continuous_id))))
theorem raw_sheet_integral_continuous_of_majorant (A : SArithmeticData F)
    (dt : @Measure A.G1 (borel _)) (f : SLocalProduct F A.Sf → ℂ)
    (hf : Continuous f)
    (hmajorant : ∀ T₀ : {T : ℝ // 0 < T}, ∃ B : A.G1 → ℝ,
      Integrable B dt ∧ ∀ᶠ T in 𝓝 T₀, ∀ᵐ t ∂dt,
        ‖f (sheetPointRaw A T.val t).val‖ ≤ B t) :
    ContinuousOn (fun T : ℝ => ∫ t, f (sheetPointRaw A T t).val ∂dt) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_iff_continuousAt.mpr
  intro T₀
  obtain ⟨B, hB, hbound⟩ := hmajorant T₀
  refine continuousAt_of_dominated (bound := B) ?_ hbound hB ?_
  · exact Filter.Eventually.of_forall fun T =>
      (hf.comp ((raw_sheet_continuous A).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t =>
      (hf.comp ((raw_sheet_continuous A).comp
        (continuous_id.prodMk continuous_const))).continuousAt

section RadialFTC
open Set
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem anchored_bound (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hi : IntervalIntegrable (fun u => ‖deriv f u‖) volume (-1) 1)
    {u : ℝ} (hu : u ∈ Icc (-1) 1) :
    ‖f u‖ ≤ ‖f 0‖ + ∫ v in (-1 : ℝ)..1, ‖deriv f v‖ := by
  have hc : Continuous f := hf.continuous
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hbi : IntegrableOn (fun u => ‖deriv f u‖) (Ioc (-1) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hi
  have hstep (a b : ℝ) (hab : a ≤ b) (ha : -1 ≤ a) (hb : b ≤ 1) :
      ‖f b - f a‖ ≤ ∫ v in (-1 : ℝ)..1, ‖deriv f v‖ := by
    have hs : Ioc a b ⊆ Ioc (-1) 1 := Ioc_subset_Ioc ha hb
    calc
      ‖f b - f a‖ ≤ ∫ v in a..b, ‖deriv f v‖ := by
        apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hc.continuousOn
          hd.differentiableOn (Eventually.of_forall (fun _ _ => le_rfl))
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hbi.mono_set hs)
      _ ≤ ∫ v in (-1 : ℝ)..1, ‖deriv f v‖ := by
        rw [intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact setIntegral_mono_set hbi (Eventually.of_forall (fun _ => norm_nonneg _))
          (Eventually.of_forall (fun _ h => hs h))
  have hdisp : ‖f u - f 0‖ ≤ ∫ v in (-1 : ℝ)..1, ‖deriv f v‖ := by
    by_cases h : 0 ≤ u
    · exact hstep 0 u h (by norm_num) hu.2
    · rw [norm_sub_rev]
      exact hstep u 0 (le_of_not_ge h) hu.1 (by norm_num)
  exact (norm_le_insert' (f u) (f 0)).trans (add_le_add_right hdisp _)
theorem radial_derivative_integrable_majorant [SFinite μ] (f : ℝ → X → ℂ)
    (hf : ∀ x, ContDiff ℝ 1 (fun u => f u x))
    (h0 : Integrable (f 0) μ)
    (h1 : Integrable (fun p : ℝ × X => deriv (fun u => f u p.2) p.1)
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod μ)) :
    ∃ B : X → ℝ, Integrable B μ ∧ ∀ u ∈ Icc (-1 : ℝ) 1,
      ∀ᵐ x ∂μ, ‖f u x‖ ≤ B x := by
  refine ⟨fun x => ‖f 0 x‖ + ∫ u in (-1 : ℝ)..1,
      ‖deriv (fun v => f v x) u‖, ?_, ?_⟩
  · simp only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact h0.norm.add h1.integral_norm_prod_right
  · intro u hu
    filter_upwards [h1.prod_left_ae] with x hx
    exact anchored_bound (fun v => f v x) (hf x)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hx.norm) hu

end RadialFTC

private theorem raw_secondCountable_G1 (A : SArithmeticData F) :
    SecondCountableTopology A.G1 := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : A.Sf) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completionᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology A.G := inferInstance
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

theorem positive_sheet_continuous
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (dt : @Measure A.G1 (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x})
    : ContinuousOn (fun T : ℝ =>
      ∫ t, ProbeWeight.fourier F A.Sf e μ W0 (sheetPointRaw A T t).val ∂dt)
      (Set.Ioi 0) := by
  letI := hdt
  letI := raw_secondCountable_G1 A
  letI (v : A.Sf) : LocallyCompactSpace (v.val.adicCompletion F) :=
    (PoissonS.finite_components_locallyCompact F A.Sf).1 v
  letI : LocallyCompactSpace A.G := inferInstance
  have hnorm : Continuous A.norm := by
    unfold SArithmeticData.norm
    fun_prop
  letI : LocallyCompactSpace A.G1 :=
    IsClosed.locallyCompactSpace (isClosed_singleton.preimage hnorm)
  letI : SFinite dt := inferInstance
  apply raw_sheet_integral_continuous_of_majorant A dt _
    (raw_fourier_continuous A e he μ hμ W0 hW0 hcompact)
  intro T₀
  let f : ℝ → A.G1 → ℂ := fun u t => ProbeWeight.fourier F A.Sf e μ W0
    (sheetPointRaw A (T₀.val * Real.exp u) t).val
  have hf : ∀ t, ContDiff ℝ 1 (fun u => f u t) := fun t =>
    SheetContinuityAtoms.Regularity.fourier_log_radial_contDiff A e he μ hμ W0
      (raw_annular_continuous A W0 hW0) hcompact T₀.val T₀.property t
  obtain ⟨h0, h1⟩ := SheetContinuityAtoms.Integrability.fourier_log_radial_integrability
    A e he hne μ dt hμ hdt W0 hW0 hcompact hannular T₀.val T₀.property (-1) 1
  have hf0 : Integrable (f 0) dt := by simpa [f] using h0
  have hderiv : Integrable (fun p : ℝ × A.G1 => deriv (fun u => f u p.2) p.1)
      ((volume.restrict (Set.Ioc (-1 : ℝ) 1)).prod dt) := by
    have heq : (fun p : ℝ × A.G1 => deriv (fun u => f u p.2) p.1) =
        fun p => (InfinitePlace.nrComplexPlaces F : ℂ)⁻¹ *
          ∑ w : InfinitePlace F, logDerivativeRaw A w 1
            (ProbeWeight.fourier F A.Sf e μ W0)
            (sheetPointRaw A (T₀.val * Real.exp p.1) p.2).val := by
      funext p
      exact SheetContinuityAtoms.Derivative.fourier_log_radial_deriv A e he μ hμ W0
        (raw_annular_continuous A W0 hW0) hcompact T₀.val T₀.property p.2 p.1
    rw [heq]
    exact (integrable_finset_sum Finset.univ (fun w _ => h1 w)).const_mul _
  obtain ⟨B, hB, hb⟩ := radial_derivative_integrable_majorant f hf hf0 hderiv
  refine ⟨B, hB, ?_⟩
  have hg : Continuous (fun T : {T : ℝ // 0 < T} => Real.log (T.val / T₀.val)) :=
    (continuous_subtype_val.div_const T₀.val).log
      (fun T => (div_pos T.property T₀.property).ne')
  have hg0 : Real.log (T₀.val / T₀.val) = 0 := by simp [T₀.property.ne']
  have hnear : ∀ᶠ T : {T : ℝ // 0 < T} in 𝓝 T₀,
      Real.log (T.val / T₀.val) ∈ Set.Icc (-1 : ℝ) 1 := by
    apply hg.continuousAt.eventually
    change ∀ᶠ y : ℝ in 𝓝 (Real.log (T₀.val / T₀.val)), y ∈ Set.Icc (-1 : ℝ) 1
    rw [hg0]
    exact Icc_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hnear] with T hT
  have heq : T₀.val * Real.exp (Real.log (T.val / T₀.val)) = T.val := by
    rw [Real.exp_log (div_pos T.property T₀.property)]
    exact mul_div_cancel₀ T.val T₀.property.ne'
  simpa only [f, heq] using hb (Real.log (T.val / T₀.val)) hT

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds

end
