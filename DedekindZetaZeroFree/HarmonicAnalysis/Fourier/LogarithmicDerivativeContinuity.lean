module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.NormSheetLogarithmicOperators
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.TraceSchwartzTensors

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory NumberField.InfinitePlace
variable {F : Type} [Field F] [NumberField F]

namespace DerivativeContinuityProof
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

local instance (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

 def mixedHomeo (F : Type) [Field F] [NumberField F] : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => IsReal v)
    (fun v => v.Completion)).trans
    ((Homeomorph.prodCongr
      (Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
      ((Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex))))))
 def coord (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    SLocalProduct F S ≃ₜ+ (mixedEmbedding.mixedSpace F × ((v : S) → v.val.adicCompletion F)) where
  toAddEquiv := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv).prodCongr (AddEquiv.refl _)
  continuous_toFun := ((mixedHomeo F).prodCongr (Homeomorph.refl _)).continuous
  continuous_invFun := ((mixedHomeo F).prodCongr (Homeomorph.refl _)).symm.continuous

private lemma archPhase_coordinates {F : Type} [Field F] [NumberField F]
    (x : InfiniteAdeleRing F) :
    ProbeAdditive.archPhase F x =
      (∏ v : {v : InfinitePlace F // v.IsReal},
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (2 * (InfiniteAdeleRing.ringEquiv_mixedSpace F x).1 v))) *
      ∏ v : {v : InfinitePlace F // v.IsComplex},
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (2 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 v).re)) := by
  unfold ProbeAdditive.archPhase
  rw [Finset.mul_sum, Complex.exp_sum]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : InfinitePlace F => v.IsReal)]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply v.2,
      Complex.ofReal_re, Complex.ofReal_mul, Complex.ofReal_ofNat]
  · apply Fintype.prod_equiv
      (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex))
    intro v
    rfl

private lemma local_schwartz_transforms
    (fR : SchwartzMap ℝ ℂ) (fC : SchwartzMap ℂ ℂ) :
    (∃ g : SchwartzMap ℝ ℂ, ∀ y,
      g y = ∫ x : ℝ, fR x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (2 * (-x * y)))) ∧
    (∃ g : SchwartzMap ℂ ℂ, ∀ y,
      g y = ∫ x : ℂ, fC x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (2 * (-x * y).re))) := by
  obtain ⟨gR, hgR⟩ := ArchSelfDual.realFourier_schwartz fR
  obtain ⟨gC, hgC⟩ := ArchSelfDual.complexTraceFourier_schwartz fC
  constructor
  · refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.smulOfNeZero ℝ ℝ 2 (by norm_num)).toContinuousLinearEquiv) gR, ?_⟩
    intro y
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      LinearEquiv.coe_toContinuousLinearEquiv, LinearEquiv.smulOfNeZero_apply, smul_eq_mul,
      hgR, ArchSelfDual.realFourier, ArchSelfDual.realMeasure]
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    change ((-2 * Real.pi * (x * (2 * y)) : ℝ) : ℂ) * Complex.I = _
    push_cast
    ring
  · refine ⟨(2 : ℂ)⁻¹ • gC, ?_⟩
    intro y
    simp only [SchwartzMap.smul_apply, hgC, ArchSelfDual.complexTraceFourier_eq_integral,
      ArchSelfDual.complexMeasure, integral_smul_measure, ENNReal.toReal_ofNat, smul_eq_mul]
    simp only [Complex.real_smul, Complex.ofReal_ofNat]
    rw [← mul_assoc]
    norm_num
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    ring

 def ContinuousSchwartzTensor (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (h : SLocalProduct F S → ℂ) : Prop :=
  ∃ (c : ℂ)
    (gReal : (v : {v : InfinitePlace F // v.IsReal}) → SchwartzMap ℝ ℂ)
    (gComplex : (v : {v : InfinitePlace F // v.IsComplex}) → SchwartzMap ℂ ℂ)
    (gFinite : (v : ↥S) → v.val.adicCompletion F → ℂ),
    (∀ v, Continuous (gFinite v)) ∧
    ∀ x, h x = c *
      ((∏ v, gReal v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 v)) *
       (∏ v, gComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
       ∏ v : ↥S, gFinite v (x.2 v))

private theorem fourier_tensor
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (μ : @Measure (SLocalProduct F S) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F S) _ _ (borel _) μ)
    (W : SLocalProduct F S → ℂ)
    (hW : ProbeWeight.IsAnnularTensor F S W)
    (hcompact : HasCompactSupport W) :
    ContinuousSchwartzTensor F S (ProbeWeight.fourier F S e μ W) := by
  classical
  letI : MeasurableSpace (SLocalProduct F S) := borel _
  letI : BorelSpace (SLocalProduct F S) := ⟨rfl⟩
  letI : μ.IsAddHaarMeasure := hμ
  obtain ⟨fR, fC, fF, hR, hC, hF, hW⟩ := hW
  let μf := fun v : S => Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F v.val)
  letI (v : S) : SigmaCompactSpace (v.val.adicCompletion F) :=
    PoissonFinite.BallExpansion.finite_completion_sigmaCompact F v.val
  letI (v : S) : SigmaFinite (μf v) := inferInstance
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : S) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : S) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  let νr := Measure.pi (fun _ : {v : InfinitePlace F // v.IsReal} => (volume : Measure ℝ))
  let νc := Measure.pi (fun _ : {v : InfinitePlace F // v.IsComplex} => (volume : Measure ℂ))
  let ν := (νr.prod νc).prod (Measure.pi μf)
  let E := coord F S
  let μ' := Measure.map E μ
  letI : μ'.IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  letI : ν.IsAddHaarMeasure := by dsimp [ν, νr, νc]; infer_instance
  have hμ' := Measure.isAddLeftInvariant_eq_smul μ' ν
  let a := μ'.addHaarScalarFactor ν
  have hr (v : {v : InfinitePlace F // v.IsReal}) :=
    (local_schwartz_transforms ((hR v).2.1.toSchwartzMap (hR v).1)
      (0 : SchwartzMap ℂ ℂ)).1
  have hc (v : {v : InfinitePlace F // v.IsComplex}) :=
    (local_schwartz_transforms (0 : SchwartzMap ℝ ℂ)
      ((hC v).2.1.toSchwartzMap (hC v).1)).2
  choose gR hgR using hr
  choose gC hgC using hc
  let gF := fun v : S => fun y => ∫ x, fF v x * (e v (-x * y) : ℂ) ∂μf v
  refine ⟨(a : ℂ), gR, gC, gF, ?_, ?_⟩
  · intro v
    change Continuous (fun y => ∫ x, fF v x * (e v (-x * y) : ℂ) ∂μf v)
    apply continuous_of_dominated (bound := fun x => ‖fF v x‖)
    · intro y
      exact ((hF v).1.continuous.mul
        (continuous_subtype_val.comp ((he v).comp
          (continuous_neg.mul continuous_const)))).aestronglyMeasurable
    · intro y
      exact Filter.Eventually.of_forall fun x => by simp [norm_mul]
    · exact ((hF v).1.continuous.integrable_of_hasCompactSupport (hF v).2.1).norm
    · exact Filter.Eventually.of_forall fun x =>
        continuous_const.mul (continuous_subtype_val.comp
          ((he v).comp (continuous_const.mul continuous_id)))
  · intro y
    have hmap := integral_map_equiv (μ := μ) E.toHomeomorph.toMeasurableEquiv
      (fun x => W (E.symm x) * ProbeAdditive.phase F S e (-E.symm x * y))
    have hi : ProbeWeight.fourier F S e μ W y =
        (a : ℂ) * ∫ x, W (E.symm x) * ProbeAdditive.phase F S e (-E.symm x * y) ∂ν := by
      unfold ProbeWeight.fourier
      have hmap' : (∫ x, W (E.symm x) * ProbeAdditive.phase F S e (-E.symm x * y) ∂μ') =
          ∫ x, W x * ProbeAdditive.phase F S e (-x * y) ∂μ := by
        change (∫ x, W (E.symm x) * ProbeAdditive.phase F S e (-E.symm x * y) ∂μ') =
          ∫ x, W (E.symm (E x)) * ProbeAdditive.phase F S e (-E.symm (E x) * y) ∂μ at hmap
        simpa only [ContinuousAddEquiv.symm_apply_apply] using hmap
      rw [← hmap', hμ']
      simp only [integral_smul_nnreal_measure, a, NNReal.smul_def, Complex.real_smul]
    rw [hi]
    congr 1
    have hfac (x : mixedEmbedding.mixedSpace F × ((v : S) → v.val.adicCompletion F)) :
        W (E.symm x) * ProbeAdditive.phase F S e (-E.symm x * y) =
        ((∏ v, fR v (x.1.1 v) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (2 * (-x.1.1 v * (E y).1.1 v)))) *
         (∏ v, fC v (x.1.2 v) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (2 * (-x.1.2 v * (E y).1.2 v).re)))) *
         ∏ v : S, fF v (x.2 v) * (e v (-x.2 v * y.2 v) : ℂ) := by
      rw [hW, ProbeAdditive.phase, archPhase_coordinates]
      have hx : InfiniteAdeleRing.ringEquiv_mixedSpace F (E.symm x).1 = x.1 := by
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x.1
      have hxy : InfiniteAdeleRing.ringEquiv_mixedSpace F (-E.symm x * y).1 =
          -x.1 * (E y).1 := by
        change InfiniteAdeleRing.ringEquiv_mixedSpace F (-(E.symm x).1 * y.1) = _
        rw [map_mul, map_neg, hx]
        rfl
      rw [hx, hxy]
      have hxf : (E.symm x).2 = x.2 := rfl
      simp only [hxf, Prod.fst_mul, Prod.snd_mul, Prod.fst_neg, Prod.snd_neg,
        Pi.mul_apply, Pi.neg_apply, Finset.prod_mul_distrib,
        Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    let kR := fun v (t : ℝ) => fR v t * Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (2 * (-t * (E y).1.1 v)))
    let kC := fun v (t : ℂ) => fC v t * Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (2 * (-t * (E y).1.2 v).re))
    let kF := fun v (t : v.val.adicCompletion F) => fF v t * (e v (-t * y.2 v) : ℂ)
    have hh : (∫ x, W (E.symm x) * ProbeAdditive.phase F S e (-E.symm x * y) ∂ν) =
        (∫ x, ((∏ v, kR v (x.1.1 v)) * ∏ v, kC v (x.1.2 v)) *
          ∏ v, kF v (x.2 v) ∂ν) := integral_congr_ae (Filter.Eventually.of_forall hfac)
    rw [hh]
    have hp := integral_prod_mul (μ := νr.prod νc) (ν := Measure.pi μf)
      (fun x => (∏ v, kR v (x.1 v)) * ∏ v, kC v (x.2 v))
      (fun x => ∏ v, kF v (x v))
    change (∫ x, ((∏ v, kR v (x.1.1 v)) * ∏ v, kC v (x.1.2 v)) *
        ∏ v, kF v (x.2 v) ∂(νr.prod νc).prod (Measure.pi μf)) = _
    rw [hp]
    have hp' := integral_prod_mul (μ := νr) (ν := νc)
      (fun x => ∏ v, kR v (x v)) (fun x => ∏ v, kC v (x v))
    rw [hp']
    have hpR := integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℝ)) kR
    have hpC := integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℂ)) kC
    have hpF := integral_fintype_prod_eq_prod (μ := μf) kF
    rw [hpR, hpC, hpF]
    simp only [hgR, hgC, gF, kR, kC, kF]
    rfl
 def complexEuler (g : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (1 / 2 : ℝ) • SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.apply (E := ℂ) ℝ ℂ).flip
    (Function.HasTemperateGrowth.id') (SchwartzMap.fderivCLM ℝ ℂ ℂ g)

@[simp] private theorem complexEuler_apply (g : SchwartzMap ℂ ℂ) (z : ℂ) :
    complexEuler g z = (1 / 2 : ℝ) • fderiv ℝ g z z := rfl

private theorem hasDerivAt_complexNormFlow (g : SchwartzMap ℂ ℂ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z))
      (complexEuler g ((Real.exp (u / 2) : ℂ) * z)) u := by
  have h : HasDerivAt (fun v : ℝ => Real.exp (v / 2))
      (Real.exp (u / 2) / 2) u :=
    by simpa [div_eq_mul_inv] using ((hasDerivAt_id u).div_const 2).exp
  have hc := h.ofReal_comp.mul_const z
  have hd := g.differentiableAt.hasFDerivAt.comp_hasDerivAt u hc
  convert hd using 1
  · rfl
  · rw [complexEuler_apply, ← map_smul]
    congr 1
    simp [smul_eq_mul]
    ring

private theorem iteratedDeriv_complexNormFlow (g : SchwartzMap ℂ ℂ) (k : ℕ) (z : ℂ) (u : ℝ) :
    iteratedDeriv k (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z)) u =
      ((complexEuler^[k]) g) ((Real.exp (u / 2) : ℂ) * z) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hf : iteratedDeriv k (fun v : ℝ => g ((Real.exp (v / 2) : ℂ) * z)) =
        fun v : ℝ => ((complexEuler^[k]) g) ((Real.exp (v / 2) : ℂ) * z) := funext ih
    rw [hf, (hasDerivAt_complexNormFlow ((complexEuler^[k]) g) z u).deriv,
      Function.iterate_succ_apply']
private theorem mixed_flow_complex (A : SArithmeticData F) (w : InfinitePlace F)
    (u : ℝ) (x : SLocalProduct F A.Sf) (v : {v : InfinitePlace F // v.IsComplex}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (complexNormFlowRaw A w u x).1).2 v =
      if v.val = w then (Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v
      else (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v := by
  change InfinitePlace.Completion.extensionEmbedding v.val
      (Function.update x.1 w
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
          (Real.exp (u / 2) : ℂ) * x.1 w) v.val) = _
  by_cases hv : v.val = w
  · subst w
    simp only [Function.update_self, ↓reduceIte]
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v.val))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v.val)).symm
        (Real.exp (u / 2) : ℂ) * x.1 v.val) = _
    rw [map_mul, RingEquiv.apply_symm_apply]
    rfl
  · rw [Function.update_of_ne hv, if_neg hv]
    rfl

private theorem real_places_empty (A : SArithmeticData F) :
    IsEmpty {v : InfinitePlace F // v.IsReal} :=
  ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place v.val)) v.property⟩

private theorem tensor_flow_factor (A : SArithmeticData F) (w : InfinitePlace F)
    (g : (v : {v : InfinitePlace F // v.IsComplex}) → SchwartzMap ℂ ℂ)
    (u : ℝ) (x : SLocalProduct F A.Sf) :
    (∏ v, g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F (complexNormFlowRaw A w u x).1).2 v)) =
      g ⟨w, A.complex_place w⟩ ((Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 ⟨w, A.complex_place w⟩) *
      ∏ v ∈ Finset.univ.erase ⟨w, A.complex_place w⟩,
        g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨w, A.complex_place w⟩)]
  congr 1
  · rw [mixed_flow_complex]; simp
  · apply Finset.prod_congr rfl
    intro v hv
    have hne : v.val ≠ w := by
      intro h
      exact (Finset.mem_erase.mp hv).1 (Subtype.ext h)
    rw [mixed_flow_complex, if_neg hne]

 private theorem derivative_tensor (A : SArithmeticData F) (w : InfinitePlace F)
    (k : ℕ) (f : SLocalProduct F A.Sf → ℂ)
    (hf : ContinuousSchwartzTensor F A.Sf f) :
    ContinuousSchwartzTensor F A.Sf (logDerivativeRaw A w k f) := by
  obtain ⟨c, gr, gc, gf, hgf, hf⟩ := hf
  letI := real_places_empty A
  let v₀ : {v : InfinitePlace F // v.IsComplex} := ⟨w, A.complex_place w⟩
  let gc' := Function.update gc v₀ ((complexEuler^[k]) (gc v₀))
  refine ⟨c, gr, gc', gf, hgf, ?_⟩
  intro x
  have hflow : (fun u => f (complexNormFlowRaw A w u x)) =
      fun u => c * (gc v₀ ((Real.exp (u / 2) : ℂ) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v₀) *
        ∏ v ∈ Finset.univ.erase v₀,
          gc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
        ∏ v : ↥A.Sf, gf v (x.2 v) := by
    funext u
    rw [hf, tensor_flow_factor]
    simp [complexNormFlowRaw, v₀, mul_assoc]
  unfold logDerivativeRaw
  rw [hflow]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field,
    iteratedDeriv_complexNormFlow, zero_div, Real.exp_zero, Complex.ofReal_one, one_mul]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  have hp : (∏ v, gc' v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) =
      ((complexEuler^[k]) (gc v₀)) ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v₀) *
      ∏ v ∈ Finset.univ.erase v₀, gc v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀)]
    simp only [gc', Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Function.update_of_ne (Finset.mem_erase.mp hv).1]
  rw [hp]
  ring

private theorem tensor_continuous (A : SArithmeticData F)
    (f : SLocalProduct F A.Sf → ℂ) (hf : ContinuousSchwartzTensor F A.Sf f) :
    Continuous f := by
  obtain ⟨c, gr, gc, gf, hgf, hf⟩ := hf
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
  rw [show f = _ from funext hf]
  apply Continuous.mul continuous_const
  apply Continuous.mul
  · apply Continuous.mul
    · apply continuous_finset_prod
      intro v hv
      exact (gr v).continuous.comp
        ((continuous_apply v).comp (continuous_fst.comp (hm.comp continuous_fst)))
    · apply continuous_finset_prod
      intro v hv
      exact (gc v).continuous.comp
        ((continuous_apply v).comp (continuous_snd.comp (hm.comp continuous_fst)))
  · apply continuous_finset_prod
    intro v hv
    exact (hgf v).comp ((continuous_apply v).comp continuous_snd)

end DerivativeContinuityProof

theorem raw_fourier_log_derivative_continuous
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (w : InfinitePlace F) (k : ℕ)
    (W0 : SLocalProduct F A.Sf → ℂ)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) :
    Continuous (logDerivativeRaw A w k (ProbeWeight.fourier F A.Sf e μ W0)) := by
  exact DerivativeContinuityProof.tensor_continuous A _
    (DerivativeContinuityProof.derivative_tensor A w k _
      (DerivativeContinuityProof.fourier_tensor A.Sf e he μ hμ W0 hW0 hcompact))

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
