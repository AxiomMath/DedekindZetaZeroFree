module

public import DedekindZetaZeroFree.Moments.Probes.AnnularWeightsAndCancellingProfiles
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.ArchimedeanTraceInversion

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetVerticalDecay
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory NumberField.InfinitePlace

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 512

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

private theorem unique_fourier (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) [Unique S]
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, ∃ x, e v x ≠ 1)
    (φ : (default : S).val.adicCompletion F → ℂ) (hlocal : IsLocallyConstant φ)
    (hsupport : HasCompactSupport φ) :
    IsLocallyConstant (fun y => ∫ x, φ x * (e default (-x*y) : ℂ) ∂μ default) ∧
    HasCompactSupport (fun y => ∫ x, φ x * (e default (-x*y) : ℂ) ∂μ default) := by
  let h : PoissonFinite.Space F S ≃ₜ (default : S).val.adicCompletion F := Homeomorph.piUnique _
  let Φ : PoissonFinite.Space F S → ℂ := φ ∘ h
  have hΦlocal : IsLocallyConstant Φ := hlocal.comp_continuous h.continuous
  have hΦsupport : HasCompactSupport Φ := hsupport.comp_homeomorph h
  obtain ⟨U, hoU, hpU⟩ := PoissonFinite.BallExpansion.exists_open_phase_annihilator F S e he
    (tsupport Φ) hΦsupport.isCompact
  have hf := PoissonFinite.fourierIntegral_isLocallyConstant_of_open_phase F S e μ Φ U hoU
    (fun u hu x hx => hpU u hu x (subset_tsupport Φ hx))
  obtain ⟨V, hoV, hpV⟩ := PoissonFinite.BallExpansion.exists_open_period_subgroup F S Φ hΦlocal hΦsupport
  letI : ∀ v : S, SigmaCompactSpace (v.val.adicCompletion F) :=
    fun v => PoissonFinite.BallExpansion.finite_completion_sigmaCompact F v.val
  have hg := PoissonFinite.fourierIntegral_hasCompactSupport_of_period F S e μ Φ V hpV
    (PoissonFinite.BallExpansion.isCompact_phase_annihilator F S e he hne V hoV)
  have heq : (PoissonFinite.fourierIntegral F S e μ Φ) ∘ h.symm =
      (fun y => ∫ x, φ x * (e default (-x*y) : ℂ) ∂μ default) := by
    funext y
    unfold PoissonFinite.fourierIntegral
    simp only [Function.comp_apply, Fintype.prod_unique]
    exact (measurePreserving_piUnique μ).integral_comp
      (MeasurableEquiv.piUnique _).measurableEmbedding
      (fun x => φ x * (e default (-x*y) : ℂ))
  rw [← heq]
  exact ⟨hf.comp_continuous h.symm.continuous, hg.comp_homeomorph h.symm⟩
private theorem local_fourier (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : AddChar (v.adicCompletion F) Circle)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (he : Continuous e) (hne : ∃ x, e x ≠ 1)
    (φ : v.adicCompletion F → ℂ) (hlocal : IsLocallyConstant φ)
    (hsupport : HasCompactSupport φ) :
    IsLocallyConstant (fun y => ∫ x, φ x * (e (-x*y) : ℂ) ∂μ) ∧
    HasCompactSupport (fun y => ∫ x, φ x * (e (-x*y) : ℂ) ∂μ) := by
  let S : Finset (HeightOneSpectrum (RingOfIntegers F)) := {v}
  letI : Unique S := ⟨⟨⟨v, Finset.mem_singleton_self v⟩⟩,
    fun w => Subtype.ext (Finset.mem_singleton.mp w.property)⟩
  have hw (w : S) : w.val = v := Finset.mem_singleton.mp w.property
  let e' : (w : S) → AddChar (w.val.adicCompletion F) Circle :=
    fun w => (hw w) ▸ e
  let μ' : (w : S) → Measure (w.val.adicCompletion F) :=
    fun w => (hw w) ▸ μ
  let φ' : (default : S).val.adicCompletion F → ℂ := (hw default) ▸ φ
  letI (w : S) : (μ' w).IsAddHaarMeasure := by
    rcases w with ⟨w, hwm⟩
    have h : w = v := Finset.mem_singleton.mp hwm
    subst w
    exact inferInstance
  have he' (w : S) : Continuous (e' w) := by
    rcases w with ⟨w, hwm⟩
    have h : w = v := Finset.mem_singleton.mp hwm
    subst w
    exact he
  have hne' (w : S) : ∃ x, e' w x ≠ 1 := by
    rcases w with ⟨w, hwm⟩
    have h : w = v := Finset.mem_singleton.mp hwm
    subst w
    exact hne
  have hl : IsLocallyConstant φ' := by dsimp [φ']; cases hw default; exact hlocal
  have hs : HasCompactSupport φ' := by dsimp [φ']; cases hw default; exact hsupport
  have h := unique_fourier F S e' μ' he' hne' φ' hl hs
  have hv : (default : S).val = v := rfl
  change IsLocallyConstant (fun y : v.adicCompletion F =>
    ∫ x, φ x * (e (-x*y) : ℂ) ∂μ) ∧
    HasCompactSupport (fun y : v.adicCompletion F =>
    ∫ x, φ x * (e (-x*y) : ℂ) ∂μ)
  at h
  exact h

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

def IsSchwartzTensor (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (h : SLocalProduct F S → ℂ) : Prop :=
  ∃ (c : ℂ)
    (gReal : (v : {v : InfinitePlace F // v.IsReal}) → SchwartzMap ℝ ℂ)
    (gComplex : (v : {v : InfinitePlace F // v.IsComplex}) → SchwartzMap ℂ ℂ)
    (gFinite : (v : ↥S) → v.val.adicCompletion F → ℂ),
    (∀ v, IsLocallyConstant (gFinite v) ∧ HasCompactSupport (gFinite v)) ∧
    ∀ x, h x = c *
      ((∏ v, gReal v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).1 v)) *
       (∏ v, gComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x.1).2 v)) *
       ∏ v : ↥S, gFinite v (x.2 v))

theorem fourier_isSchwartzTensor
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F S) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F S) _ _ (borel _) μ)
    (W : SLocalProduct F S → ℂ)
    (hW : ProbeWeight.IsAnnularTensor F S W)
    (hcompact : HasCompactSupport W) :
    IsSchwartzTensor F S (ProbeWeight.fourier F S e μ W) := by
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
    exact local_fourier F v.val (e v) (μf v) (he v)
      (AddChar.ne_one_iff.mp (hne v)) (fF v) (hF v).1 (hF v).2.1
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

end
end DedekindZetaZeroFree.ProbeSheetVerticalDecay
