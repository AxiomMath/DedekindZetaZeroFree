module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegerTensorCosets
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.NonarchimedeanWhittakerBounds

@[expose] public section

section

noncomputable section
open scoped Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.ScaleShift

private theorem scalarAction_eq (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (a : Fˣ) (x : Space F S) :
    scalarAction F S (a : F) x = Covolume.fieldDilation F S a x := by
  apply Prod.ext
  · apply (mixedEmbedding.euclidean.toMixed F).injective
    simp only [scalarAction, Covolume.fieldDilation, PoissonArch.fieldMul,
      PoissonArch.infiniteAdeleToSpace_coordinates, map_mul,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [← PoissonArch.infiniteAdeleToSpace_coordinates]
    simp
  · rfl
private theorem dilation_lattice (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (a : Fˣ) (c : F) :
    (lattice F S c).map (Covolume.fieldDilation F S a).toAddEquiv.toAddMonoidHom =
      lattice F S ((a : F) * c) := by
  change (Covolume.lattice F S c).map
      (Covolume.fieldDilation F S a).toAddEquiv.toAddMonoidHom =
    Covolume.lattice F S ((a : F) * c)
  unfold Covolume.lattice
  rw [AddSubgroup.map_map]
  congr 1
  apply AddMonoidHom.ext
  intro x
  change Covolume.fieldDilation F S a
      (Covolume.diagonalHom F S (c * x)) =
    Covolume.diagonalHom F S (((a : F) * c) * x)
  rw [Covolume.fieldDilation_diagonal]
  rw [mul_assoc]

theorem tsum_scalar_lattice
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : Fˣ) (c : F) (f : Space F S → ℂ) :
    (∑' m : lattice F S c, f (scalarAction F S (a : F) m)) =
      ∑' m : lattice F S ((a : F) * c), f m := by
  let e := ((Covolume.fieldDilation F S a).toAddEquiv.addSubgroupMap
    (lattice F S c)).trans (AddEquiv.addSubgroupCongr (dilation_lattice F S a c))
  calc
    _ = ∑' m : lattice F S c, f (e m) := by
      congr 1
      funext m
      congr 1
      change scalarAction F S (a : F) (m : Space F S) = (e m : Space F S)
      rw [scalarAction_eq]
      rfl
    _ = _ := e.toEquiv.tsum_eq (fun m : lattice F S ((a : F) * c) => f m)

end DedekindZetaZeroFree.PoissonS.ScaleShift

end

end

section

noncomputable section
open scoped Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.ScaleShift

attribute [local instance] completionMeasurable completionBorel

 def archEquiv (F : Type) [Field F] [NumberField F] (a : Fˣ) :
    PoissonArch.Space F ≃L[ℝ] PoissonArch.Space F :=
  ((NumberField.mixedEmbedding.euclidean.toMixed F).trans
    ((ContinuousLinearEquiv.piCongrRight fun v : {v : NumberField.InfinitePlace F // v.IsReal} =>
      ContinuousLinearEquiv.unitsEquivAut ℝ (a.map (v.val.embedding_of_isReal v.prop))).prodCongr
      (ContinuousLinearEquiv.piCongrRight fun v : {v : NumberField.InfinitePlace F // v.IsComplex} =>
        (ContinuousLinearEquiv.unitsEquivAut ℂ (a.map v.val.embedding)).restrictScalars ℝ))).trans
    (NumberField.mixedEmbedding.euclidean.toMixed F).symm

private theorem archEquiv_apply (F : Type) [Field F] [NumberField F] (a : Fˣ)
    (x : PoissonArch.Space F) : archEquiv F a x = PoissonArch.fieldMul F (a : F) x := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
  simp only [archEquiv, PoissonArch.fieldMul, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply]
  ext v <;> simp [ContinuousLinearEquiv.piCongrRight_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]

 def localEquiv (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (a : Fˣ) :
    v.adicCompletion F ≃ₜ v.adicCompletion F where
  toFun x := algebraMap F (v.adicCompletion F) (a : F) * x
  invFun x := algebraMap F (v.adicCompletion F) ((a⁻¹ : Fˣ) : F) * x
  left_inv x := by simp [← mul_assoc, ← map_mul]
  right_inv x := by simp [← mul_assoc, ← map_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

private theorem local_fourier_scale (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : AddChar (v.adicCompletion F) Circle)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (φ : v.adicCompletion F → ℂ) (a : Fˣ) (y : v.adicCompletion F) :
    (∫ x, φ (algebraMap F (v.adicCompletion F) (a : F) * x) *
      (e (-x * y) : ℂ) ∂μ) =
    ((FinitePlace.mk v (a : F))⁻¹ : ℂ) *
      (∫ x, φ x * (e (-x * (algebraMap F (v.adicCompletion F)
        ((a⁻¹ : Fˣ) : F) * y)) : ℂ) ∂μ) := by
  let c : (v.adicCompletion F)ˣ := a.map (algebraMap F (v.adicCompletion F))
  have hm := CompletionHaarModule.map_mul F v μ c
  have hn : ‖(c : v.adicCompletion F)‖ = FinitePlace.mk v (a : F) := by
    change ‖FinitePlace.embedding v (a : F)‖ = _
    rw [FinitePlace.mk_apply]
  have hc : 0 < FinitePlace.mk v (a : F) :=
    FinitePlace.pos_iff.mpr a.ne_zero
  have hi := integral_map_equiv (μ := μ) (localEquiv F v a).toMeasurableEquiv
    (fun x => φ x * (e (-x * (algebraMap F (v.adicCompletion F)
      ((a⁻¹ : Fˣ) : F) * y)) : ℂ))
  have hmap : Measure.map (localEquiv F v a) μ =
      ENNReal.ofReal ((FinitePlace.mk v (a : F))⁻¹) • μ := by
    change Measure.map (fun x => (c : v.adicCompletion F) * x) μ = _
    rw [hm, hn, ENNReal.ofReal_inv_of_pos hc]
  rw [(localEquiv F v a).toMeasurableEquiv_coe, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le)] at hi
  have hp (x : v.adicCompletion F) :
      -(algebraMap F (v.adicCompletion F) (a : F) * x) *
        (algebraMap F (v.adicCompletion F) ((a⁻¹ : Fˣ) : F) * y) = -x * y := by
    calc
      _ = -(algebraMap F (v.adicCompletion F) (a : F) *
        algebraMap F (v.adicCompletion F) ((a⁻¹ : Fˣ) : F)) * (x * y) := by ring
      _ = -x * y := by simp [← map_mul]
  change _ = ∫ x, φ (algebraMap F (v.adicCompletion F) (a : F) * x) *
    (e (-(algebraMap F (v.adicCompletion F) (a : F) * x) *
      (algebraMap F (v.adicCompletion F) ((a⁻¹ : Fˣ) : F) * y)) : ℂ) ∂μ at hi
  simpa only [hp, Complex.real_smul, Complex.ofReal_inv] using hi.symm

theorem scalarAction_fst
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : Fˣ) (x : Space F S) :
    (scalarAction F S (a : F) x).1 = PoissonArch.fieldMul F (a : F) x.1 := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
  rw [PoissonArch.fieldMul, ContinuousLinearEquiv.apply_symm_apply]
  show NumberField.mixedEmbedding.euclidean.toMixed F
      (PoissonArch.infiniteAdeleToSpace F (algebraMap F (InfiniteAdeleRing F) (a : F) *
        (PoissonArch.infiniteAdeleToSpace F).symm x.1)) = _
  rw [PoissonArch.infiniteAdeleToSpace_coordinates, map_mul,
    ← NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have hx := PoissonArch.infiniteAdeleToSpace_coordinates F
    ((PoissonArch.infiniteAdeleToSpace F).symm x.1)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hx
  rw [← hx]

theorem scalar_pullback_tensor
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) (a : Fˣ) :
    ∃ (gArch : 𝓢(PoissonArch.Space F, ℂ))
      (ψ : (v : S) → v.val.adicCompletion F → ℂ),
      (∀ v, IsLocallyConstant (ψ v)) ∧ (∀ v, HasCompactSupport (ψ v)) ∧
      (∀ x, tensorFunction F S gArch ψ x =
        tensorFunction F S fArch φ (scalarAction F S (a : F) x)) ∧
      (∀ y, fourierIntegral F S e μ (tensorFunction F S gArch ψ) y =
        ((productModule F S (a : F))⁻¹ : ℂ) *
          fourierIntegral F S e μ (tensorFunction F S fArch φ)
            (scalarAction F S ((a⁻¹ : Fˣ) : F) y)) := by
  let gArch := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv F a) fArch
  let ψ : (v : S) → v.val.adicCompletion F → ℂ := fun v => φ v ∘ localEquiv F v.val a
  have hl (v : S) : IsLocallyConstant (ψ v) :=
    (hlocal v).comp_continuous (localEquiv F v.val a).continuous
  have hs (v : S) : HasCompactSupport (ψ v) :=
    (hsupport v).comp_homeomorph (localEquiv F v.val a)
  have hg (x : PoissonArch.Space F) : gArch x = fArch (PoissonArch.fieldMul F (a : F) x) := by
    simp [gArch, archEquiv_apply]
  refine ⟨gArch, ψ, hl, hs, ?_, ?_⟩
  · intro x
    simp only [tensorFunction, hg, scalarAction_fst]
    rfl
  · intro y
    rw [fourierIntegral_tensorFunction F S e μ he gArch ψ hl hs,
      fourierIntegral_tensorFunction F S e μ he fArch φ hlocal hsupport]
    have ht : PoissonArch.traceFourier F gArch y.1 =
        ((PoissonArch.fieldModule F (a : F))⁻¹ : ℂ) *
        PoissonArch.traceFourier F fArch
          (PoissonArch.fieldMul F ((a⁻¹ : Fˣ) : F) y.1) := by
      simpa only [show (gArch : PoissonArch.Space F → ℂ) =
        (fun x => fArch (PoissonArch.fieldMul F (a : F) x)) from funext hg] using
        PoissonArch.traceFourier_field_scale F fArch a y.1
    rw [ht, scalarAction_fst]
    have hf (v : S) : (∫ x, ψ v x * (e v (-x * y.2 v) : ℂ) ∂μ v) =
        ((FinitePlace.mk v.val (a : F))⁻¹ : ℂ) *
        (∫ x, φ v x * (e v (-x * (scalarAction F S ((a⁻¹ : Fˣ) : F) y).2 v) : ℂ) ∂μ v) :=
      local_fourier_scale F v.val (e v) (μ v) (φ v) a (y.2 v)
    simp_rw [hf]
    rw [Finset.prod_mul_distrib]
    have hmodule : ((productModule F S (a : F))⁻¹ : ℂ) =
        ((PoissonArch.fieldModule F (a : F))⁻¹ : ℂ) *
          ∏ v : S, ((FinitePlace.mk v.val (a : F))⁻¹ : ℂ) := by
      simp only [productModule, ← Covolume.DilationArch.fieldModule_eq F,
        mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
        ← Finset.prod_inv_distrib, ← Complex.ofReal_prod,
        Finset.prod_coe_sort]
      rw [← Finset.prod_coe_sort S (fun v => FinitePlace.mk v (a : F)),
        Complex.ofReal_prod, Finset.prod_inv_distrib]
    rw [hmodule]
    ring

end DedekindZetaZeroFree.PoissonS.ScaleShift

end

end

section

noncomputable section
open scoped Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.PoissonS

local instance scaleCompletionMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance scaleCompletionBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def localProductToSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    SLocalProduct F S ≃+ Space F S :=
  (PoissonArch.infiniteAdeleToSpace F).toAddEquiv.prodCongr (AddEquiv.refl _)

def localDilation (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (d : (SLocalProduct F S)ˣ) (x : Space F S) : Space F S :=
  localProductToSpace F S ((d : SLocalProduct F S) * (localProductToSpace F S).symm x)

def localDilationModule (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (d : (SLocalProduct F S)ˣ) : ℝ :=
  ‖(d : SLocalProduct F S).1‖ * ∏ v : S, ‖(d : SLocalProduct F S).2 v‖

def tracePhase (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y : Space F S) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
    ∏ v : S, (e v (x.2 v * y.2 v) : ℂ)

theorem finite_components_locallyCompact
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    (∀ v : S, LocallyCompactSpace (v.val.adicCompletion F)) ∧
      LocallyCompactSpace (PoissonFinite.Space F S) := by
  have hv (v : S) : LocallyCompactSpace (v.val.adicCompletion F) := by
    letI : LocallyCompactSpace (NumberField.HeightOneSpectrum.adicAbv F v.val).Completion :=
      AbsoluteValue.Completion.locallyCompactSpace
        (finitePlaceCompletionBaseMap_isometry v.val)
    exact (finitePlaceCompletionContinuousMulEquiv v.val).toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  letI : ∀ v : S, LocallyCompactSpace (v.val.adicCompletion F) := hv
  exact ⟨hv, inferInstance⟩

private lemma char_local {K : Type*} [NormedField K] [IsUltrametricDist K]
    (e : AddChar K Circle) (he : Continuous e) : IsLocallyConstant e := by
  obtain ⟨r, hr, h⟩ := KPFiniteLocal.character_trivial_near_zero e he
  apply (IsLocallyConstant.iff_eventually_eq e).mpr
  intro x
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  have hyx : e (y-x) = 1 := h _ (by simpa [Metric.mem_ball, dist_eq_norm] using hy)
  have hz := e.map_add_eq_mul (y-x) x
  simpa [hyx] using hz

theorem tensorFunction_shift_modulation_bruhatSchwartz
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) (t b : Space F S) :
    ∃ (gArch : 𝓢(PoissonArch.Space F, ℂ))
      (ψ : (v : S) → v.val.adicCompletion F → ℂ),
      (∀ v, IsLocallyConstant (ψ v)) ∧ (∀ v, HasCompactSupport (ψ v)) ∧
      ∀ x, tensorFunction F S gArch ψ x =
        tensorFunction F S fArch φ (x + t) * tracePhase F S e b x := by
  let p : PoissonArch.Space F → ℂ := fun x => Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (PoissonArch.tracePairing F b.1 x : ℂ))
  have hp : p.HasTemperateGrowth := by
    have hp' : (fun x : PoissonArch.Space F => Complex.exp
        (((2 * Real.pi * inner ℝ b.1 (PoissonArch.traceAdapter F x) : ℝ) : ℂ) * Complex.I)).HasTemperateGrowth := by
      apply Complex.hasTemperateGrowth_exp_mul_I.comp
      exact (Function.HasTemperateGrowth.const (2 * Real.pi)).mul
        ((Function.hasTemperateGrowth_inner_right b.1).comp
          (PoissonArch.traceAdapter F).hasTemperateGrowth)
    convert hp' using 1
    funext x
    simp only [p, PoissonArch.tracePairing_eq_inner, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    ring
  let gArch := SchwartzMap.smulLeftCLM ℂ p (fArch.compSubConstCLM ℂ (-t.1))
  let ψ := fun (v : S) x => φ v (x+t.2 v) * (e v (b.2 v*x) : ℂ)
  refine ⟨gArch, ψ, ?_, ?_, ?_⟩
  · intro v
    apply IsLocallyConstant.mul
    · exact (hlocal v).comp_continuous (continuous_id.add continuous_const)
    · exact ((char_local (e v) (he v)).comp_continuous
        (continuous_const.mul continuous_id)).comp (fun z : Circle => (z : ℂ))
  · intro v
    exact ((hsupport v).comp_homeomorph (Homeomorph.addRight (t.2 v))).mul_right
  · intro x
    simp only [tensorFunction, gArch, SchwartzMap.smulLeftCLM_apply_apply hp,
      SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul,
      ψ, tracePhase, p, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.prod_mul_distrib]
    ring

private lemma phase_symm (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y : Space F S) : tracePhase F S e x y = tracePhase F S e y x := by
  have hp : PoissonArch.tracePairing F x.1 y.1 =
      PoissonArch.tracePairing F y.1 x.1 := by
    simp only [PoissonArch.tracePairing]
    congr 1
    · apply Finset.sum_congr rfl
      intro v hv
      rw [mul_comm]
    · congr 1
      apply Finset.sum_congr rfl
      intro v hv
      rw [mul_comm]
  unfold tracePhase
  rw [hp]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  rw [mul_comm]
private lemma phase_add_left (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y z : Space F S) :
    tracePhase F S e (x + y) z = tracePhase F S e x z * tracePhase F S e y z := by
  unfold tracePhase
  have hp : PoissonArch.tracePairing F (x.1 + y.1) z.1 =
      PoissonArch.tracePairing F x.1 z.1 + PoissonArch.tracePairing F y.1 z.1 := by
    simp [PoissonArch.tracePairing_eq_inner, inner_add_left]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [hp, Complex.ofReal_add]
  have heq : (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      (↑(PoissonArch.tracePairing F x.1 z.1) + ↑(PoissonArch.tracePairing F y.1 z.1)) =
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ↑(PoissonArch.tracePairing F x.1 z.1) +
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ↑(PoissonArch.tracePairing F y.1 z.1) := by ring
  rw [heq, Complex.exp_add]
  have hf : (∏ v : S, (e v ((x.2 v + y.2 v) * z.2 v) : ℂ)) =
      (∏ v : S, (e v (x.2 v * z.2 v) : ℂ)) *
      (∏ v : S, (e v (y.2 v * z.2 v) : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    rw [add_mul, (e v).map_add_eq_mul, Circle.coe_mul]
  rw [hf]
  ring
private lemma phase_neg_left (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y : Space F S) : tracePhase F S e (-x) y = (tracePhase F S e x y)⁻¹ := by
  unfold tracePhase
  simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply,
    PoissonArch.tracePairing_eq_inner, inner_neg_left, Complex.ofReal_neg, mul_neg,
    Complex.exp_neg, neg_mul, (e _).map_neg_eq_inv, Circle.coe_inv]
  rw [Finset.prod_inv_distrib, mul_inv]
private lemma phase_zero_left (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (y : Space F S) : tracePhase F S e 0 y = 1 := by
  simp [tracePhase, PoissonArch.tracePairing_eq_inner, AddChar.map_zero_eq_one]
private lemma phase_unit (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y : Space F S) : tracePhase F S e x y * tracePhase F S e (-x) y = 1 := by
  rw [← phase_add_left, add_neg_cancel, phase_zero_left]
private lemma phase_add_right (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y z : Space F S) :
    tracePhase F S e x (y + z) = tracePhase F S e x y * tracePhase F S e x z := by
  rw [phase_symm, phase_add_left, phase_symm F S e y x, phase_symm F S e z x]
private lemma integrand_phase_shift (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x t b y : Space F S) :
    tracePhase F S e b x * tracePhase F S e (-x) y =
      tracePhase F S e (y-b) t * tracePhase F S e (-(x+t)) (y-b) := by
  have hn (z w : Space F S) : tracePhase F S e z (-w) = tracePhase F S e (-z) w := by
    rw [phase_symm, phase_neg_left, phase_symm F S e w z, phase_neg_left]
  have hz : tracePhase F S e (-t) (y-b) * tracePhase F S e (y-b) t = 1 := by
    rw [phase_symm F S e (y-b) t, mul_comm]
    exact phase_unit F S e t (y-b)
  rw [neg_add, phase_add_left]
  rw [show tracePhase F S e (y-b) t *
      (tracePhase F S e (-x) (y-b) * tracePhase F S e (-t) (y-b)) =
      tracePhase F S e (-x) (y-b) *
      (tracePhase F S e (-t) (y-b) * tracePhase F S e (y-b) t) by ring, hz, mul_one]
  rw [sub_eq_add_neg, phase_add_right, hn, neg_neg, phase_symm F S e b x]
  ring

theorem fourierIntegral_shift_modulation
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) (t b y : Space F S) :
    fourierIntegral F S e μ
      (fun x => tensorFunction F S fArch φ (x + t) * tracePhase F S e b x) y =
      tracePhase F S e (y - b) t *
        fourierIntegral F S e μ (tensorFunction F S fArch φ) (y - b) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : S) : LocallyCompactSpace (v.val.adicCompletion F) := (finite_components_locallyCompact F S).1 v
  letI (v : S) : SeparableSpace (v.val.adicCompletion F) := SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : S) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  letI (v : S) : SigmaFinite (μ v) := inferInstance
  haveI : (PoissonArch.traceMeasure F).IsAddLeftInvariant := by
    unfold PoissonArch.traceMeasure
    infer_instance
  haveI : SFinite (PoissonArch.traceMeasure F) := by
    unfold PoissonArch.traceMeasure
    infer_instance
  haveI : (Measure.pi μ).IsAddLeftInvariant := inferInstance
  haveI : (productMeasure F S μ).IsAddLeftInvariant := by
    unfold productMeasure
    infer_instance
  have hFourier (f : Space F S → ℂ) (z : Space F S) :
      fourierIntegral F S e μ f z = ∫ x, f x * tracePhase F S e (-x) z ∂productMeasure F S μ := by
    unfold fourierIntegral tracePhase
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, PoissonArch.tracePairing_eq_inner,
      inner_neg_left, Complex.ofReal_neg]
    rw [← mul_assoc]
    congr 2
    congr 1
    ring
  rw [hFourier, hFourier, ← integral_const_mul]
  calc
    _ = ∫ x, tracePhase F S e (y-b) t *
        (tensorFunction F S fArch φ (x+t) * tracePhase F S e (-(x+t)) (y-b))
        ∂productMeasure F S μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mul_assoc, integrand_phase_shift F S e x t b y]
      ring
    _ = ∫ x, tracePhase F S e (y-b) t *
        (tensorFunction F S fArch φ x * tracePhase F S e (-x) (y-b))
        ∂productMeasure F S μ := integral_add_right_eq_self
          (μ := productMeasure F S μ)
          (fun x => tracePhase F S e (y-b) t *
            (tensorFunction F S fArch φ x * tracePhase F S e (-x) (y-b))) t

theorem poisson_scale_shift
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (hS : ContainsDifferent F S)
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v))
    (hconductor : TraceConductor F S e)
    (hnorm : LocalNormalization F S μ)
    (hdiagonal : ∀ r : sIntegerRing F S,
      tracePhase F S e (diagonalHom F S (r : F)) (diagonalHom F S 1) = 1)
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v))
    (a : Fˣ) (t b : Space F S) :
    (∑' m : lattice F S (a : F),
      tensorFunction F S fArch φ ((m : Space F S) + t) * tracePhase F S e b m) =
    ((productModule F S (a : F))⁻¹ : ℂ) *
      ∑' h : lattice F S ((a⁻¹ : Fˣ) : F),
        tracePhase F S e ((h : Space F S) - b) t *
          fourierIntegral F S e μ (tensorFunction F S fArch φ)
            ((h : Space F S) - b) := by
  obtain ⟨gArch, ψ, hψlocal, hψsupport, hg⟩ :=
    tensorFunction_shift_modulation_bruhatSchwartz F S e he fArch φ hlocal hsupport t b
  obtain ⟨kArch, χ, hχlocal, hχsupport, hk, hkFourier⟩ :=
    ScaleShift.scalar_pullback_tensor F S e μ he gArch ψ hψlocal hψsupport a
  have hbase := ScaleShift.normalized_tensor_poisson F S hS e μ he
    hconductor hnorm hdiagonal kArch χ hχlocal hχsupport
  have hleft :
      (∑' m : lattice F S 1, tensorFunction F S kArch χ m) =
        ∑' m : lattice F S (a : F),
          tensorFunction F S fArch φ ((m : Space F S) + t) * tracePhase F S e b m := by
    calc
      _ = ∑' m : lattice F S 1,
          tensorFunction F S gArch ψ (ScaleShift.scalarAction F S (a : F) m) :=
        tsum_congr (fun m => hk m)
      _ = ∑' m : lattice F S (a : F), tensorFunction F S gArch ψ m := by
        have hr := ScaleShift.tsum_scalar_lattice F S a 1 (tensorFunction F S gArch ψ)
        rw [mul_one] at hr
        exact hr
      _ = _ := tsum_congr (fun m => hg m)
  have hright :
      (∑' h : lattice F S 1, fourierIntegral F S e μ (tensorFunction F S kArch χ) h) =
        ((productModule F S (a : F))⁻¹ : ℂ) *
          ∑' h : lattice F S ((a⁻¹ : Fˣ) : F),
            tracePhase F S e ((h : Space F S) - b) t *
              fourierIntegral F S e μ (tensorFunction F S fArch φ)
                ((h : Space F S) - b) := by
    calc
      _ = ∑' h : lattice F S 1, ((productModule F S (a : F))⁻¹ : ℂ) *
          fourierIntegral F S e μ (tensorFunction F S gArch ψ)
            (ScaleShift.scalarAction F S ((a⁻¹ : Fˣ) : F) h) :=
        tsum_congr (fun h => hkFourier h)
      _ = ((productModule F S (a : F))⁻¹ : ℂ) *
          ∑' h : lattice F S 1,
            fourierIntegral F S e μ (tensorFunction F S gArch ψ)
              (ScaleShift.scalarAction F S ((a⁻¹ : Fˣ) : F) h) := tsum_mul_left
      _ = ((productModule F S (a : F))⁻¹ : ℂ) *
          ∑' h : lattice F S ((a⁻¹ : Fˣ) : F),
            fourierIntegral F S e μ (tensorFunction F S gArch ψ) h := by
        congr 1
        have hr := ScaleShift.tsum_scalar_lattice F S a⁻¹ 1
          (fourierIntegral F S e μ (tensorFunction F S gArch ψ))
        rw [mul_one] at hr
        exact hr
      _ = _ := by
        congr 1
        apply tsum_congr
        intro h
        rw [show tensorFunction F S gArch ψ =
            (fun x => tensorFunction F S fArch φ (x + t) * tracePhase F S e b x) from
          funext hg]
        exact fourierIntegral_shift_modulation F S e μ he fArch φ hlocal hsupport t b h
  exact hleft.symm.trans (hbase.trans hright)

theorem tensorFunction_local_dilation_bruhatSchwartz
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v))
    (d : (SLocalProduct F S)ˣ) :
    ∃ (gArch : 𝓢(PoissonArch.Space F, ℂ))
      (ψ : (v : S) → v.val.adicCompletion F → ℂ),
      (∀ x, gArch x = fArch ((PoissonArch.infiniteAdeleToSpace F)
        ((d⁻¹ : (SLocalProduct F S)ˣ).val.1 *
          (PoissonArch.infiniteAdeleToSpace F).symm x))) ∧
      (∀ v x, ψ v x = φ v ((d⁻¹ : (SLocalProduct F S)ˣ).val.2 v * x)) ∧
      (∀ v, IsLocallyConstant (ψ v)) ∧ (∀ v, HasCompactSupport (ψ v)) ∧
      ∀ x, tensorFunction F S fArch φ (localDilation F S d⁻¹ x) =
        tensorFunction F S gArch ψ x := by
  let R := NumberField.mixedEmbedding.mixedSpace F
  let e : NumberField.InfiniteAdeleRing F ≃+* R := NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
  let u : Rˣ := Units.map e.toMonoidHom (Units.map (RingHom.fst _ _).toMonoidHom d⁻¹)
  let A : PoissonArch.Space F ≃L[ℝ] PoissonArch.Space F :=
    (NumberField.mixedEmbedding.euclidean.toMixed F).trans
      ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := R)) u) |>.trans
        (NumberField.mixedEmbedding.euclidean.toMixed F).symm
  let gArch := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A fArch
  let ψ := fun (v : S) x => φ v ((d⁻¹ : (SLocalProduct F S)ˣ).val.2 v * x)
  have hA (x : PoissonArch.Space F) : A x = (PoissonArch.infiniteAdeleToSpace F)
        ((d⁻¹ : (SLocalProduct F S)ˣ).val.1 * (PoissonArch.infiniteAdeleToSpace F).symm x) := by
    apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
    change (↑u : R) * (NumberField.mixedEmbedding.euclidean.toMixed F x) = _
    rw [PoissonArch.infiniteAdeleToSpace_coordinates, map_mul]
    have hx := PoissonArch.infiniteAdeleToSpace_coordinates F
      ((PoissonArch.infiniteAdeleToSpace F).symm x)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hx
    rw [← hx]
    rfl
  refine ⟨gArch, ψ, ?_, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro x
    exact congrArg fArch (hA x)
  · intro v
    exact (hlocal v).comp_continuous (continuous_const.mul continuous_id)
  · intro v
    let dv : (v.val.adicCompletion F)ˣ := Units.map
      ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom d⁻¹
    exact (hsupport v).comp_homeomorph (Homeomorph.smul dv)
  · intro x
    change fArch ((PoissonArch.infiniteAdeleToSpace F)
      ((d⁻¹ : (SLocalProduct F S)ˣ).val.1 * (PoissonArch.infiniteAdeleToSpace F).symm x.1)) *
      (∏ v : S, φ v ((d⁻¹ : (SLocalProduct F S)ˣ).val.2 v * x.2 v)) =
      fArch (A x.1) * (∏ v : S, φ v ((d⁻¹ : (SLocalProduct F S)ˣ).val.2 v * x.2 v))
    rw [hA]

private theorem norm_arch_mixed (F : Type) [Field F] [NumberField F]
    (z : InfiniteAdeleRing F) :
    ‖z‖ = (∏ v : {v : InfinitePlace F // v.IsReal},
      |(InfiniteAdeleRing.ringEquiv_mixedSpace F z).1 v|) *
      ∏ v : {v : InfinitePlace F // v.IsComplex},
        Complex.normSq ((InfiniteAdeleRing.ringEquiv_mixedSpace F z).2 v) := by
  classical
  rw [InfiniteAdeleRing.norm_def]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : InfinitePlace F => v.IsReal)
    (fun v => ‖z v‖ ^ v.mult)]
  congr 1
  · apply Finset.prod_congr rfl; intro v hv
    rw [v.2.mult_eq_one, pow_one]
    change ‖z v.1‖ = |NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (z v.1)|
    simpa only [dist_zero_right, map_zero, Real.norm_eq_abs] using
      ((NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).dist_eq
        (z v.1) 0).symm
  · let equiv : {v : InfinitePlace F // ¬ v.IsReal} ≃
        {v : InfinitePlace F // v.IsComplex} :=
      Equiv.subtypeEquivRight fun _ => InfinitePlace.not_isReal_iff_isComplex
    apply Fintype.prod_equiv equiv
    intro v
    have hv := InfinitePlace.not_isReal_iff_isComplex.mp v.2
    rw [hv.mult_eq_two, Complex.normSq_eq_norm_sq]
    change ‖z v.1‖ ^ 2 = ‖NumberField.InfinitePlace.Completion.extensionEmbedding v.1 (z v.1)‖ ^ 2
    congr 1
    simpa only [dist_zero_right, map_zero] using
      ((NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).dist_eq
        (z v.1) 0).symm
 def localArchEquiv (F : Type) [Field F] [NumberField F]
    (d : (InfiniteAdeleRing F)ˣ) : PoissonArch.Space F ≃L[ℝ] PoissonArch.Space F :=
  let w : (mixedEmbedding.mixedSpace F)ˣ :=
    Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMonoidHom d
  ((mixedEmbedding.euclidean.toMixed F).trans
    ((ContinuousLinearEquiv.piCongrRight fun v : {v : InfinitePlace F // v.IsReal} =>
      ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.map (Pi.evalRingHom _ v).toMonoidHom
          (Units.map (RingHom.fst _ _).toMonoidHom w))).prodCongr
      (ContinuousLinearEquiv.piCongrRight fun v : {v : InfinitePlace F // v.IsComplex} =>
        (ContinuousLinearEquiv.unitsEquivAut ℂ
          (Units.map (Pi.evalRingHom _ v).toMonoidHom
            (Units.map (RingHom.snd _ _).toMonoidHom w))).restrictScalars ℝ))).trans
    (mixedEmbedding.euclidean.toMixed F).symm

private theorem localArchEquiv_apply (F : Type) [Field F] [NumberField F]
    (d : (InfiniteAdeleRing F)ˣ) (x : PoissonArch.Space F) :
    localArchEquiv F d x = PoissonArch.infiniteAdeleToSpace F
      (d.val * (PoissonArch.infiniteAdeleToSpace F).symm x) := by
  apply (mixedEmbedding.euclidean.toMixed F).injective
  simp only [localArchEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
    PoissonArch.infiniteAdeleToSpace_coordinates, map_mul]
  have hx := PoissonArch.infiniteAdeleToSpace_coordinates F
    ((PoissonArch.infiniteAdeleToSpace F).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hx
  rw [← hx]
  ext v <;> simp [ContinuousLinearEquiv.piCongrRight_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]

private theorem localArchEquiv_abs_det (F : Type) [Field F] [NumberField F]
    (d : (InfiniteAdeleRing F)ˣ) :
    |LinearMap.det (localArchEquiv F d).toLinearMap| = ‖d.val‖ := by
  let z := InfiniteAdeleRing.ringEquiv_mixedSpace F d.val
  let R : {v : InfinitePlace F // v.IsReal} → ℝ →ₗ[ℝ] ℝ :=
    fun v => LinearMap.mulLeft ℝ (z.1 v)
  let C : {v : InfinitePlace F // v.IsComplex} → ℂ →ₗ[ℝ] ℂ :=
    fun v => (LinearMap.mulLeft ℂ (z.2 v)).restrictScalars ℝ
  have he : (localArchEquiv F d).toLinearMap =
    (mixedEmbedding.euclidean.toMixed F).symm.toLinearMap.comp
      (((LinearMap.pi fun v => (R v).comp (LinearMap.proj v)).prodMap
        (LinearMap.pi fun v => (C v).comp (LinearMap.proj v))).comp
          (mixedEmbedding.euclidean.toMixed F).toLinearMap) := by
    ext x
    apply (mixedEmbedding.euclidean.toMixed F).injective
    change (mixedEmbedding.euclidean.toMixed F) (localArchEquiv F d x) = _
    rw [localArchEquiv_apply]
    simp only [PoissonArch.infiniteAdeleToSpace_coordinates, map_mul,
      LinearMap.prodMap_apply, ContinuousLinearEquiv.coe_coe,
      LinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    have hx := PoissonArch.infiniteAdeleToSpace_coordinates F
      ((PoissonArch.infiniteAdeleToSpace F).symm x)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hx
    rw [← hx]
    ext v <;> simp [R, C, z, mul_comm]
  rw [he, ContinuousLinearEquiv.toLinearEquiv_symm]
  have hd := LinearMap.det_conj
    ((LinearMap.pi fun v => (R v).comp (LinearMap.proj v)).prodMap
      (LinearMap.pi fun v => (C v).comp (LinearMap.proj v)))
    (mixedEmbedding.euclidean.toMixed F).toLinearEquiv.symm
  simp only [LinearEquiv.symm_symm] at hd
  rw [hd, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi, abs_mul]
  have hc (c : ℂ) : LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) =
      Complex.normSq c := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_mulLeft, Algebra.norm_complex_apply]
  simp only [R, C, LinearMap.det_mulLeft, hc, Finset.abs_prod,
    abs_of_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _)]
  exact (norm_arch_mixed F d.val).symm
private theorem localArchPairing_scale (F : Type) [Field F] [NumberField F]
    (d : (InfiniteAdeleRing F)ˣ) (x y : PoissonArch.Space F) :
    PoissonArch.tracePairing F (localArchEquiv F d⁻¹ x) (localArchEquiv F d y) =
      PoissonArch.tracePairing F x y := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hh : e (d⁻¹).val * e d.val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  simp only [localArchEquiv_apply, PoissonArch.tracePairing,
    PoissonArch.infiniteAdeleToSpace_coordinates, map_mul]
  have hx := PoissonArch.infiniteAdeleToSpace_coordinates F
    ((PoissonArch.infiniteAdeleToSpace F).symm x)
  have hy := PoissonArch.infiniteAdeleToSpace_coordinates F
    ((PoissonArch.infiniteAdeleToSpace F).symm y)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hx hy
  rw [← hx, ← hy]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    have h := congrArg (fun z => z.1 v) hh
    simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] at h ⊢
    rw [mul_mul_mul_comm, h, one_mul]
  · congr 1
    apply Finset.sum_congr rfl
    intro v hv
    have h := congrArg (fun z => z.2 v) hh
    simp only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] at h ⊢
    rw [mul_mul_mul_comm, h, one_mul]

private theorem localArchEquiv_inv (F : Type) [Field F] [NumberField F]
    (d : (InfiniteAdeleRing F)ˣ) : localArchEquiv F d⁻¹ = (localArchEquiv F d).symm := by
  apply ContinuousLinearEquiv.symm_bijective.injective
  ext x
  apply (localArchEquiv F d⁻¹).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_symm]
  simp only [localArchEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [← mul_assoc, Units.inv_mul, one_mul, ContinuousLinearEquiv.apply_symm_apply]

theorem traceFourier_local_unit_scale (F : Type) [Field F] [NumberField F]
    (f : PoissonArch.Space F → ℂ) (d : (InfiniteAdeleRing F)ˣ) (y : PoissonArch.Space F) :
    PoissonArch.traceFourier F (fun x => f (PoissonArch.infiniteAdeleToSpace F
      ((d⁻¹).val * (PoissonArch.infiniteAdeleToSpace F).symm x))) y =
    (‖d.val‖ : ℂ) * PoissonArch.traceFourier F f (PoissonArch.infiniteAdeleToSpace F
      (d.val * (PoissonArch.infiniteAdeleToSpace F).symm y)) := by
  let A := localArchEquiv F d
  have hdet : LinearMap.det A.symm.toLinearMap ≠ 0 := A.symm.toLinearEquiv.isUnit_det'.ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (PoissonArch.Space F)) hdet
  let g := fun x => f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
    (PoissonArch.tracePairing F x (A y) : ℂ))
  have hi := integral_map_equiv (μ := (volume : Measure (PoissonArch.Space F)))
    A.symm.toHomeomorph.toMeasurableEquiv g
  rw [show Measure.map A.symm.toHomeomorph.toMeasurableEquiv volume =
      Measure.map A.symm.toLinearMap volume from rfl, hmap,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at hi
  have hfactor : |(LinearMap.det A.symm.toLinearMap)⁻¹| = ‖d.val‖ := by
    rw [show A.symm.toLinearMap = A.toLinearEquiv.symm.toLinearMap from rfl,
      LinearEquiv.det_coe_symm, inv_inv]
    exact localArchEquiv_abs_det F d
  have hp (x : PoissonArch.Space F) : g (A.symm x) =
      f (PoissonArch.infiniteAdeleToSpace F ((d⁻¹).val *
        (PoissonArch.infiniteAdeleToSpace F).symm x)) *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x y : ℂ)) := by
    change f (A.symm x) * Complex.exp _ = _
    rw [← localArchEquiv_inv, localArchPairing_scale, localArchEquiv_apply]
  rw [hfactor] at hi
  change ‖d.val‖ • (∫ x, g x ∂(volume : Measure (PoissonArch.Space F))) =
    ∫ x, g (A.symm x) ∂(volume : Measure (PoissonArch.Space F)) at hi
  simp_rw [hp] at hi
  unfold PoissonArch.traceFourier PoissonArch.traceMeasure
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (PoissonArch.haarScalar_pos F).le,
    smul_eq_mul]
  rw [← hi]
  simp only [g, A, localArchEquiv_apply, Complex.real_smul]
  ring

private lemma norm_pow (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (RingOfIntegers F))
    (d : (v.adicCompletion F)ˣ) : ∃ k : ℤ, ‖d.val‖ = (v.asIdeal.absNorm : ℝ)^(-k) := by
  have hd : Valued.v d.val ≠ (0 : WithZero (Multiplicative ℤ)) := by
    exact (Valued.v.map_eq_zero_iff).not.mpr d.ne_zero
  refine ⟨-WithZero.log (Valued.v d.val), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hd, neg_neg]
  simp
private lemma ballfacts (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure] :
    0 < μv {x | ‖x‖ ≤ 1} ∧ μv {x | ‖x‖ ≤ 1} ≠ ⊤ := by
  letI : LocallyCompactSpace (v.adicCompletion F) :=
    (finite_components_locallyCompact F {v}).1 ⟨v, Finset.mem_singleton_self v⟩
  have ho : IsOpen {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    simpa [Metric.closedBall, dist_zero_right] using
      IsUltrametricDist.isOpen_closedBall (0 : v.adicCompletion F) one_ne_zero
  have hc : IsCompact {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    simpa [Metric.closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : v.adicCompletion F) (1 : ℝ))
  exact ⟨ho.measure_pos μv ⟨0, by simp⟩, hc.measure_lt_top.ne⟩
private lemma generic_ball_mass (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure] (k : ℤ) :
    μv.real {x | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ)^(-k)} =
      (v.asIdeal.absNorm : ℝ)^(-k) * μv.real {x | ‖x‖ ≤ 1} := by
  let U : Set (v.adicCompletion F) := {x | ‖x‖ ≤ 1}
  let m := integerVolume F v
  have hm : 0 < m := integerVolume_pos F v
  have hU := ballfacts F v μv
  let c : ENNReal := ENNReal.ofReal m / μv U
  have hc0 : c ≠ 0 := by
    exact ENNReal.div_ne_zero.mpr ⟨by simpa using hm, hU.2⟩
  have hctop : c ≠ ⊤ := by
    apply ENNReal.div_ne_top ENNReal.ofReal_ne_top hU.1.ne'
  let ν : Measure (v.adicCompletion F) := c • μv
  haveI : ν.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul μv hc0 hctop
  have hν : ν U = ENNReal.ofReal m := by
    simp only [ν, Measure.smul_apply, smul_eq_mul, c]
    rw [ENNReal.div_mul_cancel hU.1.ne' hU.2]
  have hh := local_ball_volume F v ν hν k
  have hc : c.toReal * μv.real U = m := by
    have h := congrArg ENNReal.toReal hν
    simpa only [ν, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hm.le, Measure.real] using h
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hr : c.toReal * μv.real {x | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ)^(-k)} =
      (v.asIdeal.absNorm : ℝ)^(-k) * m := by
    simpa only [ν, Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul] using hh
  apply (mul_left_cancel₀ hcpos.ne')
  rw [hr, ← hc]
  ring
theorem finite_unit_integral_scale (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure]
    (d : (v.adicCompletion F)ˣ) (f : v.adicCompletion F → ℂ) :
    (∫ x, f ((d⁻¹).val * x) ∂μv) = (‖d.val‖ : ℂ) * ∫ x, f x ∂μv := by
  let K := v.adicCompletion F
  letI : LocallyCompactSpace K :=
    (finite_components_locallyCompact F {v}).1 ⟨v, Finset.mem_singleton_self v⟩
  letI : SecondCountableTopology K := completion_secondCountable F v
  let A : K ≃ₜ+ K :=
    { DistribMulAction.toAddEquiv K d⁻¹ with
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let ν : Measure K := μv.map A
  haveI : ν.IsAddHaarMeasure := A.isAddHaarMeasure_map μv
  let c := ν.addHaarScalarFactor μv
  have hν : ν = c • μv := Measure.isAddLeftInvariant_eq_smul ν μv
  let U : Set K := {x | ‖x‖ ≤ 1}
  have hpre : A ⁻¹' U = {x : K | ‖x‖ ≤ ‖d.val‖} := by
    ext x
    change ‖(d⁻¹).val*x‖ ≤ 1 ↔ ‖x‖ ≤ ‖d.val‖
    rw [norm_mul]
    have hi : ‖(d⁻¹).val‖ * ‖d.val‖ = 1 := by rw [← norm_mul, Units.inv_mul, norm_one]
    constructor
    · intro h
      have hh := mul_le_mul_of_nonneg_right h (norm_nonneg d.val)
      rw [mul_right_comm, hi, one_mul, one_mul] at hh
      exact hh
    · intro h
      have hh := mul_le_mul_of_nonneg_left h (norm_nonneg (d⁻¹).val)
      nlinarith [hi]
  have hUm : MeasurableSet U := by
    exact (isClosed_le continuous_norm continuous_const).measurableSet
  have hmass : ν.real U = ‖d.val‖ * μv.real U := by
    change ((μv.map A) U).toReal = _
    rw [Measure.map_apply (show Measurable A from A.continuous.measurable) hUm, hpre]
    obtain ⟨k, hk⟩ := norm_pow F v d
    rw [hk]
    exact generic_ball_mass F v μv k
  have hc : (c : ℝ) = ‖d.val‖ := by
    have hU := ballfacts F v μv
    have hm : 0 < μv.real U := ENNReal.toReal_pos hU.1.ne' hU.2
    rw [hν] at hmass
    change (((c : ENNReal) * μv U).toReal) = _ at hmass
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at hmass
    exact (mul_right_cancel₀ hm.ne') hmass
  have hi := integral_map_equiv (μ := μv) A.toHomeomorph.toMeasurableEquiv f
  change (∫ x, f x ∂ν) = _ at hi
  rw [hν, integral_smul_nnreal_measure] at hi
  change (c : ℝ) • (∫ x, f x ∂μv) = ∫ x, f ((d⁻¹).val * x) ∂μv at hi
  rw [hc, Complex.real_smul] at hi
  exact hi.symm

theorem fourierIntegral_local_dilation
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v))
    (d : (SLocalProduct F S)ˣ) (y : Space F S) :
    fourierIntegral F S e μ
      (fun x => tensorFunction F S fArch φ (localDilation F S d⁻¹ x)) y =
      (localDilationModule F S d : ℂ) *
        fourierIntegral F S e μ (tensorFunction F S fArch φ) (localDilation F S d y) := by
  obtain ⟨g, ψ, hg, hψ, hl, hs, hfun⟩ := tensorFunction_local_dilation_bruhatSchwartz
    F S fArch φ hlocal hsupport d
  have hfun' : (fun x => tensorFunction F S fArch φ (localDilation F S d⁻¹ x)) =
      tensorFunction F S g ψ := funext hfun
  rw [hfun', fourierIntegral_tensorFunction F S e μ he g ψ hl hs,
    fourierIntegral_tensorFunction F S e μ he fArch φ hlocal hsupport]
  let da : (InfiniteAdeleRing F)ˣ := Units.map (RingHom.fst _ _).toMonoidHom d
  have hga : PoissonArch.traceFourier F g y.1 =
      (‖d.val.1‖ : ℂ) * PoissonArch.traceFourier F fArch (localDilation F S d y).1 := by
    have hg' : (g : PoissonArch.Space F → ℂ) = fun x => fArch
      (PoissonArch.infiniteAdeleToSpace F ((da⁻¹).val * (PoissonArch.infiniteAdeleToSpace F).symm x)) := funext hg
    rw [hg']
    exact traceFourier_local_unit_scale F fArch da y.1
  rw [hga]
  have hv (v : S) : (∫ x, ψ v x * (e v (-x*y.2 v) : ℂ) ∂μ v) =
      (‖d.val.2 v‖ : ℂ) * ∫ x, φ v x * (e v (-x*(localDilation F S d y).2 v) : ℂ) ∂μ v := by
    let dv : (v.val.adicCompletion F)ˣ := Units.map
      ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom d
    have hh : dv.val * (dv⁻¹).val = 1 := Units.mul_inv dv
    have hh' : ∀ x : v.val.adicCompletion F,
        -((dv⁻¹).val*x)*(dv.val*y.2 v) = -x*y.2 v := by
      intro x
      calc
        _ = -(dv.val*(dv⁻¹).val)*x*y.2 v := by ring
        _ = _ := by rw [hh]; ring
    have hi := finite_unit_integral_scale F v.val (μ v) dv
      (fun x => φ v x * (e v (-x*(dv.val*y.2 v)) : ℂ))
    simp only [hh'] at hi
    have hdv : (dv⁻¹).val = (d⁻¹).val.2 v := rfl
    have hdy : (localDilation F S d y).2 v = dv.val * y.2 v := rfl
    have hdv' : dv.val = d.val.2 v := rfl
    simpa only [hψ, hdy, hdv, hdv'] using hi
  simp_rw [hv]
  rw [Finset.prod_mul_distrib]
  simp only [localDilationModule, Complex.ofReal_mul, Complex.ofReal_prod]
  ring

end DedekindZetaZeroFree.PoissonS

end

end
