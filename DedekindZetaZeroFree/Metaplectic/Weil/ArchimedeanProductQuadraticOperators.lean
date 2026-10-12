module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.TensorConvolutionApproximation
public import DedekindZetaZeroFree.Metaplectic.Weil.ThetaAndQuadraticOperators

@[expose] public section

section

noncomputable section
open scoped Classical ENNReal NNReal

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

private theorem productFourier_tensor {ι : Type*} [Fintype ι]
    (g : ι → ℂ → ℂ) (y : ι → ℂ) :
    productFourier (fun z => ∏ i, g i (z i)) y = ∏ i, ComplexWeil.F 2 (g i) (y i) := by
  letI : MeasureTheory.SigmaFinite (ComplexWeil.mu 2) := by
    unfold ComplexWeil.mu
    rw [show ENNReal.ofReal ‖(2 : ℂ)‖ = ((2 : ℝ≥0) : ℝ≥0∞) by norm_num]
    change MeasureTheory.SigmaFinite ((2 : ℝ≥0) • (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    infer_instance
  unfold productFourier ComplexWeil.F
  simp_rw [← Finset.prod_mul_distrib]
  exact MeasureTheory.integral_fintype_prod_eq_prod (E := fun _ : ι => ℂ)
    (fun i x => g i x * ComplexWeil.psi 2 (-x * y i))

private theorem productChirp_tensor {ι : Type*} [Fintype ι]
    (b : ι → ℂ) (g : ι → ℂ → ℂ) :
    productChirp b (fun z => ∏ i, g i (z i)) =
      (fun z => ∏ i, ComplexWeil.M 2 (b i) (g i) (z i)) := by
  funext z
  simp only [productChirp, ComplexWeil.M, Finset.prod_mul_distrib]

theorem product_quadratic_on_tensor {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) (f : SchwartzMap (ι → ℂ) ℂ)
    (g : ι → SchwartzMap ℂ ℂ) (hf : ∀ z, f z = ∏ i, g i (z i)) (y : ι → ℂ) :
    productFourier (productChirp a (productFourier (⇑f))) y =
      (∏ i, ((1 / (2 * ‖a i‖) : ℝ) : ℂ)) *
        productChirp (fun i => -1 / (4 * a i))
          (productDilation (fun i => 1 / (2 * a i))
            (productFourier (productChirp (fun i => -1 / (4 * a i)) (⇑f)))) y := by
  have hfg : (⇑f : (ι → ℂ) → ℂ) = fun z => ∏ i, g i (z i) := funext hf
  rw [hfg]
  have hF : productFourier (fun z => ∏ i, g i (z i)) =
      fun z => ∏ i, ComplexWeil.F 2 (⇑(g i)) (z i) :=
    funext (productFourier_tensor (fun i => ⇑(g i)))
  rw [hF, productChirp_tensor, productFourier_tensor, productChirp_tensor]
  unfold productChirp productDilation
  rw [productFourier_tensor]
  simp_rw [ComplexWeil.F_M_F_quadratic_kernel 2 _ (by norm_num) (ha _) (g _)]
  simp only [Finset.prod_mul_distrib]
  rw [mul_assoc]
  congr 1
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    congr 1
    ring
  · apply Finset.prod_congr rfl
    intro i hi
    congr 1
    ring

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical NNReal RealInnerProductSpace
namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps
variable {ι : Type*} [Fintype ι]
 def coords : PiLp 2 (fun _ : ι => ℂ) ≃L[ℝ] (ι → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℝ _
 def freq : (ι → ℂ) ≃L[ℝ] PiLp 2 (fun _ : ι => ℂ) :=
  (ContinuousLinearEquiv.piCongrRight (fun _ : ι =>
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
      (Units.mk0 (2 : ℂ) (by norm_num))).trans Complex.conjCLE)).trans coords.symm
private lemma freq_apply (y : ι → ℂ) (i : ι) :
    freq y i = (starRingEnd ℂ) (2 * y i) := rfl
 instance mu_haar : (ComplexWeil.mu 2).IsAddHaarMeasure := by
  rw [ComplexWeil.mu_two]
  exact Measure.IsAddHaarMeasure.smul _ (by norm_num) (by norm_num)
 def prodMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  Measure.pi (fun _ : ι => ComplexWeil.mu 2)
 instance prod_haar : (prodMeasure ι).IsAddHaarMeasure := by
  dsimp [prodMeasure]
  infer_instance
 def scalar (ι : Type*) [Fintype ι] : ℝ≥0 :=
  ((prodMeasure ι).map (coords (ι := ι)).symm).addHaarScalarFactor volume
private lemma measure_eq :
    (prodMeasure ι).map (coords (ι := ι)).symm = scalar ι • volume := by
  letI := (coords (ι := ι)).symm.isAddHaarMeasure_map (prodMeasure ι)
  exact Measure.isAddLeftInvariant_eq_smul _ _
private lemma kernel_eq (z : PiLp 2 (fun _ : ι => ℂ)) (y : ι → ℂ) :
    (∏ i, ComplexWeil.psi 2 (-z i * y i)) =
      (Real.fourierChar (- inner ℝ z (freq y)) : ℂ) := by
  simp only [ComplexWeil.psi, Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [PiLp.inner_apply, ← Finset.sum_neg_distrib]
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [freq_apply, Complex.inner]
  norm_num [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im]
  push_cast
  ring
private lemma prodFourier_eq (f : (ι → ℂ) → ℂ) (y : ι → ℂ) :
    productFourier f y = (scalar ι : ℂ) *
      FourierTransform.fourier (fun z => f (coords z)) (freq y) := by
  have hi := integral_map_equiv (μ := prodMeasure ι)
    (coords (ι := ι)).symm.toHomeomorph.toMeasurableEquiv
    (fun z : PiLp 2 (fun _ : ι => ℂ) =>
      f (coords z) * ∏ i, ComplexWeil.psi 2 (-z i * y i))
  change (∫ z : PiLp 2 (fun _ : ι => ℂ),
    f (coords z) * ∏ i, ComplexWeil.psi 2 (-z i * y i)
      ∂(prodMeasure ι).map (coords (ι := ι)).symm) = productFourier f y at hi
  rw [measure_eq, integral_smul_nnreal_measure] at hi
  simp only [Complex.real_smul] at hi
  rw [← hi, Real.fourier_eq]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [kernel_eq, Circle.smul_def]
  ring
set_option backward.isDefEq.respectTransparency false in
private lemma chirp_growth (b : ι → ℂ) :
    (fun z : ι → ℂ => ∏ i, ComplexWeil.psi 2 (b i * z i ^ 2)).HasTemperateGrowth := by
  have hp (i : ι) : (fun z : ι → ℂ => ComplexWeil.psi 2 (b i * z i ^ 2)).HasTemperateGrowth := by
    have he : (fun z : ι → ℂ => z i).HasTemperateGrowth :=
      (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).hasTemperateGrowth
    have hm : (fun z : ι → ℂ => 2 * (b i * z i ^ 2)).HasTemperateGrowth := by
      convert! ((Function.HasTemperateGrowth.const (2 : ℂ)).mul
        ((Function.HasTemperateGrowth.const (b i)).mul (he.pow 2))) using 1
    have hq : (fun z : ι → ℂ => (2 * (b i * z i ^ 2)).re).HasTemperateGrowth := by
      exact Complex.reCLM.hasTemperateGrowth.comp hm
    have h := Complex.hasTemperateGrowth_exp_mul_I.comp
      ((Function.HasTemperateGrowth.const (2 * Real.pi)).mul hq)
    simpa [ComplexWeil.psi, Function.comp_def] using h
  have hprod (s : Finset ι) :
      (fun z : ι → ℂ => ∏ i ∈ s, ComplexWeil.psi 2 (b i * z i ^ 2)).HasTemperateGrowth := by
    induction s using Finset.induction_on with
    | empty => simpa using (Function.HasTemperateGrowth.const (1 : ℂ))
    | @insert i s hi hs =>
      simp only [Finset.prod_insert hi]
      convert! (hp i).mul hs using 1
  exact hprod Finset.univ
 def chirpCLM (b : ι → ℂ) :
    SchwartzMap (ι → ℂ) ℂ →L[ℂ] SchwartzMap (ι → ℂ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z => ∏ i, ComplexWeil.psi 2 (b i * z i ^ 2))
private lemma chirpCLM_apply (b : ι → ℂ) (f : SchwartzMap (ι → ℂ) ℂ) :
    ⇑(chirpCLM b f) = productChirp b (⇑f) := by
  funext z
  rw [chirpCLM, SchwartzMap.smulLeftCLM_apply_apply (chirp_growth b)]
  rfl
 def fourierCLM :
    SchwartzMap (ι → ℂ) ℂ →L[ℂ] SchwartzMap (ι → ℂ) ℂ :=
  (scalar ι : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ freq ∘L
      SchwartzMap.fourierTransformCLM ℂ ∘L
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coords)
private lemma fourierCLM_apply (f : SchwartzMap (ι → ℂ) ℂ) :
    ⇑(fourierCLM f) = productFourier (⇑f) := by
  funext y
  rw [prodFourier_eq]
  simp [fourierCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    SchwartzMap.fourier_coe, Function.comp_def, smul_eq_mul]
 def evalCLM (y : ι → ℂ) : SchwartzMap (ι → ℂ) ℂ →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (ι → ℂ) ℂ)
private lemma evalCLM_apply (y : ι → ℂ) (f : SchwartzMap (ι → ℂ) ℂ) : evalCLM y f = f y := rfl

theorem product_quadratic_continuous_linear {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) (y : ι → ℂ) :
    ∃ L R : SchwartzMap (ι → ℂ) ℂ →L[ℂ] ℂ,
      (∀ f, L f = productFourier (productChirp a (productFourier (⇑f))) y) ∧
      (∀ f, R f = (∏ i, ((1 / (2 * ‖a i‖) : ℝ) : ℂ)) *
        productChirp (fun i => -1 / (4 * a i))
          (productDilation (fun i => 1 / (2 * a i))
            (productFourier (productChirp (fun i => -1 / (4 * a i)) (⇑f)))) y) := by
  let b : ι → ℂ := fun i => -1 / (4 * a i)
  let c : ℂ := (∏ i, ((1 / (2 * ‖a i‖) : ℝ) : ℂ)) *
    ∏ i, ComplexWeil.psi 2 (b i * y i ^ 2)
  refine ⟨evalCLM y ∘L fourierCLM ∘L chirpCLM a ∘L fourierCLM,
    c • (evalCLM (fun i => 1 / (2 * a i) * y i) ∘L fourierCLM ∘L chirpCLM b), ?_, ?_⟩
  · intro f
    simp only [ContinuousLinearMap.comp_apply, evalCLM_apply]
    rw [fourierCLM_apply, chirpCLM_apply, fourierCLM_apply]
  · intro f
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      evalCLM_apply, smul_eq_mul]
    rw [fourierCLM_apply, chirpCLM_apply]
    simp only [c, b, productChirp, productDilation]
    ring
end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

end

end

section

noncomputable section
open NumberField
open scoped NumberField Classical

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

def complexCoordinates (F : Type) [Field F] [NumberField F] (x : PoissonArch.Space F) :
    {w : InfinitePlace F // w.IsComplex} → ℂ :=
  (mixedEmbedding.euclidean.toMixed F x).2

def complexLift (F : Type) [Field F] [NumberField F]
    (z : {w : InfinitePlace F // w.IsComplex} → ℂ) : PoissonArch.Space F :=
  (mixedEmbedding.euclidean.toMixed F).symm (0, z)

theorem complex_coordinate_transport {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) :
    (∀ x, complexLift F (complexCoordinates F x) = x) ∧
    (∀ (f : PoissonArch.Space F → ℂ) y,
      PoissonArch.traceFourier F f y =
        productFourier (fun z => f (complexLift F z)) (complexCoordinates F y)) ∧
    (∀ f : SchwartzMap (PoissonArch.Space F) ℂ,
      ∃ g : SchwartzMap ({w : InfinitePlace F // w.IsComplex} → ℂ) ℂ,
        ∀ z, g z = f (complexLift F z)) := by
  letI : IsEmpty {w : InfinitePlace F // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place w.val)) w.property⟩
  have hl : ∀ x, complexLift F (complexCoordinates F x) = x := by
    intro x
    apply (mixedEmbedding.euclidean.toMixed F).injective
    simp only [complexLift, complexCoordinates, ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext (Subsingleton.elim _ _) rfl
  refine ⟨hl, ?_, ?_⟩
  · intro f y
    have hi (h : PoissonArch.Space F → ℂ) :
        (∫ x, h x ∂PoissonArch.traceMeasure F) =
          (PoissonArch.haarScalar F : ℂ) * ∫ z, h (complexLift F z) := by
      rw [PoissonArch.traceMeasure, MeasureTheory.integral_smul_measure,
        ENNReal.toReal_ofReal (PoissonArch.haarScalar_pos F).le]
      change (PoissonArch.haarScalar F : ℂ) * _ = _
      congr 1
      have hm := (mixedEmbedding.euclidean.volumePreserving_toMixed F).integral_comp
        (mixedEmbedding.euclidean.toMixed F).toHomeomorph.measurableEmbedding
        (fun x : mixedEmbedding.mixedSpace F =>
          h ((mixedEmbedding.euclidean.toMixed F).symm x))
      simp only [ContinuousLinearEquiv.symm_apply_apply] at hm
      rw [hm, MeasureTheory.Measure.volume_eq_prod]
      have hp := MeasureTheory.integral_prod_mul
        (μ := (MeasureTheory.volume : MeasureTheory.Measure
          ({w : InfinitePlace F // w.IsReal} → ℝ)))
        (ν := (MeasureTheory.volume : MeasureTheory.Measure
          ({w : InfinitePlace F // w.IsComplex} → ℂ)))
        (fun _ => (1 : ℂ)) (fun z => h (complexLift F z))
      simp only [one_mul] at hp
      have he : (fun x : mixedEmbedding.mixedSpace F =>
          h ((mixedEmbedding.euclidean.toMixed F).symm x)) =
          (fun x => h (complexLift F x.2)) := by
        funext x
        apply congrArg h
        apply congrArg (mixedEmbedding.euclidean.toMixed F).symm
        exact Prod.ext (Subsingleton.elim _ _) rfl
      rw [he, hp]
      simp only [MeasureTheory.integral_const, MeasureTheory.Measure.real,
        MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ,
        Finset.prod_of_isEmpty, ENNReal.toReal_one, one_smul, one_mul]
    letI : MeasureTheory.SigmaFinite (ComplexWeil.mu 2) := by
      rw [ComplexWeil.mu_two]
      change MeasureTheory.SigmaFinite ((2 : NNReal) • (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      infer_instance
    have hm : MeasureTheory.Measure.pi
        (fun _ : {w : InfinitePlace F // w.IsComplex} => ComplexWeil.mu 2) =
        ENNReal.ofReal (PoissonArch.haarScalar F) • MeasureTheory.volume := by
      apply MeasureTheory.Measure.pi_eq
      intro s hs
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.volume_pi,
        MeasureTheory.Measure.pi_pi]
      simp only [ComplexWeil.mu, MeasureTheory.Measure.smul_apply,
        Finset.prod_mul_distrib, Finset.prod_const, PoissonArch.haarScalar]
      norm_num [ENNReal.ofReal_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      rfl
    rw [PoissonArch.traceFourier, hi, productFourier, hm,
      MeasureTheory.integral_smul_measure,
      ENNReal.toReal_ofReal (PoissonArch.haarScalar_pos F).le]
    change (PoissonArch.haarScalar F : ℂ) * _ =
      (PoissonArch.haarScalar F : ℂ) * _
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    congr 1
    unfold complexLift complexCoordinates PoissonArch.tracePairing
    simp only [ContinuousLinearEquiv.apply_symm_apply, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add]
    unfold ComplexWeil.psi
    simp only [map_neg, Complex.mul_re, Complex.ofReal_ofNat]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    norm_num [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im]
    push_cast
    ring
  · intro f
    let e : ({w : InfinitePlace F // w.IsComplex} → ℂ) ≃L[ℝ] PoissonArch.Space F :=
      (ContinuousLinearEquiv.uniqueProd ℝ
        ({w : InfinitePlace F // w.IsComplex} → ℂ)
        ({w : InfinitePlace F // w.IsReal} → ℝ)).symm.trans
        (mixedEmbedding.euclidean.toMixed F).symm
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f, ?_⟩
    intro z
    change f (e z) = f (complexLift F z)
    apply congrArg f
    apply congrArg (mixedEmbedding.euclidean.toMixed F).symm
    exact Prod.ext (Subsingleton.elim _ _) rfl

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

end

end

section

noncomputable section
open NumberField
open scoped NumberField Classical

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

theorem complex_coefficient {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (a : Fˣ) :
    ((Real.sqrt (∏ w : InfinitePlace F, w (2 * (a : F)) ^ w.mult))⁻¹ : ℂ) =
      ∏ w : {w : InfinitePlace F // w.IsComplex},
        ((1 / (2 * ‖(mixedEmbedding F (a : F)).2 w‖) : ℝ) : ℂ) := by
  letI : IsEmpty {w : InfinitePlace F // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place w.1)) w.2⟩
  have hp : (∏ w : InfinitePlace F, w (2 * (a : F)) ^ w.mult) =
      ∏ w : {w : InfinitePlace F // w.IsComplex},
        (2 * ‖(mixedEmbedding F (a : F)).2 w‖) ^ 2 := by
    rw [InfinitePlace.prod_eq_prod_mul_prod]
    simp only [Fintype.prod_empty, one_mul]
    apply Finset.prod_congr rfl
    intro w _
    rw [w.2.mult_eq_two, mixedEmbedding.mixedEmbedding_apply_isComplex,
      ← InfinitePlace.norm_embedding_eq]
    simp only [map_mul, map_ofNat, norm_mul]
    norm_num
  have habs (w : {w : InfinitePlace F // w.IsComplex}) :
      |2 * ‖(mixedEmbedding F (a : F)).2 w‖| =
        2 * ‖(mixedEmbedding F (a : F)).2 w‖ := abs_of_nonneg (by positivity)
  rw [hp, Real.sqrt_prod _ (fun w _ => sq_nonneg _)]
  simp_rw [Real.sqrt_sq_eq_abs, habs, one_div]
  push_cast
  rw [Finset.prod_inv_distrib]

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

end

end

section

noncomputable section
open scoped NumberField Classical FourierTransform
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

variable (F : Type) [Field F] [NumberField F]

def archChirp (b : F) (f : PoissonArch.Space F → ℂ) : PoissonArch.Space F → ℂ :=
  fun x => Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    (PoissonArch.tracePairing F (PoissonArch.fieldMul F b x) x : ℂ)) * f x

def archDilation (c : F) (f : PoissonArch.Space F → ℂ) : PoissonArch.Space F → ℂ :=
  fun x => f (PoissonArch.fieldMul F c x)

variable {F}

def archComplexLift (F : Type) [Field F] [NumberField F]
    (z : {w : InfinitePlace F // w.IsComplex} → ℂ) : PoissonArch.Space F :=
  (mixedEmbedding.euclidean.toMixed F).symm (0, z)

theorem archChirp_complexCoordinates (b : F)
    (f : PoissonArch.Space F → ℂ) (z : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    archChirp F b f (archComplexLift F z) =
      (∏ w, ComplexWeil.psi 2 ((mixedEmbedding F b).2 w * z w ^ 2)) *
        f (archComplexLift F z) := by
  unfold archChirp
  congr 1
  unfold archComplexLift PoissonArch.tracePairing PoissonArch.fieldMul
  simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.fst_mul, Prod.snd_mul,
    Pi.mul_apply, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  unfold ComplexWeil.psi
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  push_cast
  ring

theorem archDilation_complexCoordinates (c : F)
    (f : PoissonArch.Space F → ℂ) (z : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    archDilation F c f (archComplexLift F z) =
      f (archComplexLift F (fun w => (mixedEmbedding F c).2 w * z w)) := by
  unfold archDilation archComplexLift PoissonArch.fieldMul
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  apply congrArg f
  apply congrArg (mixedEmbedding.euclidean.toMixed F).symm
  exact Prod.ext (by ext w; simp) rfl

theorem archimedean_quadratic_operator (A : SArithmeticData F) (a : Fˣ)
    (fArch : SchwartzMap (PoissonArch.Space F) ℂ) :
    PoissonArch.traceFourier F
        (archChirp F (a : F) (PoissonArch.traceFourier F fArch)) =
      fun y => ((Real.sqrt (∏ w : InfinitePlace F,
          w (2 * (a : F)) ^ w.mult))⁻¹ : ℂ) *
        archChirp F (-1 / (4 * (a : F)))
          (archDilation F (1 / (2 * (a : F)))
            (PoissonArch.traceFourier F
              (archChirp F (-1 / (4 * (a : F))) fArch))) y := by
  let ι := {w : InfinitePlace F // w.IsComplex}
  let ac : ι → ℂ := fun w => (mixedEmbedding F (a : F)).2 w
  have hac : ∀ w, ac w ≠ 0 := by
    intro w
    dsimp [ac]
    rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
    exact (map_ne_zero w.val.embedding).mpr (Units.ne_zero a)
  obtain ⟨hlift, hFourier, hSchwartz⟩ := ArchimedeanSteps.complex_coordinate_transport A
  obtain ⟨g, hg⟩ := hSchwartz fArch
  have hproduct : ∀ y : ι → ℂ,
      ArchimedeanSteps.productFourier
          (ArchimedeanSteps.productChirp ac (ArchimedeanSteps.productFourier (⇑g))) y =
        (∏ i, ((1 / (2 * ‖ac i‖) : ℝ) : ℂ)) *
          ArchimedeanSteps.productChirp (fun i => -1 / (4 * ac i))
            (ArchimedeanSteps.productDilation (fun i => 1 / (2 * ac i))
              (ArchimedeanSteps.productFourier
                (ArchimedeanSteps.productChirp (fun i => -1 / (4 * ac i)) (⇑g)))) y := by
    intro y
    obtain ⟨L, R, hL, hR⟩ :=
      ArchimedeanSteps.product_quadratic_continuous_linear ac hac y
    have heq : ∀ f ∈ ArchimedeanSteps.tensorCore ι, L f = R f := by
      apply Submodule.span_induction
      · intro f hf
        obtain ⟨gs, hfs⟩ := hf
        rw [hL, hR]
        exact ArchimedeanSteps.product_quadratic_on_tensor ac hac f gs hfs y
      · simp
      · intro f₁ f₂ hf₁ hf₂ he₁ he₂
        simp only [map_add, he₁, he₂]
      · intro c f hf he
        simp only [map_smul, he]
    have hLR : (L : SchwartzMap (ι → ℂ) ℂ → ℂ) = R :=
      Continuous.ext_on (ArchimedeanSteps.tensorCore_dense ι)
        L.continuous R.continuous heq
    rw [← hL, ← hR, hLR]
  have hchirp (b : F) (f : PoissonArch.Space F → ℂ) (z : ι → ℂ) :
      archChirp F b f (ArchimedeanSteps.complexLift F z) =
        ArchimedeanSteps.productChirp (fun w => (mixedEmbedding F b).2 w)
          (fun z => f (ArchimedeanSteps.complexLift F z)) z := by
    exact archChirp_complexCoordinates b f z
  have hcoords (z : ι → ℂ) :
      ArchimedeanSteps.complexCoordinates F (ArchimedeanSteps.complexLift F z) = z := by
    simp [ArchimedeanSteps.complexCoordinates, ArchimedeanSteps.complexLift]
  have hb : (fun w : ι => (mixedEmbedding F (-1 / (4 * (a : F)))).2 w) =
      (fun w => -1 / (4 * ac w)) := by
    funext w
    simp [ac, mixedEmbedding.mixedEmbedding_apply_isComplex, map_div₀, map_ofNat]
  have hc : (fun w : ι => (mixedEmbedding F (1 / (2 * (a : F)))).2 w) =
      (fun w => 1 / (2 * ac w)) := by
    funext w
    simp [ac, mixedEmbedding.mixedEmbedding_apply_isComplex, map_div₀, map_ofNat]
  have hF (f : PoissonArch.Space F → ℂ) (z : ι → ℂ) :
      PoissonArch.traceFourier F f (ArchimedeanSteps.complexLift F z) =
        ArchimedeanSteps.productFourier (fun z => f (ArchimedeanSteps.complexLift F z)) z := by
    rw [hFourier, hcoords]
  have hgfun : (fun z : ι → ℂ => fArch (ArchimedeanSteps.complexLift F z)) = ⇑g := by
    funext z
    exact (hg z).symm
  have hFfun (f : PoissonArch.Space F → ℂ) :
      (fun z : ι → ℂ => PoissonArch.traceFourier F f (ArchimedeanSteps.complexLift F z)) =
        ArchimedeanSteps.productFourier (fun z => f (ArchimedeanSteps.complexLift F z)) := by
    funext z
    exact hF f z
  have hMfun (b : F) (f : PoissonArch.Space F → ℂ) :
      (fun z : ι → ℂ => archChirp F b f (ArchimedeanSteps.complexLift F z)) =
        ArchimedeanSteps.productChirp (fun w => (mixedEmbedding F b).2 w)
          (fun z => f (ArchimedeanSteps.complexLift F z)) := by
    funext z
    exact hchirp b f z
  have hD (c : F) (f : PoissonArch.Space F → ℂ) (z : ι → ℂ) :
      archDilation F c f (ArchimedeanSteps.complexLift F z) =
        f (ArchimedeanSteps.complexLift F (fun w => (mixedEmbedding F c).2 w * z w)) := by
    exact archDilation_complexCoordinates c f z
  funext y
  have hy := hlift y
  rw [← hy]
  rw [hF, hMfun, hFfun, hgfun, hproduct, ArchimedeanSteps.complex_coefficient A a]
  rw [hchirp]
  simp only [ArchimedeanSteps.productChirp]
  rw [hD, hF, hMfun, hgfun]
  simp only [hb, hc, ArchimedeanSteps.productChirp, ArchimedeanSteps.productDilation,
    ac, mul_assoc]
  rfl

end DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

end

end
