module

public import DedekindZetaZeroFree.LFunctions.Tate.ComplexLocalMellinIdentity
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.TensorTransformsAndLatticeSummability
public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanAdditiveCharacters
public import DedekindZetaZeroFree.LFunctions.Tate.UnitShellFourierIntegrability
public import DedekindZetaZeroFree.LFunctions.Tate.UnitShellFourierNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree
namespace TateTensorProfile

noncomputable section
open scoped Classical NumberField SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local instance archMeasurable : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance archBorel : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

local instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def additiveMeasure : Measure (SLocalProduct F S) :=
  (Measure.map (PoissonArch.infiniteAdeleToSpace F).symm
      (PoissonArch.traceMeasure F)).prod
    (Measure.pi (fun v : S => localNormalizedHaar F v.val))

def modulus (x : SLocalProduct F S) : ℝ :=
  ‖x.1‖ * ∏ v : S, ‖x.2 v‖

def multiplicativeDensityConstant : ℝ :=
  ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces F : ℝ)⁻¹ *
    ∏ v : S,
      ((1 - (TateFiniteShell.q F v.val : ℝ)⁻¹) *
        localHalfDifferentFactor F v.val)⁻¹

def multiplicativeMeasure : Measure (SLocalProduct F S) :=
  ((additiveMeasure F S).restrict {x | IsUnit x}).withDensity
    (fun x => ENNReal.ofReal (multiplicativeDensityConstant F S / modulus F S x))

def fourier (W : SLocalProduct F S → ℂ) (y : SLocalProduct F S) : ℂ :=
  ∫ x, W x * (sLocalTraceCharacter F S (-(x * y)) : ℂ) ∂additiveMeasure F S

def normMellin (W : SLocalProduct F S → ℂ) (s : ℝ) : ℂ :=
  ∫ x, fourier F S W x * ((modulus F S x : ℂ) ^ (s : ℂ))
    ∂multiplicativeMeasure F S

def archTensor (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (x : PoissonArch.Space F) : ℂ :=
  ∏ v, f v ((mixedEmbedding.euclidean.toMixed F x).2 v)

 instance realPlacesEmpty : IsEmpty {v : InfinitePlace F // v.IsReal} :=
  ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr
    (NumberField.IsTotallyComplex.isComplex v.val)) v.property⟩

def coordinateTensor
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (x : SLocalProduct F S) : ℂ :=
  archTensor F f (PoissonArch.infiniteAdeleToSpace F x.1) *
    ∏ v : S, TateFiniteShell.annularTest F v.val (x.2 v)

theorem complexAnnular_zero_not_tsupport (f : ℂ → ℂ) (hf : IsComplexAnnular f) :
    (0 : ℂ) ∉ tsupport f := by
  obtain ⟨a, b, ha, hab, hs⟩ := hf.2.2
  intro h
  have := (hs h).1
  exact (not_le.mpr ha) (by simpa using this)

theorem coordinateTensor_ne_zero
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (hf : ∀ v, f v ≠ 0) : coordinateTensor F S f ≠ 0 := by
  have hpoints : ∀ v, ∃ z, f v z ≠ 0 := by
    intro v
    by_contra h
    exact hf v (funext (by simpa using not_exists.mp h))
  choose z hz using hpoints
  let x : SLocalProduct F S :=
    ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (0, z), fun _ => 1⟩
  have hx : coordinateTensor F S f x ≠ 0 := by
    simp only [coordinateTensor, archTensor, x,
      PoissonArch.infiniteAdeleToSpace_coordinates, RingEquiv.apply_symm_apply]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun v hv => hz v)
    · apply Finset.prod_ne_zero_iff.mpr
      intro v hv
      have hmem := (TateFiniteShell.mem_unitShell_iff F v.val 1).mpr (map_one _)
      simp [TateFiniteShell.annularTest, hmem]
  intro h
  exact hx (congrFun h x)

theorem archTensor_integral_zero
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (v₀ : {v : InfinitePlace F // v.IsComplex})
    (hzero : ∫ z : ℂ, f v₀ z = 0) :
    (∫ x, archTensor F f x ∂PoissonArch.traceMeasure F) = 0 := by
  rw [PoissonArch.traceMeasure, integral_smul_measure]
  have h : (∫ x : PoissonArch.Space F, archTensor F f x) = 0 := by
    unfold archTensor
    rw [(mixedEmbedding.euclidean.volumePreserving_toMixed F).integral_comp
      (mixedEmbedding.euclidean.toMixed F).toHomeomorph.measurableEmbedding
      (fun x => ∏ v, f v (x.2 v))]
    change (∫ x : mixedEmbedding.mixedSpace F, ∏ v, f v (x.2 v)) = 0
    rw [Measure.volume_eq_prod]
    have hi := integral_prod_mul (μ := volume) (ν := volume)
      (fun _ : ({v : InfinitePlace F // v.IsReal} → ℝ) => (1 : ℂ))
      (fun x : ({v : InfinitePlace F // v.IsComplex} → ℂ) => ∏ v, f v (x v))
    simp only [one_mul] at hi
    rw [hi]
    simp_rw [volume_pi]
    rw [integral_fintype_prod_eq_prod]
    rw [Finset.prod_eq_zero (Finset.mem_univ v₀) hzero, mul_zero]
  rw [h, smul_zero]

set_option backward.isDefEq.respectTransparency false in

theorem coordinateTensor_fourier_zero
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (v₀ : {v : InfinitePlace F // v.IsComplex})
    (hzero : ∫ z : ℂ, f v₀ z = 0) :
    fourier F S (coordinateTensor F S f) 0 = 0 := by
  simp only [fourier, mul_zero, neg_zero, AddChar.map_zero_eq_one,
    mul_one]
  simp only [Circle.coe_one, mul_one]
  unfold additiveMeasure coordinateTensor
  rw [integral_prod_mul
    (fun x : InfiniteAdeleRing F => archTensor F f (PoissonArch.infiniteAdeleToSpace F x))
    (fun x : ((v : S) → v.val.adicCompletion F) =>
      ∏ v : S, TateFiniteShell.annularTest F v.val (x v))]
  have harch :
      (∫ x : InfiniteAdeleRing F, archTensor F f (PoissonArch.infiniteAdeleToSpace F x)
        ∂Measure.map (PoissonArch.infiniteAdeleToSpace F).symm (PoissonArch.traceMeasure F)) = 0 := by
    change (∫ x : InfiniteAdeleRing F,
      archTensor F f (PoissonArch.infiniteAdeleToSpace F x)
      ∂Measure.map (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.toMeasurableEquiv
        (PoissonArch.traceMeasure F)) = 0
    rw [integral_map_equiv (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.toMeasurableEquiv]
    convert archTensor_integral_zero F f v₀ hzero using 1
    congr 1
    funext x
    exact congrArg (archTensor F f) ((PoissonArch.infiniteAdeleToSpace F).apply_symm_apply x)
  rw [harch, zero_mul]

theorem archTensor_integral
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ) :
    (∫ x, archTensor F f x ∂PoissonArch.traceMeasure F) =
      (PoissonArch.haarScalar F : ℂ) * ∏ v, ∫ z : ℂ, f v z := by
  rw [PoissonArch.traceMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (PoissonArch.haarScalar_pos F).le]
  change (PoissonArch.haarScalar F : ℂ) * _ = _
  congr 1
  have hm := (mixedEmbedding.euclidean.volumePreserving_toMixed F).integral_comp
    (mixedEmbedding.euclidean.toMixed F).toHomeomorph.measurableEmbedding
    (fun x : mixedEmbedding.mixedSpace F => ∏ v, f v (x.2 v))
  change (∫ x, archTensor F f x) = _ at hm ⊢
  rw [hm]
  have hp := integral_prod_mul
    (μ := (volume : Measure ({v : InfinitePlace F // v.IsReal} → ℝ)))
    (ν := (volume : Measure ({v : InfinitePlace F // v.IsComplex} → ℂ)))
    (fun _ => (1 : ℂ)) (fun x => ∏ v, f v (x v))
  simp only [one_mul] at hp
  rw [Measure.volume_eq_prod]
  rw [hp]
  simp only [integral_const, Measure.real, volume_pi, Measure.pi_univ,
    Finset.prod_of_isEmpty, ENNReal.toReal_one, one_smul, one_mul]
  exact integral_fintype_prod_eq_prod f

 def complexPlacesEquiv : InfinitePlace F ≃ {v : InfinitePlace F // v.IsComplex} where
  toFun v := ⟨v, NumberField.IsTotallyComplex.isComplex v⟩
  invFun v := v.val
  left_inv _ := rfl
  right_inv _ := rfl
private theorem complex_phase (v : {v : InfinitePlace F // v.IsComplex})
    (x y : InfiniteAdeleRing F) :
    (archTraceCharacter v.val ((-(x * y)) v.val) : ℂ) =
      Complex.exp (((-4 * Real.pi *
        (((InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 v) *
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F y).2 v)).re : ℝ) : ℂ) * Complex.I) := by
  rw [archTraceCharacter_of_isComplex v.val v.property, Circle.coe_exp]
  simp only [Pi.neg_apply, Pi.mul_apply, map_neg, map_mul,
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply, Complex.neg_re,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change Complex.exp (↑(2 * Real.pi * (2 *
    ((InfinitePlace.Completion.extensionEmbedding v.val) (-(x v.val * y v.val))).re)) * Complex.I) = _
  simp only [map_neg, map_mul, Complex.neg_re]
  congr 2
  push_cast
  ring
private theorem arch_phase (x y : InfiniteAdeleRing F) :
    (∏ v : InfinitePlace F, (archTraceCharacter v ((-(x*y)) v) : ℂ)) =
      ∏ v : {v : InfinitePlace F // v.IsComplex},
        Complex.exp (((-4 * Real.pi *
          (((InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 v) *
            ((InfiniteAdeleRing.ringEquiv_mixedSpace F y).2 v)).re : ℝ) : ℂ) * Complex.I) := by
  apply Fintype.prod_equiv (complexPlacesEquiv F)
  intro v
  exact complex_phase F (complexPlacesEquiv F v) x y

theorem archTensor_traceFourier
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (y : PoissonArch.Space F) :
    PoissonArch.traceFourier F (archTensor F f) y =
      ∏ v, complexTraceFourier (f v) ((mixedEmbedding.euclidean.toMixed F y).2 v) := by
  have hphase (x : PoissonArch.Space F) :
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (PoissonArch.tracePairing F x y : ℂ)) =
        ∏ v : {v : InfinitePlace F // v.IsComplex},
          Complex.exp (((-4 * Real.pi *
            (((mixedEmbedding.euclidean.toMixed F x).2 v) *
              ((mixedEmbedding.euclidean.toMixed F y).2 v)).re : ℝ) : ℂ) * Complex.I) := by
    rw [PoissonArch.tracePairing]
    simp only [Finset.sum_of_isEmpty, zero_add]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  unfold PoissonArch.traceFourier
  simp_rw [hphase, archTensor, ← Finset.prod_mul_distrib]
  change (∫ x, archTensor F (fun v z => f v z *
    Complex.exp (↑(-4 * Real.pi * (z * (mixedEmbedding.euclidean.toMixed F y).2 v).re) * Complex.I)) x
    ∂PoissonArch.traceMeasure F) = _
  rw [archTensor_integral]
  simp only [complexTraceFourier, Finset.prod_mul_distrib, Finset.prod_const,
    PoissonArch.haarScalar, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rfl
set_option backward.isDefEq.respectTransparency false in

theorem coordinateTensor_fourier
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (y : SLocalProduct F S) :
    fourier F S (coordinateTensor F S f) y =
      (∏ v, complexTraceFourier (f v)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F y.1).2 v)) *
      ∏ v : S, TateFiniteShell.fourier F v.val (localFiniteCharacter F v.val)
        (localNormalizedHaar F v.val) (TateFiniteShell.annularTest F v.val) (y.2 v) := by
  have hcoe {ι : Type} (t : Finset ι) (g : ι → Circle) :
      ((∏ i ∈ t, g i : Circle) : ℂ) = ∏ i ∈ t, (g i : ℂ) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih => simp [hi, Circle.coe_mul, ih]
  have hfactor (x : SLocalProduct F S) :
      coordinateTensor F S f x * (sLocalTraceCharacter F S (-(x * y)) : ℂ) =
      (archTensor F f (PoissonArch.infiniteAdeleToSpace F x.1) *
        ∏ v : InfinitePlace F, (archTraceCharacter v (-(x.1 v * y.1 v)) : ℂ)) *
      ∏ v : S, (TateFiniteShell.annularTest F v.val (x.2 v) *
        (localFiniteCharacter F v.val (-(x.2 v * y.2 v)) : ℂ)) := by
    rw [sLocalTraceCharacter_apply]
    simp only [Circle.coe_mul, SubmonoidClass.coe_finset_prod, coordinateTensor,
      Prod.fst_neg, Prod.fst_mul, Prod.snd_neg, Prod.snd_mul, Pi.neg_apply, Pi.mul_apply,
      Finset.prod_mul_distrib]
    simp only [hcoe]
    change (archTensor F f (PoissonArch.infiniteAdeleToSpace F x.1) *
      ∏ v : S, TateFiniteShell.annularTest F v.val (x.2 v)) *
        ((∏ v : InfinitePlace F, (archTraceCharacter v (-(x.1 v * y.1 v)) : ℂ)) *
        (∏ v : S, (localFiniteCharacter F v.val (-(x.2 v * y.2 v)) : ℂ))) = _
    ring
  unfold fourier additiveMeasure
  simp_rw [hfactor]
  rw [integral_prod_mul
    (fun x : InfiniteAdeleRing F => archTensor F f (PoissonArch.infiniteAdeleToSpace F x) *
      ∏ v : InfinitePlace F, (archTraceCharacter v (-(x v * y.1 v)) : ℂ))
    (fun x : ((v : S) → v.val.adicCompletion F) =>
      ∏ v : S, TateFiniteShell.annularTest F v.val (x v) *
        (localFiniteCharacter F v.val (-(x v * y.2 v)) : ℂ))]
  rw [integral_fintype_prod_eq_prod
    (μ := fun v : S => localNormalizedHaar F v.val)
    (fun (v : S) (x : v.val.adicCompletion F) =>
      TateFiniteShell.annularTest F v.val x *
        (localFiniteCharacter F v.val (-(x * y.2 v)) : ℂ))]
  congr 1
  swap
  · simp only [TateFiniteShell.fourier, neg_mul]
  have hap (x : InfiniteAdeleRing F) :
      (∏ v : InfinitePlace F, (archTraceCharacter v (-(x v * y.1 v)) : ℂ)) =
        ∏ v : {v : InfinitePlace F // v.IsComplex},
          Complex.exp (↑(-4 * Real.pi *
            (((InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 v) *
              ((InfiniteAdeleRing.ringEquiv_mixedSpace F y.1).2 v)).re) * Complex.I) :=
    arch_phase F x y.1
  simp_rw [hap]
  have he : MeasurableEmbedding ((PoissonArch.infiniteAdeleToSpace F).symm :
      PoissonArch.Space F → InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.measurableEmbedding
  rw [he.integral_map]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  have hy := PoissonArch.infiniteAdeleToSpace_coordinates F y.1
  have hx (x : PoissonArch.Space F) :
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((PoissonArch.infiniteAdeleToSpace F).symm x) =
        mixedEmbedding.euclidean.toMixed F x := by
    rw [← PoissonArch.infiniteAdeleToSpace_coordinates,
      ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [hx, ← hy]
  rw [← archTensor_traceFourier]
  unfold PoissonArch.traceFourier
  congr 1
  funext x
  congr 1
  rw [PoissonArch.tracePairing]
  simp only [Finset.sum_of_isEmpty, zero_add]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem modulus_nonneg (x : SLocalProduct F S) : 0 ≤ modulus F S x := by
  exact mul_nonneg
    (by rw [InfiniteAdeleRing.norm_def]; positivity)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _))

theorem modulus_measurable : Measurable (modulus F S) := by
  unfold modulus
  apply Measurable.mul
  · simp only [InfiniteAdeleRing.norm_def]
    apply Finset.measurable_prod
    intro v hv
    have hm : Measurable (fun x : InfiniteAdeleRing F => ‖x v‖) :=
      (continuous_apply v).norm.measurable
    exact (hm.comp measurable_fst).pow_const v.mult
  · apply Finset.measurable_prod
    intro v hv
    exact ((measurable_pi_apply v).comp measurable_snd).norm

theorem multiplicativeDensityConstant_pos : 0 < multiplicativeDensityConstant F S := by
  unfold multiplicativeDensityConstant
  apply mul_pos
  · exact inv_pos.mpr (pow_pos (mul_pos (by norm_num) Real.pi_pos) _)
  · apply Finset.prod_pos
    intro v hv
    apply inv_pos.mpr
    apply mul_pos _ (localHalfDifferentFactor_pos F v.val)
    apply sub_pos.mpr
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast finiteCompletion_residueCard_gt_one F v.val

theorem multiplicative_integral (g : SLocalProduct F S → ℂ) :
    (∫ x, g x ∂multiplicativeMeasure F S) =
      ∫ x in {x | IsUnit x},
        (multiplicativeDensityConstant F S / modulus F S x) • g x
        ∂additiveMeasure F S := by
  unfold multiplicativeMeasure
  have hd : Measurable (fun x : SLocalProduct F S =>
      ENNReal.ofReal (multiplicativeDensityConstant F S / modulus F S x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (modulus_measurable F S))
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g]
  simp only [ENNReal.toReal_ofReal (div_nonneg
    (multiplicativeDensityConstant_pos F S).le (modulus_nonneg F S _))]

theorem modulus_pos_of_isUnit (x : SLocalProduct F S) (hx : IsUnit x) :
    0 < modulus F S x := by
  obtain ⟨ha, hb⟩ := Prod.isUnit_iff.mp hx
  unfold modulus
  apply mul_pos
  · rw [InfiniteAdeleRing.norm_def]
    apply Finset.prod_pos
    intro v hv
    apply pow_pos
    exact norm_pos_iff.mpr (isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp ha v))
  · apply Finset.prod_pos
    intro v hv
    exact norm_pos_iff.mpr (isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp hb v))

theorem normMellin_additive_integral
    (W : SLocalProduct F S → ℂ) (s : ℝ) :
    normMellin F S W s =
      ∫ x in {x | IsUnit x},
        (multiplicativeDensityConstant F S / modulus F S x) •
          (fourier F S W x * (modulus F S x ^ s : ℝ))
        ∂additiveMeasure F S := by
  unfold normMellin
  rw [multiplicative_integral]
  simp_rw [← Complex.ofReal_cpow (modulus_nonneg F S _)]

theorem modulus_pos_iff (x : SLocalProduct F S) : 0 < modulus F S x ↔ IsUnit x := by
  refine ⟨?_, modulus_pos_of_isUnit F S x⟩
  intro hx
  apply Prod.isUnit_iff.mpr
  constructor
  · apply Pi.isUnit_iff.mpr
    intro v
    apply isUnit_iff_ne_zero.mpr
    intro hv
    have hn : ‖x.1‖ = 0 := by
      rw [InfiniteAdeleRing.norm_def]
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      rw [hv, norm_zero]
      exact zero_pow (by
        unfold InfinitePlace.mult
        split_ifs <;> norm_num)
    simpa [modulus, hn] using hx
  · apply Pi.isUnit_iff.mpr
    intro v
    apply isUnit_iff_ne_zero.mpr
    intro hv
    have hn : (∏ v : S, ‖x.2 v‖) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
    change 0 < ‖x.1‖ * (∏ v : S, ‖x.2 v‖) at hx
    rw [hn, mul_zero] at hx
    exact (lt_irrefl 0) hx

theorem measurableSet_units : MeasurableSet {x : SLocalProduct F S | IsUnit x} := by
  have heq : {x : SLocalProduct F S | IsUnit x} = {x | 0 < modulus F S x} := by
    ext x
    exact (modulus_pos_iff F S x).symm
  rw [heq]
  exact measurableSet_lt measurable_const (modulus_measurable F S)

theorem normMellin_weighted_additive
    (W : SLocalProduct F S → ℂ) (s : ℝ) :
    normMellin F S W s = multiplicativeDensityConstant F S •
      ∫ x in {x | IsUnit x}, fourier F S W x * (modulus F S x ^ (s - 1) : ℝ)
        ∂additiveMeasure F S := by
  rw [normMellin_additive_integral, ← integral_smul]
  apply setIntegral_congr_fun (measurableSet_units F S)
  intro x hx
  dsimp only
  rw [Real.rpow_sub_one (modulus_pos_of_isUnit F S x hx).ne']
  simp only [Complex.real_smul, Complex.ofReal_div]
  ring

theorem modulus_rpow (x : SLocalProduct F S) (r : ℝ) :
    modulus F S x ^ r = ‖x.1‖ ^ r * ∏ v : S, ‖x.2 v‖ ^ r := by
  rw [modulus, Real.mul_rpow
    (by rw [InfiniteAdeleRing.norm_def]; positivity)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _))]
  congr 1
  exact (Real.finset_prod_rpow Finset.univ (fun v : S => ‖x.2 v‖)
    (fun _ _ => norm_nonneg _) r).symm

theorem weighted_tensor_integral
    (gArch : InfiniteAdeleRing F → ℂ)
    (g : (v : S) → v.val.adicCompletion F → ℂ) (r : ℝ) :
    (∫ x in {x : SLocalProduct F S | IsUnit x},
      (gArch x.1 * ∏ v : S, g v (x.2 v)) * (modulus F S x ^ r : ℝ)
      ∂additiveMeasure F S) =
    (∫ a in {a : InfiniteAdeleRing F | IsUnit a},
      gArch a * (‖a‖ ^ r : ℝ)
      ∂Measure.map (PoissonArch.infiniteAdeleToSpace F).symm (PoissonArch.traceMeasure F)) *
    ∏ v : S, ∫ z in ({0}ᶜ : Set (v.val.adicCompletion F)),
      g v z * (‖z‖ ^ r : ℝ) ∂localNormalizedHaar F v.val := by
  letI : SFinite (PoissonArch.traceMeasure F) := by
    unfold PoissonArch.traceMeasure
    infer_instance
  have hset : {x : SLocalProduct F S | IsUnit x} =
      {a : InfiniteAdeleRing F | IsUnit a} ×ˢ
      Set.pi Set.univ (fun v : S => ({0}ᶜ : Set (v.val.adicCompletion F))) := by
    ext x
    simp [Prod.isUnit_iff, Pi.isUnit_iff, isUnit_iff_ne_zero]
  have hfactor (x : SLocalProduct F S) :
      (gArch x.1 * ∏ v : S, g v (x.2 v)) * (modulus F S x ^ r : ℝ) =
      (gArch x.1 * (‖x.1‖ ^ r : ℝ)) *
        ∏ v : S, (g v (x.2 v) * (‖x.2 v‖ ^ r : ℝ)) := by
    rw [modulus_rpow]
    push_cast
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hfactor]
  rw [hset, additiveMeasure, setIntegral_prod_mul
    (fun a : InfiniteAdeleRing F => gArch a * (‖a‖ ^ r : ℝ))
    (fun z : (v : S) → v.val.adicCompletion F => ∏ v, g v (z v) * (‖z v‖ ^ r : ℝ))]
  congr 1
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (fun v z => g v z * (‖z‖ ^ r : ℝ))

theorem coordinateTensor_normMellin_product
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ) (s : ℝ) :
    normMellin F S (coordinateTensor F S f) s = multiplicativeDensityConstant F S •
      ((∫ a in {a : InfiniteAdeleRing F | IsUnit a},
        ((∏ v, complexTraceFourier (f v)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v)) * (‖a‖ ^ (s - 1) : ℝ))
        ∂Measure.map (PoissonArch.infiniteAdeleToSpace F).symm (PoissonArch.traceMeasure F)) *
      ∏ v : S, ∫ z in ({0}ᶜ : Set (v.val.adicCompletion F)),
        TateFiniteShell.fourier F v.val (localFiniteCharacter F v.val)
          (localNormalizedHaar F v.val) (TateFiniteShell.annularTest F v.val) z *
          (‖z‖ ^ (s - 1) : ℝ) ∂localNormalizedHaar F v.val) := by
  rw [normMellin_weighted_additive]
  simp_rw [coordinateTensor_fourier F S f]
  exact congrArg (fun z : ℂ => multiplicativeDensityConstant F S • z)
    (weighted_tensor_integral F S
      (fun a => ∏ v, complexTraceFourier (f v)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v))
      (fun v => TateFiniteShell.fourier F v.val (localFiniteCharacter F v.val)
        (localNormalizedHaar F v.val) (TateFiniteShell.annularTest F v.val)) (s - 1))

theorem arch_norm_coordinates (a : InfiniteAdeleRing F) :
    ‖a‖ = ∏ v : {v : InfinitePlace F // v.IsComplex},
      ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v‖ ^ 2 := by
  rw [InfiniteAdeleRing.norm_def]
  apply Fintype.prod_equiv (complexPlacesEquiv F)
  intro v
  have hv := NumberField.IsTotallyComplex.isComplex v
  change ‖a v‖ ^ v.mult = ‖InfinitePlace.Completion.extensionEmbedding v (a v)‖ ^ 2
  rw [show v.mult = 2 from InfinitePlace.mult_isComplex ⟨v, hv⟩]
  have he := InfinitePlace.Completion.isometry_extensionEmbedding v
  have hz : InfinitePlace.Completion.extensionEmbedding v 0 = 0 := map_zero _
  have hn := he.dist_eq (a v) 0
  simpa only [dist_zero_right, hz] using congrArg (fun r : ℝ => r ^ 2) hn.symm

theorem arch_weighted_integral
    (g : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (s : ℝ) (hs : s ≠ 1) :
    (∫ a in {a : InfiniteAdeleRing F | IsUnit a},
      (∏ v, g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v)) * (‖a‖ ^ (s - 1) : ℝ)
      ∂Measure.map (PoissonArch.infiniteAdeleToSpace F).symm (PoissonArch.traceMeasure F)) =
      (PoissonArch.haarScalar F : ℂ) *
        ∏ v, ∫ z : ℂ, complexNormMellinIntegrand (g v) s z := by
  have hz : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hvanish (a : InfiniteAdeleRing F) (ha : a ∉ {a | IsUnit a}) :
      (∏ v, g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v)) *
        (‖a‖ ^ (s - 1) : ℝ) = 0 := by
    rw [InfiniteAdeleRing.norm_eq_zero_of_not_isUnit ha, Real.zero_rpow hz,
      Complex.ofReal_zero, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
  have he : MeasurableEmbedding ((PoissonArch.infiniteAdeleToSpace F).symm :
      PoissonArch.Space F → InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.measurableEmbedding
  rw [he.integral_map]
  have hfactor (a : InfiniteAdeleRing F) :
      (∏ v, g v ((InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v)) * (‖a‖ ^ (s - 1) : ℝ) =
      ∏ v, complexNormMellinIntegrand (g v) s
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F a).2 v) := by
    rw [arch_norm_coordinates,
      ← Real.finset_prod_rpow Finset.univ _ (fun _ _ => sq_nonneg _) (s - 1)]
    push_cast
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    unfold complexNormMellinIntegrand
    split_ifs with h
    · rw [h, norm_zero, zero_pow (by norm_num), Real.zero_rpow hz,
        Complex.ofReal_zero, mul_zero]
    · rfl
  simp_rw [hfactor]
  have hc (x : PoissonArch.Space F) :
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((PoissonArch.infiniteAdeleToSpace F).symm x) =
        mixedEmbedding.euclidean.toMixed F x := by
    rw [← PoissonArch.infiniteAdeleToSpace_coordinates,
      ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [hc]
  exact archTensor_integral F (fun v => complexNormMellinIntegrand (g v) s)

theorem coordinateTensor_normMellin_ne_zero_of_factors
    (f : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (s : ℝ) (hs : s ≠ 1)
    (ha : ∀ v, complexNormMellin (complexTraceFourier (f v)) s ≠ 0)
    (hg : ∀ v : S, (∫ z in ({0}ᶜ : Set (v.val.adicCompletion F)),
      TateFiniteShell.fourier F v.val (localFiniteCharacter F v.val)
        (localNormalizedHaar F v.val) (TateFiniteShell.annularTest F v.val) z *
        (‖z‖ ^ (s - 1) : ℝ) ∂localNormalizedHaar F v.val) ≠ 0) :
    normMellin F S (coordinateTensor F S f) s ≠ 0 := by
  rw [coordinateTensor_normMellin_product,
    arch_weighted_integral F (fun v => complexTraceFourier (f v)) s hs]
  simp only [Complex.real_smul]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (multiplicativeDensityConstant_pos F S).ne'
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr (PoissonArch.haarScalar_pos F).ne'
      · apply Finset.prod_ne_zero_iff.mpr
        intro v hv
        intro hz
        apply ha v
        simp only [complexNormMellin, hz, mul_zero]
    · exact Finset.prod_ne_zero_iff.mpr (fun v _ => hg v)

end
end TateTensorProfile
end DedekindZetaZeroFree

section

namespace DedekindZetaZeroFree
namespace TateTensorProfile

noncomputable section
open scoped Classical NumberField SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem archTensor_integrable_of_factors
    (g : (v : {v : InfinitePlace F // v.IsComplex}) → ℂ → ℂ)
    (hg : ∀ v, Integrable (g v) (volume : Measure ℂ)) :
    Integrable (archTensor F g) (PoissonArch.traceMeasure F) := by
  have hp := Integrable.fintype_prod_dep hg
  have ha : Integrable (fun _ : {v : InfinitePlace F // v.IsReal} → ℝ => (1 : ℂ)) volume := by
    apply integrable_const_iff.mpr
    right
    constructor
    simp only [volume_pi, Measure.pi_univ, Finset.prod_of_isEmpty]
    exact ENNReal.one_lt_top
  have hi := ha.mul_prod hp
  simp only [one_mul] at hi
  rw [← volume_pi, ← Measure.volume_eq_prod] at hi
  have hm := (mixedEmbedding.euclidean.volumePreserving_toMixed F).integrable_comp_emb
    (mixedEmbedding.euclidean.toMixed F).toHomeomorph.measurableEmbedding
    (g := fun x : mixedEmbedding.mixedSpace F => ∏ v, g v (x.2 v))
  exact (hm.mpr hi).smul_measure ENNReal.ofReal_ne_top

end
end TateTensorProfile
end DedekindZetaZeroFree

end
