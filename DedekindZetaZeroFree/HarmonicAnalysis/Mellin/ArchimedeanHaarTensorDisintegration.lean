module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LocalUnitsTensorIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.RadialIsolation
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

abbrev RemainingCoordinates {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F) :=
  ((w : {w : InfinitePlace F // w ≠ v}) → w.val.Completionˣ) ×
    ((w : S) → (w.val.adicCompletion F)ˣ)

local instance {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F) :
    MeasurableSpace (RemainingCoordinates S v) := borel _

 local instance instBorelSpaceHaarDisintegrationRealUnits : BorelSpace ℝˣ := ⟨by
  change MeasurableSpace.comap Units.val (borel ℝ) = borel ℝˣ
  rw [Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
private theorem real_addHaar_map_mul (μ : Measure ℝ) [μ.IsAddHaarMeasure] (c : ℝ) (hc : c ≠ 0) :
    μ.map (fun x => c*x) = (ENNReal.ofReal |c|)⁻¹ • μ := by
  let L : ℝ →ₗ[ℝ] ℝ := LinearMap.mulLeft ℝ c
  have hdet : L.det = c := by
    exact LinearMap.det_mulLeft _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ
    (f := L) (by rwa [hdet])
  convert hmap using 1
  · rfl
  · rw [hdet, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hc)]

private theorem realUnits_density_left (μ : Measure ℝ) [μ.IsAddHaarMeasure] :
    (Measure.comap Units.val
      (μ.withDensity (fun x : ℝ => ENNReal.ofReal (|x|⁻¹)))).IsMulLeftInvariant := by
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ)).measurableEmbedding
  let D := fun x : ℝ => ENNReal.ofReal (|x|⁻¹)
  have hD : Measurable D := by dsimp [D]; fun_prop
  constructor
  intro g
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  change (μ.withDensity D).comap Units.val ((fun x => g * x) ⁻¹' s) =
    (μ.withDensity D).comap Units.val s
  rw [ev.comap_apply, ev.comap_apply]
  have hpre : Units.val '' ((fun x => g * x) ⁻¹' s) =
      (fun x : ℝ => (g : ℝ) * x) ⁻¹' (Units.val '' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨g * u, hu, by simp⟩
    · rintro ⟨u, hu, he⟩
      refine ⟨g⁻¹ * u, ?_, ?_⟩
      · simpa using hu
      · change ((g⁻¹ * u : ℝˣ) : ℝ) = x
        simp only [Units.val_mul]
        rw [he]; simp
  rw [hpre, withDensity_apply _ (by exact (ev.measurableSet_image.mpr hs).preimage (by fun_prop)),
    withDensity_apply _ (ev.measurableSet_image.mpr hs)]
  have hscale := real_addHaar_map_mul μ (g : ℝ) g.ne_zero
  have hmul (x : ℝ) : D ((g : ℝ) * x) = (ENNReal.ofReal |(g : ℝ)|)⁻¹ * D x := by
    dsimp [D]
    rw [abs_mul, mul_inv, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_inv_of_pos (abs_pos.mpr g.ne_zero)]
  have hm := setLIntegral_map (μ := μ) (g := fun x : ℝ => (g : ℝ) * x)
    (s := Units.val '' s) (ev.measurableSet_image.mpr hs) hD (by fun_prop)
  rw [hscale, Measure.restrict_smul, lintegral_smul_measure] at hm
  simp only [ENNReal.smul_def, smul_eq_mul] at hm
  simp_rw [hmul] at hm
  rw [lintegral_const_mul _ hD] at hm
  exact (ENNReal.mul_right_inj (by simp) (by simp [abs_pos.mpr g.ne_zero])).mp hm.symm

private theorem realUnits_density_isHaarMeasure (μ : Measure ℝ) [μ.IsAddHaarMeasure] :
    (Measure.comap Units.val
      (μ.withDensity (fun x : ℝ => ENNReal.ofReal (|x|⁻¹)))).IsHaarMeasure := by
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ)).measurableEmbedding
  let D := fun x : ℝ => ENNReal.ofReal (|x|⁻¹)
  have hD : Measurable D := by dsimp [D]; fun_prop
  letI := realUnits_density_left μ
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds (1 : ℝˣ)
  have hint : (interior K).Nonempty := ⟨1, mem_interior_iff_mem_nhds.mpr hKmem⟩
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK hint
  · rw [ev.comap_apply]
    change (μ.withDensity D) (Units.val '' K) ≠ 0
    apply mt (withDensity_apply_eq_zero (μ := μ) (s := Units.val '' K) hD).mp
    have heq : {x | D x ≠ 0} ∩ (Units.val '' K) = Units.val '' K := by
      apply Set.inter_eq_right.mpr
      rintro x ⟨u, hu, rfl⟩
      exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (abs_pos.mpr u.ne_zero))).ne'
    rw [heq]
    have hpos : 0 < μ (Units.val '' interior K) :=
      (IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ isOpen_interior).measure_pos μ
        (hint.image _)
    exact (hpos.trans_le (measure_mono (Set.image_mono interior_subset))).ne'
  · rw [ev.comap_apply, withDensity_apply _ ((hK.image Units.continuous_val).measurableSet)]
    have hc : ContinuousOn (fun x : ℝ => |x|⁻¹) (Units.val '' K) := by
      apply ContinuousOn.inv₀ (by fun_prop)
      rintro x ⟨u, hu, rfl⟩
      exact (abs_pos.mpr u.ne_zero).ne'
    have hi := ContinuousOn.integrableOn_compact (μ := μ) (hK.image Units.continuous_val) hc
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => by positivity))]
    exact ENNReal.ofReal_ne_top

private theorem realUnits_density_integral (f : ℝ → ℂ) :
    (∫ u : ℝˣ, f u.val ∂Measure.comap Units.val
      (volume.withDensity (fun x : ℝ => ENNReal.ofReal (|x|⁻¹)))) =
      ∫ x : ℝ, f x / ((|x| : ℝ) : ℂ) := by
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ)).measurableEmbedding
  rw [← ev.integral_map, ev.map_comap]
  have hrange : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩; exact u.ne_zero
    · intro hx; exact ⟨Units.mk0 x hx, rfl⟩
  rw [hrange]
  have hz : (volume.withDensity (fun x : ℝ => ENNReal.ofReal (|x|⁻¹))) {0} = 0 :=
    withDensity_absolutelyContinuous _ _ (measure_singleton 0)
  rw [Measure.restrict_eq_self_of_ae_mem]
  · rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    simp only [Complex.real_smul, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp [ENNReal.toReal_ofReal (by positivity : 0 ≤ |x|⁻¹), div_eq_mul_inv, mul_comm]
  · simpa only [ae_iff, Set.mem_compl_iff, not_not, Set.setOf_mem_eq] using hz

theorem realUnits_haar_integral_density (ν : Measure ℝˣ) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℂ,
      (∫ u : ℝˣ, f u.val ∂ν) = c • (∫ x : ℝ, f x / ((|x| : ℝ) : ℂ)) := by
  letI : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ : Measure ℝˣ := Measure.comap Units.val
    (volume.withDensity (fun x : ℝ => ENNReal.ofReal (|x|⁻¹)))
  letI : μ.IsHaarMeasure := realUnits_density_isHaarMeasure volume
  refine ⟨(ν.haarScalarFactor μ : ℝ), ?_, ?_⟩
  · exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ
  · intro f
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul ν μ, integral_smul_nnreal_measure]
    congr 1
    exact realUnits_density_integral f

 local instance instBorelSpaceHaarDisintegrationComplexUnits : BorelSpace ℂˣ := ⟨by
  change MeasurableSpace.comap Units.val (borel ℂ) = borel ℂˣ
  rw [Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
private theorem complexUnits_density_integral (f : ℂ → ℂ) :
    (∫ u : ℂˣ, f u.val ∂Measure.comap Units.val
      (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Real.pi * ‖z‖ ^ 2)⁻¹)))) =
      (Real.pi : ℂ)⁻¹ * (∫ z : ℂ, f z / ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℂ)).measurableEmbedding
  rw [← ev.integral_map, ev.map_comap]
  have hrange : Set.range (Units.val : ℂˣ → ℂ) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩; exact u.ne_zero
    · intro hx; exact ⟨Units.mk0 x hx, rfl⟩
  rw [hrange]
  have hz : (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Real.pi * ‖z‖ ^ 2)⁻¹))) {0} = 0 :=
    withDensity_absolutelyContinuous _ _ (measure_singleton 0)
  rw [Measure.restrict_eq_self_of_ae_mem]
  · rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top), ← integral_const_mul]
    simp only [Complex.real_smul, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp [div_eq_mul_inv, mul_inv, mul_comm, mul_assoc, mul_left_comm]
  · simpa only [ae_iff, Set.mem_compl_iff, not_not, Set.setOf_mem_eq] using hz

theorem complexUnits_haar_integral_density (ν : Measure ℂˣ) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℂ → ℂ,
      (∫ u : ℂˣ, f u.val ∂ν) = c • (∫ z : ℂ, f z / ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ : Measure ℂˣ := Measure.comap Units.val
    (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Real.pi * ‖z‖ ^ 2)⁻¹)))
  letI : μ.IsHaarMeasure := ProbeSheetFourierMellinBounds.complexUnits_density_isHaarMeasure volume
  refine ⟨(ν.haarScalarFactor μ : ℝ) / Real.pi, ?_, ?_⟩
  · exact div_pos (by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ)
      Real.pi_pos
  · intro f
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul ν μ, integral_smul_nnreal_measure]
    rw [show (∫ u : ℂˣ, f u.val ∂μ) = _ from complexUnits_density_integral f]
    simp [NNReal.smul_def, Complex.real_smul, smul_eq_mul, div_eq_mul_inv, mul_assoc]
 def rawProdUnits (M N : Type*) [Monoid M] [Monoid N]
    [TopologicalSpace M] [TopologicalSpace N] : (M × N)ˣ ≃ₜ* Mˣ × Nˣ where
  __ := MulEquiv.prodUnits
  continuous_toFun := Homeomorph.prodUnits.continuous
  continuous_invFun := Homeomorph.prodUnits.symm.continuous
 def rawProdCongr {M N P Q : Type*} [Monoid M] [Monoid N] [Monoid P] [Monoid Q]
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] [TopologicalSpace Q]
    (e : M ≃ₜ* N) (f : P ≃ₜ* Q) : M × P ≃ₜ* N × Q where
  __ := e.toMulEquiv.prodCongr f.toMulEquiv
  continuous_toFun := e.continuous.prodMap f.continuous
  continuous_invFun := e.symm.continuous.prodMap f.symm.continuous
 def rawSplitAt {ι : Type*} [DecidableEq ι] (M : ι → Type*)
    [∀ i, Monoid (M i)] [∀ i, TopologicalSpace (M i)] (i : ι) :
    ((j : ι) → M j) ≃ₜ* M i × ((j : {j : ι // j ≠ i}) → M j) where
  toEquiv := Equiv.piSplitAt i M
  map_mul' := by intro x y; rfl
  continuous_toFun := (Homeomorph.piSplitAt i M).continuous
  continuous_invFun := (Homeomorph.piSplitAt i M).symm.continuous
 def rawAssoc (M N P : Type*) [Monoid M] [Monoid N] [Monoid P]
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] :
    (M × N) × P ≃ₜ* M × (N × P) where
  toEquiv := Equiv.prodAssoc M N P
  map_mul' := by intro x y; rfl
  continuous_toFun := (Homeomorph.prodAssoc M N P).continuous
  continuous_invFun := (Homeomorph.prodAssoc M N P).symm.continuous

def rawCompletionIsolation {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F) :
    (SLocalProduct F S)ˣ ≃ₜ* v.Completionˣ × RemainingCoordinates S v :=
  ((rawProdUnits _ _).trans
    (rawProdCongr ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits)).trans
      ((rawProdCongr (rawSplitAt (fun w : InfinitePlace F => w.Completionˣ) v)
        (ContinuousMulEquiv.refl _)).trans (rawAssoc _ _ _))
@[simp] theorem rawCompletionIsolation_fst {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F)
    (y : (SLocalProduct F S)ˣ) :
    ((rawCompletionIsolation S v y).1).val = y.val.1 v := rfl
@[simp] theorem rawCompletionIsolation_remaining_arch {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F)
    (y : (SLocalProduct F S)ˣ) (w : {w : InfinitePlace F // w ≠ v}) :
    (((rawCompletionIsolation S v y).2).1 w).val = y.val.1 w := rfl
@[simp] theorem rawCompletionIsolation_remaining_finite {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F)
    (y : (SLocalProduct F S)ˣ) (w : S) :
    (((rawCompletionIsolation S v y).2).2 w).val = y.val.2 w := rfl

def remainingModulus {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F)
    (p : RemainingCoordinates S v) : ℝ :=
  (∏ w : {w : InfinitePlace F // w ≠ v}, ‖(p.1 w).val‖ ^ 2) *
    ∏ w : S, ‖(p.2 w).val‖

theorem remainingModulus_pos {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F)
    (p : RemainingCoordinates S v) : 0 < remainingModulus S v p := by
  apply mul_pos
  · exact Finset.prod_pos fun w _ => pow_pos (Units.norm_pos (p.1 w)) _
  · exact Finset.prod_pos fun w _ => Units.norm_pos (p.2 w)

theorem remainingModulus_continuous {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F) :
    Continuous (remainingModulus S v) := by
  unfold remainingModulus
  fun_prop

theorem remainingLogModulus_measurable {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F) :
    Measurable (fun p => Real.log (remainingModulus S v p)) := by
  letI : BorelSpace (RemainingCoordinates S v) := ⟨rfl⟩
  exact Real.measurable_log.comp (remainingModulus_continuous S v).measurable

theorem rawCompletionIsolation_modulus {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F)
    (y : (SLocalProduct F S)ˣ) :
    ProbeWeight.modulus F S y = ‖y.val.1 v‖ ^ 2 *
      remainingModulus S v (rawCompletionIsolation S v y).2 := by
  unfold ProbeWeight.modulus remainingModulus
  simp only [rawCompletionIsolation_remaining_arch, rawCompletionIsolation_remaining_finite]
  rw [Fintype.prod_eq_mul_prod_compl v]
  have he : (∏ w ∈ ({v}ᶜ : Finset (InfinitePlace F)), ‖y.val.1 w‖ ^ 2) =
      ∏ w : {w : InfinitePlace F // w ≠ v}, ‖y.val.1 w‖ ^ 2 := by
    exact Finset.prod_subtype _ (by simp) _
  rw [he]
  ring

theorem rawCompletionIsolation_log_modulus {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F)
    (y : (SLocalProduct F S)ˣ) :
    Real.log (ProbeWeight.modulus F S y) = Real.log (‖y.val.1 v‖ ^ 2) +
      Real.log (remainingModulus S v (rawCompletionIsolation S v y).2) := by
  rw [rawCompletionIsolation_modulus, Real.log_mul]
  · exact pow_ne_zero _ (Units.norm_pos (rawCompletionIsolation S v y).1).ne'
  · exact (remainingModulus_pos S v _).ne'

theorem isolate_integral_of_scaled_product
    {G X Y : Type*} [MeasurableSpace G] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure G) (μ : Measure X) (η : Measure Y) [SFinite μ] [SFinite η]
    (e : G ≃ᵐ X × Y) (c : NNReal)
    (he : MeasurePreserving e ν (c • (μ.prod η)))
    (f : G → ℂ) (b : X → ℂ) (a : Y → ℂ)
    (hb : Integrable b μ) (ha : Integrable a η)
    (L : G → ℝ) (LX : X → ℝ) (LY : Y → ℝ)
    (hLX : Measurable LX) (hLY : Measurable LY)
    (hf : ∀ y, f y = b (e y).1 * a (e y).2)
    (hL : ∀ y, L y = LX (e y).1 + LY (e y).2)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (hbound : ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) :
    (∫ y, f y * φ (L y) ∂ν) =
      ∫ p, ((c : ℂ) * a p) * (∫ x, b x * φ (LX x + LY p) ∂μ) ∂η := by
  obtain ⟨C, hC⟩ := hbound
  have hprod : Integrable
      (fun p : X × Y => (b p.1 * a p.2) * φ (LX p.1 + LY p.2)) (μ.prod η) :=
    (hb.mul_prod ha).mul_bdd
      (hφ.measurable.comp ((hLX.comp measurable_fst).add
        (hLY.comp measurable_snd))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC _)
  calc
    _ = ∫ y, (b (e y).1 * a (e y).2) * φ (LX (e y).1 + LY (e y).2) ∂ν := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hf, hL]
    _ = ∫ p : X × Y, (b p.1 * a p.2) * φ (LX p.1 + LY p.2) ∂(c • (μ.prod η)) :=
      he.integral_comp e.measurableEmbedding
        (fun p : X × Y => (b p.1 * a p.2) * φ (LX p.1 + LY p.2))
    _ = (c : ℂ) * ∫ p : X × Y, (b p.1 * a p.2) * φ (LX p.1 + LY p.2) ∂μ.prod η := by
      rw [integral_smul_nnreal_measure]
      simp only [NNReal.smul_def, Complex.real_smul]
    _ = (c : ℂ) * ∫ p, a p * (∫ x, b x * φ (LX x + LY p) ∂μ) ∂η := by
      congr 1
      rw [integral_prod _ hprod, integral_integral_swap hprod]
      apply integral_congr_ae
      filter_upwards with p
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      ring

private lemma fieldUnitsBorel {K : Type*} [Field K] [TopologicalSpace K]
    [ContinuousInv₀ K] [MeasurableSpace K] [BorelSpace K] : BorelSpace Kˣ := ⟨by
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K), Units.isEmbedding_val₀.isInducing.eq_induced,
    borel_comap]⟩
def realCompletionUnitEquiv {F : Type} [Field F] [NumberField F]
    (v : InfinitePlace F) (hv : v.IsReal) : v.Completionˣ ≃ₜ* ℝˣ :=
  Units.mapContinuousMulEquiv {
    toMulEquiv := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
    continuous_toFun := (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
    continuous_invFun := (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous }
def complexCompletionUnitEquiv {F : Type} [Field F] [NumberField F]
    (v : InfinitePlace F) (hv : v.IsComplex) : v.Completionˣ ≃ₜ* ℂˣ :=
  Units.mapContinuousMulEquiv {
    toMulEquiv := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toMulEquiv
    continuous_toFun := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
    continuous_invFun := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous }

local instance {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSpace (SLocalProduct F S) := borel _
private lemma rawUnitsBorel {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    @BorelSpace (SLocalProduct F S)ˣ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) := by
  have he : Topology.IsEmbedding (Units.val : (SLocalProduct F S)ˣ → SLocalProduct F S) := by
    let e0 := (rawProdUnits (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)).trans
      (rawProdCongr ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits)
    have hi := ((Topology.IsEmbedding.piMap (fun v : InfinitePlace F =>
      (Units.isEmbedding_val₀ (G₀ := v.Completion)))).prodMap
      (Topology.IsEmbedding.piMap (fun v : S =>
        (Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F)))))
    exact hi.comp e0.toHomeomorph.isEmbedding
  exact ⟨by
    change MeasurableSpace.comap Units.val (borel (SLocalProduct F S)) = borel _
    rw [he.isInducing.eq_induced, borel_comap]⟩

theorem rawCompletionIsolation_haar {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : InfinitePlace F)
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (μ : Measure v.Completionˣ) (hμ : μ.IsHaarMeasure)
    (η : Measure (RemainingCoordinates S v)) (hη : η.IsHaarMeasure) :
    ∃ c : NNReal, ν.map (rawCompletionIsolation S v) = c • μ.prod η := by
  letI : BorelSpace (RemainingCoordinates S v) := ⟨rfl⟩
  letI : BorelSpace v.Completionˣ := fieldUnitsBorel
  letI : MeasurableSpace (SLocalProduct F S) := borel _
  letI : BorelSpace (SLocalProduct F S)ˣ := rawUnitsBorel S
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (w : S) : TopologicalSpace.SeparableSpace (w.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (w.val.denseRange_algebraMap F)
  letI (w : S) : SecondCountableTopology (w.val.adicCompletion F) := inferInstance
  letI (w : S) : SecondCountableTopology (w.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completion := by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.secondCountableTopology
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  letI (w : InfinitePlace F) : BorelSpace w.Completionˣ := fieldUnitsBorel
  letI (w : S) : BorelSpace (w.val.adicCompletion F)ˣ := fieldUnitsBorel
  letI := hν
  letI := hμ
  letI := hη
  have hsfμ : SFinite μ := inferInstance
  have hsfη : SFinite η := inferInstance
  have hmulμ : MeasurableMul v.Completionˣ := inferInstance
  have hmulη : MeasurableMul (RemainingCoordinates S v) := inferInstance
  let e := rawCompletionIsolation S v
  let ν' := ν.map e
  letI : ν'.IsHaarMeasure := e.isHaarMeasure_map ν
  exact ⟨ν'.haarScalarFactor (μ.prod η), Measure.isMulLeftInvariant_eq_smul ν' (μ.prod η)⟩

def completionTensorFactor {F : Type} [Field F] [NumberField F]
    (gR : {v : InfinitePlace F // v.IsReal} → SchwartzMap ℝ ℂ)
    (gC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap ℂ ℂ)
    (v : InfinitePlace F) (x : v.Completion) : ℂ :=
  if hv : v.IsReal then gR ⟨v, hv⟩ (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x)
  else gC ⟨v, v.not_isReal_iff_isComplex.mp hv⟩ (InfinitePlace.Completion.extensionEmbedding v x)

@[simp] theorem completionTensorFactor_real {F : Type} [Field F] [NumberField F]
    (gR : {v : InfinitePlace F // v.IsReal} → SchwartzMap ℝ ℂ)
    (gC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap ℂ ℂ)
    (v : InfinitePlace F) (hv : v.IsReal) (x : v.Completion) :
    completionTensorFactor gR gC v x =
      gR ⟨v, hv⟩ (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x) := by
  simp [completionTensorFactor, hv]

@[simp] theorem completionTensorFactor_complex {F : Type} [Field F] [NumberField F]
    (gR : {v : InfinitePlace F // v.IsReal} → SchwartzMap ℝ ℂ)
    (gC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap ℂ ℂ)
    (v : InfinitePlace F) (hv : v.IsComplex) (x : v.Completion) :
    completionTensorFactor gR gC v x =
      gC ⟨v, hv⟩ (InfinitePlace.Completion.extensionEmbedding v x) := by
  simp [completionTensorFactor, v.not_isReal_iff_isComplex.mpr hv]

set_option maxHeartbeats 1000000

attribute [local instance] fieldUnitsBorel

 local instance instSecondCountableTopologyLocalSheetCompletion {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) : SecondCountableTopology w.Completion := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.secondCountableTopology
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.secondCountableTopology

 local instance instSecondCountableTopologyLocalSheetCompletionUnits {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

 def realC {F : Type} [Field F] [NumberField F]
    {v : InfinitePlace F} (hv : v.IsReal) : v.Completion ≃ₜ* ℝ where
  __ := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
  continuous_toFun := (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
  continuous_invFun := (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous

 def complexC {F : Type} [Field F] [NumberField F]
    {v : InfinitePlace F} (hv : v.IsComplex) : v.Completion ≃ₜ* ℂ where
  __ := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toMulEquiv
  continuous_toFun := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
  continuous_invFun := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous

 def archTest {F : Type} [Field F] [NumberField F]
    (gR : (v : {v : InfinitePlace F // v.IsReal}) → SchwartzMap ℝ ℂ)
    (gC : (v : {v : InfinitePlace F // v.IsComplex}) → SchwartzMap ℂ ℂ)
    (v : InfinitePlace F) (x : v.Completion) : ℂ :=
  if hv : v.IsReal then gR ⟨v, hv⟩ (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x)
  else gC ⟨v, InfinitePlace.not_isReal_iff_isComplex.mp hv⟩
    (InfinitePlace.Completion.extensionEmbedding v x)

private lemma archTest_prod {F : Type} [Field F] [NumberField F]
    (gR : (v : {v : InfinitePlace F // v.IsReal}) → SchwartzMap ℝ ℂ)
    (gC : (v : {v : InfinitePlace F // v.IsComplex}) → SchwartzMap ℂ ℂ)
    (x : InfiniteAdeleRing F) :
    (∏ v, archTest gR gC v (x v)) =
      (∏ v, gR v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x).1 v)) *
      ∏ v, gC v ((InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 v) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : InfinitePlace F => v.IsReal)]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    simp [archTest, v.prop]
  · apply Fintype.prod_equiv
      (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex))
    intro v
    simp only [archTest, dif_neg v.prop]
    rfl

private lemma archTest_integrable {F : Type} [Field F] [NumberField F]
    (gR : (v : {v : InfinitePlace F // v.IsReal}) → SchwartzMap ℝ ℂ)
    (gC : (v : {v : InfinitePlace F // v.IsComplex}) → SchwartzMap ℂ ℂ)
    (v : InfinitePlace F) (μ : Measure v.Completionˣ) [μ.IsHaarMeasure]
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : v.Completionˣ => archTest gR gC v x.val *
      ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) μ := by
  rcases v.isReal_or_isComplex with hv | hv
  · let e := Units.mapContinuousMulEquiv (realC hv)
    letI : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
    letI : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
    have hi := ProbeSheetGlobalIntegrability.schwartz_realUnitsMellin_integrable
      (gR ⟨v, hv⟩) (μ.map e) (σ : ℂ) hσ
    have hn (x : v.Completion) :
        ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x‖ = ‖x‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
        (map_zero _) x
    have hi' := e.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hi
    change Integrable (fun x : v.Completionˣ =>
      gR ⟨v, hv⟩ (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x.val) *
      ((‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x.val‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) μ at hi'
    simpa only [archTest, dif_pos hv, hn] using hi'
  · let e := Units.mapContinuousMulEquiv (complexC hv)
    letI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
    letI : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
    have hi := ProbeSheetFourierMellinBounds.schwartz_complexUnitsMellin_integrable_of_isHaarMeasure
      (gC ⟨v, hv⟩) (μ.map e) (σ : ℂ) hσ
    have hn (x : v.Completion) :
        ‖InfinitePlace.Completion.extensionEmbedding v x‖ = ‖x‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero _) x
    have hi' := e.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hi
    change Integrable (fun x : v.Completionˣ =>
      gC ⟨v, hv⟩ (InfinitePlace.Completion.extensionEmbedding v x.val) *
      ((‖InfinitePlace.Completion.extensionEmbedding v x.val‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) μ at hi'
    simpa only [archTest, dif_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hv), hn] using hi'

private lemma cpow_prod_nonneg {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (z : ℂ) :
    ((∏ i ∈ s, b i : ℝ) : ℂ) ^ z = ∏ i ∈ s, (b i : ℂ) ^ z := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hb i (by simp))
        (Finset.prod_nonneg (fun j hj => hb j (by simp [hj]))),
      ih (fun j hj => hb j (by simp [hj])), Finset.prod_insert hi]

private lemma cast_integrable {X : Type*} {m n : MeasurableSpace X}
    (h : m = n) (μ : @Measure X m) (f : X → ℂ)
    (hf : @Integrable ℂ _ _ X m f μ) :
    @Integrable ℂ _ _ X n f (Eq.mp (congrArg (fun m => @Measure X m) h) μ) := by
  subst n
  exact hf

private lemma cast_haar {X : Type*} [Group X] [TopologicalSpace X]
    {m n : MeasurableSpace X} (h : m = n) (μ : @Measure X m)
    (hh : @Measure.IsHaarMeasure X _ _ m μ) :
    @Measure.IsHaarMeasure X _ _ n (Eq.mp (congrArg (fun m => @Measure X m) h) μ) := by
  subst n
  exact hh

theorem schwartzTensor_isolate_archimedean_integral
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ)
    (hh : ProbeSheetVerticalDecay.IsSchwartzTensor F S h)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ (v : InfinitePlace F) (η : Measure (RemainingCoordinates S v))
      (_ : SFinite η) (L : RemainingCoordinates S v → ℝ)
      (a : RemainingCoordinates S v → ℂ),
      Measurable L ∧ Integrable a η ∧
      ((∃ g : SchwartzMap ℝ ℂ, v.IsReal ∧
        ∀ φ : ℝ → ℂ, Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
          (∫ y : (SLocalProduct F S)ˣ,
            (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
              φ (Real.log (ProbeWeight.modulus F S y)) ∂ν) =
            ∫ p, a p * (∫ x : ℝ,
              (g x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) / ((|x| : ℝ) : ℂ)) *
                φ (Real.log (x ^ 2) + L p)) ∂η) ∨
       (∃ g : SchwartzMap ℂ ℂ, v.IsComplex ∧
        ∀ φ : ℝ → ℂ, Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
          (∫ y : (SLocalProduct F S)ˣ,
            (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
              φ (Real.log (ProbeWeight.modulus F S y)) ∂ν) =
            ∫ p, a p * (∫ z : ℂ,
              (g z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) /
                ((‖z‖ ^ 2 : ℝ) : ℂ)) *
                φ (Real.log (‖z‖ ^ 2) + L p)) ∂η)) := by
  classical
  obtain ⟨ct, gR, gC, gF, hF, ht⟩ := hh
  let v : InfinitePlace F := Classical.choice inferInstance
  letI : BorelSpace (RemainingCoordinates S v) := ⟨rfl⟩
  letI : BorelSpace (SLocalProduct F S)ˣ := rawUnitsBorel S
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (w : S) : TopologicalSpace.SeparableSpace (w.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (w.val.denseRange_algebraMap F)
  letI (w : S) : SecondCountableTopology (w.val.adicCompletion F) := inferInstance
  letI (w : S) : SecondCountableTopology (w.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  letI (w : S) : MeasurableSpace (w.val.adicCompletion F) := borel _
  letI (w : S) : BorelSpace (w.val.adicCompletion F) := ⟨rfl⟩
  let μ : Measure v.Completionˣ := Measure.haar
  let ηA : Measure ((w : {w : InfinitePlace F // w ≠ v}) → w.val.Completionˣ) :=
    Measure.pi (fun _ => Measure.haar)
  let ηF : Measure ((w : S) → (w.val.adicCompletion F)ˣ) :=
    Measure.pi (fun _ => Measure.haar)
  have hm : (@Prod.instMeasurableSpace
      ((w : {w : InfinitePlace F // w ≠ v}) → w.val.Completionˣ)
      ((w : S) → (w.val.adicCompletion F)ˣ) _ _) = borel (RemainingCoordinates S v) :=
    @BorelSpace.measurable_eq
      (((w : {w : InfinitePlace F // w ≠ v}) → w.val.Completionˣ) ×
       ((w : S) → (w.val.adicCompletion F)ˣ)) _ (@Prod.instMeasurableSpace _ _ _ _)
      (by infer_instance)
  let η : Measure (RemainingCoordinates S v) :=
    Eq.mp (congrArg (fun m => @Measure (RemainingCoordinates S v) m) hm) (ηA.prod ηF)
  letI : μ.IsHaarMeasure := inferInstanceAs (Measure.haar.IsHaarMeasure)
  letI : η.IsHaarMeasure := cast_haar hm (ηA.prod ηF) (by dsimp [ηA, ηF]; infer_instance)
  letI : SFinite η := inferInstance
  let kA (w : InfinitePlace F) (x : w.Completionˣ) :=
    archTest gR gC w x.val * ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)
  let kF (w : S) (x : (w.val.adicCompletion F)ˣ) :=
    gF w x.val * (‖x.val‖ : ℂ) ^ (σ : ℂ)
  let b : v.Completionˣ → ℂ := kA v
  let a0 : RemainingCoordinates S v → ℂ := fun p =>
    ct * ((∏ w : {w : InfinitePlace F // w ≠ v}, kA w (p.1 w)) *
      ∏ w : S, kF w (p.2 w))
  have hb : Integrable b μ := archTest_integrable gR gC v μ σ hσ
  have haA : Integrable (fun p => ∏ w : {w : InfinitePlace F // w ≠ v}, kA w (p w)) ηA :=
    Integrable.fintype_prod_dep (fun w =>
      archTest_integrable gR gC w.val Measure.haar σ hσ)
  have haF : Integrable (fun p => ∏ w : S, kF w (p w)) ηF :=
    Integrable.fintype_prod_dep (fun w =>
      ProbeSheetGlobalIntegrability.finiteUnitsMellin_integrable F w.val
        (gF w) (hF w).1 (hF w).2 Measure.haar (σ : ℂ) hσ)
  have ha : Integrable a0 η :=
    cast_integrable hm (ηA.prod ηF) a0 ((haA.mul_prod haF).const_mul ct)
  obtain ⟨c, hc⟩ := rawCompletionIsolation_haar S v ν hν μ inferInstance η inferInstance
  let e := (rawCompletionIsolation S v).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e ν (c • μ.prod η) := ⟨e.measurable, hc⟩
  let L : RemainingCoordinates S v → ℝ := fun p => Real.log (remainingModulus S v p)
  let LX : v.Completionˣ → ℝ := fun x => Real.log (‖x.val‖ ^ 2)
  have hL : Measurable L := remainingLogModulus_measurable S v
  have hLX : Measurable LX := by dsimp [LX]; fun_prop
  have hf (y : (SLocalProduct F S)ˣ) :
      h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ) =
        b (e y).1 * a0 (e y).2 := by
    have ht' : h y.val = ct *
        ((∏ w : InfinitePlace F, archTest gR gC w (y.val.1 w)) *
          ∏ w : S, gF w (y.val.2 w)) := by
      rw [archTest_prod]; exact ht _
    rw [ht', rawCompletionIsolation_modulus S v,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (sq_nonneg _)
        (remainingModulus_pos S v _).le]
    dsimp [b, a0, kA, kF, e]
    simp only [rawCompletionIsolation_fst, rawCompletionIsolation_remaining_arch,
      rawCompletionIsolation_remaining_finite, Finset.prod_mul_distrib]
    rw [Fintype.prod_eq_mul_prod_compl v]
    have hp : (∏ w ∈ ({v}ᶜ : Finset (InfinitePlace F)), archTest gR gC w (y.val.1 w)) =
        ∏ w : {w : InfinitePlace F // w ≠ v}, archTest gR gC w (y.val.1 w) :=
      Finset.prod_subtype _ (by simp) _
    rw [hp]
    unfold remainingModulus
    simp only [rawCompletionIsolation_remaining_arch, rawCompletionIsolation_remaining_finite]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
      (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)),
      cpow_prod_nonneg _ _ (fun _ _ => sq_nonneg _) (σ : ℂ),
      cpow_prod_nonneg _ _ (fun _ _ => norm_nonneg _) (σ : ℂ)]
    change _ = (archTest gR gC v (y.val.1 v) * ((‖y.val.1 v‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) *
      (ct * ((∏ w : {w : InfinitePlace F // w ≠ v}, archTest gR gC w (y.val.1 w)) *
        (∏ w : {w : InfinitePlace F // w ≠ v}, ((‖y.val.1 w‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) *
        ((∏ w : S, gF w (y.val.2 w)) * ∏ w : S, (‖y.val.2 w‖ : ℂ) ^ (σ : ℂ))))
    simp only [Finset.univ_eq_attach]
    ring
  have hiso (φ : ℝ → ℂ) (hφ : Continuous φ) (hbound : ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) :=
    isolate_integral_of_scaled_product ν μ η e c he
      (fun y => h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) b a0 hb ha
      (fun y => Real.log (ProbeWeight.modulus F S y)) LX L hLX hL hf
      (fun y => rawCompletionIsolation_log_modulus S v y) φ hφ hbound
  rcases v.isReal_or_isComplex with hv | hv
  · let u := Units.mapContinuousMulEquiv (realC hv)
    let ρ : Measure ℝˣ := μ.map u
    letI : ρ.IsHaarMeasure := u.isHaarMeasure_map μ
    obtain ⟨d, hd, hden⟩ := realUnits_haar_integral_density ρ
    let a : RemainingCoordinates S v → ℂ := fun p =>
      (c : ℂ) * (d : ℂ) * a0 p
    refine ⟨v, η, inferInstance, L, a, hL, ha.const_mul _, Or.inl ?_⟩
    refine ⟨gR ⟨v, hv⟩, hv, ?_⟩
    intro φ hφ hbound
    rw [hiso φ hφ hbound]
    apply integral_congr_ae
    filter_upwards with p
    have hn (x : v.Completion) :
        ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x‖ = ‖x‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
        (map_zero _) x
    let f : ℝ → ℂ := fun x =>
      (gR ⟨v, hv⟩ x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) *
        φ (Real.log (x ^ 2) + L p)
    have hcomp (x : v.Completionˣ) :
        b x * φ (LX x + L p) = f (u x).val := by
      change _ = f (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x.val)
      dsimp [b, kA, archTest, LX, f]
      rw [dif_pos hv]
      have hs : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x.val) ^ 2 =
          ‖x.val‖ ^ 2 := by
        rw [← hn x.val, Real.norm_eq_abs, sq_abs]
      rw [hs]
    have hi : (∫ x, b x * φ (LX x + L p) ∂μ) =
        (d : ℂ) * (∫ x : ℝ,
          ((gR ⟨v, hv⟩ x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) / ((|x| : ℝ) : ℂ)) *
            φ (Real.log (x ^ 2) + L p)) := by
      calc
        _ = ∫ x, f (u x).val ∂μ := integral_congr_ae (Filter.Eventually.of_forall hcomp)
        _ = ∫ x : ℝˣ, f x.val ∂ρ :=
          (u.toHomeomorph.measurableEmbedding.integral_map (fun x : ℝˣ => f x.val)).symm
        _ = _ := by
          rw [hden f]
          simp only [Complex.real_smul]
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          dsimp [f]
          ring
    rw [hi]
    dsimp [a]
    ring
  · let u := Units.mapContinuousMulEquiv (complexC hv)
    let ρ : Measure ℂˣ := μ.map u
    letI : ρ.IsHaarMeasure := u.isHaarMeasure_map μ
    obtain ⟨d, hd, hden⟩ := complexUnits_haar_integral_density ρ
    let a : RemainingCoordinates S v → ℂ := fun p =>
      (c : ℂ) * (d : ℂ) * a0 p
    refine ⟨v, η, inferInstance, L, a, hL, ha.const_mul _, Or.inr ?_⟩
    refine ⟨gC ⟨v, hv⟩, hv, ?_⟩
    intro φ hφ hbound
    rw [hiso φ hφ hbound]
    apply integral_congr_ae
    filter_upwards with p
    have hn (x : v.Completion) :
        ‖InfinitePlace.Completion.extensionEmbedding v x‖ = ‖x‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero _) x
    let f : ℂ → ℂ := fun x =>
      (gC ⟨v, hv⟩ x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) *
        φ (Real.log (‖x‖ ^ 2) + L p)
    have hcomp (x : v.Completionˣ) :
        b x * φ (LX x + L p) = f (u x).val := by
      change _ = f (InfinitePlace.Completion.extensionEmbedding v x.val)
      dsimp [b, kA, archTest, LX, f]
      rw [dif_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hv), hn]
    have hi : (∫ x, b x * φ (LX x + L p) ∂μ) =
        (d : ℂ) * (∫ x : ℂ,
          ((gC ⟨v, hv⟩ x * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) / ((‖x‖ ^ 2 : ℝ) : ℂ)) *
            φ (Real.log (‖x‖ ^ 2) + L p)) := by
      calc
        _ = ∫ x, f (u x).val ∂μ := integral_congr_ae (Filter.Eventually.of_forall hcomp)
        _ = ∫ x : ℂˣ, f x.val ∂ρ :=
          (u.toHomeomorph.measurableEmbedding.integral_map (fun x : ℂˣ => f x.val)).symm
        _ = _ := by
          rw [hden f]
          simp only [Complex.real_smul]
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          dsimp [f]
          ring
    rw [hi]
    dsimp [a]
    ring

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.RadialIsolation
