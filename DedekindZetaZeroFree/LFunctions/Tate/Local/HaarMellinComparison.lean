module

public import DedekindZetaZeroFree.LFunctions.Tate.AnnularTensorProfiles
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.DilationAndTranslation
public import DedekindZetaZeroFree.LFunctions.Tate.ArchimedeanAdditiveHaarScaling
public import DedekindZetaZeroFree.LFunctions.Tate.FiniteAdditiveHaarScaling

@[expose] public section

namespace DedekindZetaZeroFree.TateSLocalComparison
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local instance archMeasurable : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance archBorel : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
local instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩
theorem units_val_isEmbedding : Topology.IsEmbedding (Units.val : (SLocalProduct F S)ˣ → SLocalProduct F S) := by
  let e : (SLocalProduct F S)ˣ ≃ₜ
      ((InfiniteAdeleRing F)ˣ × ((v : S) → v.val.adicCompletion F)ˣ) := Homeomorph.prodUnits
  have ha : Topology.IsEmbedding (Units.val : (InfiniteAdeleRing F)ˣ → InfiniteAdeleRing F) := by
    exact (Topology.IsEmbedding.piMap (fun _ => Units.isEmbedding_val₀)).comp
      ContinuousMulEquiv.piUnits.toHomeomorph.isEmbedding
  have hb : Topology.IsEmbedding
      (Units.val : ((v : S) → v.val.adicCompletion F)ˣ → ((v : S) → v.val.adicCompletion F)) := by
    exact (Topology.IsEmbedding.piMap (fun _ => Units.isEmbedding_val₀)).comp
      ContinuousMulEquiv.piUnits.toHomeomorph.isEmbedding
  exact (ha.prodMap hb).comp e.isEmbedding
local instance unitsBorel : BorelSpace (SLocalProduct F S)ˣ := by
  constructor
  change (inferInstance : MeasurableSpace (SLocalProduct F S)).comap Units.val = borel _
  rw [BorelSpace.measurable_eq (α := SLocalProduct F S), ← borel_comap,
    ← (units_val_isEmbedding F S).isInducing.eq_induced]

theorem modulus_continuous [NumberField.IsTotallyComplex F] :
    Continuous (TateTensorProfile.modulus F S) := by
  unfold TateTensorProfile.modulus
  apply Continuous.mul
  · simp only [InfiniteAdeleRing.norm_def]
    exact continuous_finset_prod _ (fun v _ => ((continuous_apply v).comp continuous_fst).norm.pow _)
  · exact continuous_finset_prod _ (fun v _ => ((continuous_apply v).comp continuous_snd).norm)

theorem units_val_isOpenEmbedding [NumberField.IsTotallyComplex F] :
    Topology.IsOpenEmbedding (Units.val : (SLocalProduct F S)ˣ → SLocalProduct F S) := by
  refine ⟨units_val_isEmbedding F S, ?_⟩
  have heq : Set.range (Units.val : (SLocalProduct F S)ˣ → SLocalProduct F S) =
      {x | 0 < TateTensorProfile.modulus F S x} := by
    ext x
    change IsUnit x ↔ 0 < TateTensorProfile.modulus F S x
    exact (TateTensorProfile.modulus_pos_iff F S x).symm
  rw [heq]
  exact isOpen_lt continuous_const (modulus_continuous F S)

theorem modulus_mul [NumberField.IsTotallyComplex F] (x y : SLocalProduct F S) :
    TateTensorProfile.modulus F S (x * y) =
      TateTensorProfile.modulus F S x * TateTensorProfile.modulus F S y := by
  unfold TateTensorProfile.modulus
  have ha : ‖x.1 * y.1‖ = ‖x.1‖ * ‖y.1‖ := by
    rw [InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_def]
    change (∏ v, ‖x.1 v * y.1 v‖ ^ v.mult) = _
    simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, Finset.prod_mul_distrib, ha]
  ring

private theorem canonical_additive_haar (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F] :
    (TateTensorProfile.additiveMeasure F S).IsAddHaarMeasure := by
  letI := PoissonArch.traceMeasure_isAddHaarMeasure F
  letI : ∀ v : S, (localNormalizedHaar F v.val).IsAddHaarMeasure :=
    fun v => localNormalizedHaar_isAddHaarMeasure F v.val
  letI := (PoissonArch.infiniteAdeleToSpace F).symm.isAddHaarMeasure_map
    (PoissonArch.traceMeasure F)
  unfold TateTensorProfile.additiveMeasure
  infer_instance

theorem additive_fourier_comparison (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F]
    (μ : @Measure (SLocalProduct F S) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F S) _ _ (borel _) μ) :
    ∃ b : ℝ, 0 < b ∧ ∀ (W : SLocalProduct F S → ℂ) (y : SLocalProduct F S),
      (∫ x, W x * (sLocalTraceCharacter F S (-x * y) : ℂ) ∂μ) =
        (b : ℂ) * TateTensorProfile.fourier F S W y := by
  letI := canonical_additive_haar F S
  letI : ∀ v : S, SecondCountableTopology (v.val.adicCompletion F) :=
    fun v => PoissonS.completion_secondCountable F v.val
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.secondCountableTopology
  have heq := BorelSpace.measurable_eq (α := SLocalProduct F S)
  revert μ hμ
  rw [← heq]
  intro μ hμ
  letI := hμ
  let b := Measure.addHaarScalarFactor μ (TateTensorProfile.additiveMeasure F S)
  refine ⟨(b : ℝ), ?_, ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ
      (TateTensorProfile.additiveMeasure F S)
  · intro W y
    rw [Measure.isAddLeftInvariant_eq_smul μ (TateTensorProfile.additiveMeasure F S),
      integral_smul_nnreal_measure]
    simp only [TateTensorProfile.fourier, neg_mul, Complex.real_smul]
    rfl

def canonicalUnitsMeasure (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F] : Measure (SLocalProduct F S)ˣ :=
  Measure.comap Units.val ((TateTensorProfile.additiveMeasure F S).withDensity
    (fun x => ENNReal.ofReal (TateTensorProfile.multiplicativeDensityConstant F S /
      TateTensorProfile.modulus F S x)))

theorem canonicalUnitsMeasure_map (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F] :
    Measure.map Units.val (canonicalUnitsMeasure F S) =
      TateTensorProfile.multiplicativeMeasure F S := by
  unfold canonicalUnitsMeasure TateTensorProfile.multiplicativeMeasure
  rw [(units_val_isOpenEmbedding F S).measurableEmbedding.map_comap]
  rw [restrict_withDensity (units_val_isOpenEmbedding F S).measurableEmbedding.measurableSet_range]
  rfl

theorem canonicalUnitsMeasure_integral (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F] (g : SLocalProduct F S → ℂ) :
    (∫ y, g y.val ∂canonicalUnitsMeasure F S) =
      ∫ x, g x ∂TateTensorProfile.multiplicativeMeasure F S := by
  rw [← canonicalUnitsMeasure_map]
  exact ((units_val_isOpenEmbedding F S).measurableEmbedding.integral_map g).symm

theorem canonicalUnitsMeasure_left (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F]
    (hscale : ∀ g : (SLocalProduct F S)ˣ,
      Measure.map (fun x : SLocalProduct F S => g.val * x) (TateTensorProfile.additiveMeasure F S) =
        (ENNReal.ofReal (TateTensorProfile.modulus F S g.val))⁻¹ •
          TateTensorProfile.additiveMeasure F S) :
    (canonicalUnitsMeasure F S).IsMulLeftInvariant := by
  let ev := (units_val_isOpenEmbedding F S).measurableEmbedding
  let D := fun x : SLocalProduct F S => ENNReal.ofReal
    (TateTensorProfile.multiplicativeDensityConstant F S / TateTensorProfile.modulus F S x)
  have hD : Measurable D :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (TateTensorProfile.modulus_measurable F S))
  constructor
  intro g
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  change ((TateTensorProfile.additiveMeasure F S).withDensity D).comap Units.val
    ((fun x => g * x) ⁻¹' s) =
      ((TateTensorProfile.additiveMeasure F S).withDensity D).comap Units.val s
  rw [ev.comap_apply, ev.comap_apply]
  have hpre : Units.val '' ((fun x => g * x) ⁻¹' s) =
      (fun x : SLocalProduct F S => g.val * x) ⁻¹' (Units.val '' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨g * u, hu, by simp⟩
    · rintro ⟨u, hu, he⟩
      refine ⟨g⁻¹ * u, ?_, ?_⟩
      · simpa using hu
      · change (g⁻¹ * u).val = x
        simp only [Units.val_mul]
        rw [he]; simp
  rw [hpre, withDensity_apply _ (by exact (ev.measurableSet_image.mpr hs).preimage (by fun_prop)),
    withDensity_apply _ (ev.measurableSet_image.mpr hs)]
  have hmul (x : SLocalProduct F S) : D (g.val * x) =
      (ENNReal.ofReal (TateTensorProfile.modulus F S g.val))⁻¹ * D x := by
    dsimp [D]
    rw [modulus_mul]
    rw [show TateTensorProfile.multiplicativeDensityConstant F S /
        (TateTensorProfile.modulus F S g.val * TateTensorProfile.modulus F S x) =
        (TateTensorProfile.modulus F S g.val)⁻¹ *
          (TateTensorProfile.multiplicativeDensityConstant F S / TateTensorProfile.modulus F S x) by
          simp only [div_eq_mul_inv, mul_inv]; ring]
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (TateTensorProfile.modulus_nonneg F S _)),
      ENNReal.ofReal_inv_of_pos (TateTensorProfile.modulus_pos_of_isUnit F S _ g.isUnit)]
  have hm := setLIntegral_map (μ := TateTensorProfile.additiveMeasure F S)
    (g := fun x : SLocalProduct F S => g.val * x)
    (s := Units.val '' s) (ev.measurableSet_image.mpr hs) hD (by fun_prop)
  rw [hscale, Measure.restrict_smul, lintegral_smul_measure] at hm
  simp only [ENNReal.smul_def, smul_eq_mul] at hm
  simp_rw [hmul] at hm
  rw [lintegral_const_mul _ hD] at hm
  exact (ENNReal.mul_right_inj
    (by simp)
    (by simp only [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero, not_le];
        exact TateTensorProfile.modulus_pos_of_isUnit F S _ g.isUnit)).mp hm.symm
theorem canonicalUnitsMeasure_isHaar (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F]
    [LocallyCompactSpace (SLocalProduct F S)]
    [hleft : (canonicalUnitsMeasure F S).IsMulLeftInvariant] :
    (canonicalUnitsMeasure F S).IsHaarMeasure := by
  letI := canonical_additive_haar F S
  letI : LocallyCompactSpace (SLocalProduct F S)ˣ :=
    (units_val_isOpenEmbedding F S).locallyCompactSpace
  let ev := (units_val_isOpenEmbedding F S).measurableEmbedding
  let D := fun x : SLocalProduct F S => ENNReal.ofReal
    (TateTensorProfile.multiplicativeDensityConstant F S / TateTensorProfile.modulus F S x)
  have hD : Measurable D :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (TateTensorProfile.modulus_measurable F S))
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds (1 : (SLocalProduct F S)ˣ)
  have hint : (interior K).Nonempty := ⟨1, mem_interior_iff_mem_nhds.mpr hKmem⟩
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK hint
  · unfold canonicalUnitsMeasure
    rw [ev.comap_apply]
    change ((TateTensorProfile.additiveMeasure F S).withDensity D) (Units.val '' K) ≠ 0
    apply mt (withDensity_apply_eq_zero (μ := TateTensorProfile.additiveMeasure F S)
      (s := Units.val '' K) hD).mp
    have heq : {x | D x ≠ 0} ∩ (Units.val '' K) = Units.val '' K := by
      apply Set.inter_eq_right.mpr
      rintro x ⟨u, hu, rfl⟩
      exact (ENNReal.ofReal_pos.mpr (div_pos (TateTensorProfile.multiplicativeDensityConstant_pos F S)
        (TateTensorProfile.modulus_pos_of_isUnit F S _ u.isUnit))).ne'
    rw [heq]
    have hpos : 0 < (TateTensorProfile.additiveMeasure F S) (Units.val '' interior K) :=
      ((units_val_isOpenEmbedding F S).isOpenMap _ isOpen_interior).measure_pos _ (hint.image _)
    exact (hpos.trans_le (measure_mono (Set.image_mono interior_subset))).ne'
  · unfold canonicalUnitsMeasure
    rw [ev.comap_apply, withDensity_apply _ ((hK.image Units.continuous_val).measurableSet)]
    have hc : ContinuousOn (fun x : SLocalProduct F S =>
        TateTensorProfile.multiplicativeDensityConstant F S / TateTensorProfile.modulus F S x)
        (Units.val '' K) := by
      apply ContinuousOn.div continuousOn_const (modulus_continuous F S).continuousOn
      rintro x ⟨u, hu, rfl⟩
      exact (TateTensorProfile.modulus_pos_of_isUnit F S _ u.isUnit).ne'
    have hi := ContinuousOn.integrableOn_compact (μ := TateTensorProfile.additiveMeasure F S)
      (hK.image Units.continuous_val) hc
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x =>
      div_nonneg (TateTensorProfile.multiplicativeDensityConstant_pos F S).le
        (TateTensorProfile.modulus_nonneg F S x)))]
    exact ENNReal.ofReal_ne_top

theorem units_normMellin_comparison_of_canonicalHaar
    (S : Finset (HeightOneSpectrum (𝓞 F))) [NumberField.IsTotallyComplex F]
    [SecondCountableTopology (SLocalProduct F S)ˣ]
    [(canonicalUnitsMeasure F S).IsHaarMeasure]
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ (W : SLocalProduct F S → ℂ) (s : ℝ),
      (∫ y, TateTensorProfile.fourier F S W y.val *
        (TateTensorProfile.modulus F S y.val : ℂ) ^ (s : ℂ) ∂ν) =
        (c : ℂ) * TateTensorProfile.normMellin F S W s := by
  have heq := BorelSpace.measurable_eq (α := SLocalProduct F S)
  revert ν hν
  rw [← heq]
  intro ν hν
  letI := hν
  let c := Measure.haarScalarFactor ν (canonicalUnitsMeasure F S)
  refine ⟨(c : ℝ), ?_, ?_⟩
  · exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure ν (canonicalUnitsMeasure F S)
  · intro W s
    rw [Measure.isMulLeftInvariant_eq_smul ν (canonicalUnitsMeasure F S),
      integral_smul_nnreal_measure,
      canonicalUnitsMeasure_integral F S
        (fun x => TateTensorProfile.fourier F S W x *
          (TateTensorProfile.modulus F S x : ℂ) ^ (s : ℂ))]
    simp only [TateTensorProfile.normMellin]
    rfl

theorem haar_fourierMellin_comparison_of_canonicalHaar
    (S : Finset (HeightOneSpectrum (𝓞 F))) [NumberField.IsTotallyComplex F]
    [SecondCountableTopology (SLocalProduct F S)ˣ]
    [(canonicalUnitsMeasure F S).IsHaarMeasure]
    (μ : @Measure (SLocalProduct F S) (borel _))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F S) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν) :
    ∃ a : ℝ, 0 < a ∧ ∀ (W : SLocalProduct F S → ℂ) (s : ℝ),
      (∫ y, (∫ x, W x * (sLocalTraceCharacter F S (-x * y.val) : ℂ) ∂μ) *
        (TateTensorProfile.modulus F S y.val : ℂ) ^ (s : ℂ) ∂ν) =
        (a : ℂ) * TateTensorProfile.normMellin F S W s := by
  obtain ⟨b, hb, hfourier⟩ := additive_fourier_comparison F S μ hμ
  obtain ⟨c, hc, hmellin⟩ := units_normMellin_comparison_of_canonicalHaar F S ν hν
  refine ⟨b * c, mul_pos hb hc, ?_⟩
  intro W s
  simp_rw [hfourier, mul_assoc]
  rw [integral_const_mul, hmellin, Complex.ofReal_mul, mul_assoc]

theorem additiveMeasure_map_mul (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F] (g : (SLocalProduct F S)ˣ) :
    Measure.map (fun x : SLocalProduct F S => g.val * x)
        (TateTensorProfile.additiveMeasure F S) =
      (ENNReal.ofReal (TateTensorProfile.modulus F S g.val))⁻¹ •
        TateTensorProfile.additiveMeasure F S := by
  letI : LocallyCompactSpace (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.secondCountableTopology
  letI := PoissonArch.traceMeasure_isAddHaarMeasure F
  letI := (PoissonArch.infiniteAdeleToSpace F).symm.isAddHaarMeasure_map
    (PoissonArch.traceMeasure F)
  let ga : (InfiniteAdeleRing F)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)) g
  let gf : ((v : S) → v.val.adicCompletion F)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)) g
  have ha := TateSLocalMeasurability.archimedean_map_mul F ga
  have hf := TateSLocalMeasurability.finite_map_mul F S gf
  unfold TateTensorProfile.additiveMeasure
  change Measure.map (Prod.map (fun x => ga.val * x) (fun x => gf.val * x)) _ = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), ha, hf,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  congr 1
  unfold TateTensorProfile.modulus
  change (ENNReal.ofReal ‖g.val.1‖)⁻¹ *
      (ENNReal.ofReal (∏ v : S, ‖g.val.2 v‖))⁻¹ =
    (ENNReal.ofReal (‖g.val.1‖ * ∏ v : S, ‖g.val.2 v‖))⁻¹
  rw [ENNReal.ofReal_mul (by
    simp only [InfiniteAdeleRing.norm_def]
    positivity), ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
      (Or.inl ENNReal.ofReal_ne_top)]

theorem haar_fourierMellin_comparison (S : Finset (HeightOneSpectrum (𝓞 F)))
    [NumberField.IsTotallyComplex F]
    (μ : @Measure (SLocalProduct F S) (borel _))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F S) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν) :
    ∃ a : ℝ, 0 < a ∧ ∀ (W : SLocalProduct F S → ℂ) (s : ℝ),
      (∫ y, (∫ x, W x * (sLocalTraceCharacter F S (-x * y.val) : ℂ) ∂μ) *
        (TateTensorProfile.modulus F S y.val : ℂ) ^ (s : ℂ) ∂ν) =
        (a : ℂ) * TateTensorProfile.normMellin F S W s := by
  letI : ∀ v : S, LocallyCompactSpace (v.val.adicCompletion F) :=
    (PoissonS.finite_components_locallyCompact F S).1
  letI : LocallyCompactSpace (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  letI : ∀ v : S, SecondCountableTopology (v.val.adicCompletion F) :=
    fun v => PoissonS.completion_secondCountable F v.val
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (SLocalProduct F S)ˣ :=
    (units_val_isEmbedding F S).secondCountableTopology
  letI : (canonicalUnitsMeasure F S).IsMulLeftInvariant :=
    canonicalUnitsMeasure_left F S (additiveMeasure_map_mul F S)
  letI := canonicalUnitsMeasure_isHaar F S
  exact haar_fourierMellin_comparison_of_canonicalHaar F S μ ν hμ hν

end
end DedekindZetaZeroFree.TateSLocalComparison
