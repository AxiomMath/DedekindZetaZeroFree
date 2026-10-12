module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LocalUnitsTensorIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetLogDensity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

theorem integrable_log_density_of_radial_section
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (ν : Measure G) [ν.IsMulLeftInvariant] [SFinite ν]
    (L : G → ℝ) (hL : Measurable L)
    (a : ℝ → G) (ha : Measurable a)
    (hLa : ∀ s y, L (a s * y) = s + L y)
    (w : G → ℂ) (hw : Integrable w ν) :
    ∃ q : ℝ → ℂ, Integrable q ∧ ∀ φ : ℝ → ℂ,
      Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
      (∫ y, w y * φ (L y) ∂ν) = ∫ t, q t * φ t := by
  let T : (ℝ × G) ≃ᵐ (ℝ × G) :=
    { toFun := fun p => (p.1, a p.1 * p.2)
      invFun := fun p => (p.1, (a p.1)⁻¹ * p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      measurable_toFun := measurable_fst.prodMk ((ha.comp measurable_fst).mul measurable_snd)
      measurable_invFun := measurable_fst.prodMk ((ha.comp measurable_fst).inv.mul measurable_snd) }
  have hT : MeasurePreserving T (volume.prod ν) (volume.prod ν) := by
    exact (MeasurePreserving.id volume).skew_product
      (g := fun s y => a s * y)
      ((ha.comp measurable_fst).mul measurable_snd)
      (Filter.Eventually.of_forall fun s => (measurePreserving_mul_left ν (a s)).map_eq)
  let U : (ℝ × G) ≃ᵐ (ℝ × G) :=
    { toFun := fun p => (p.1 - L p.2, p.2)
      invFun := fun p => (p.1 + L p.2, p.2)
      left_inv := by intro p; dsimp; congr 1; ring
      right_inv := by intro p; dsimp; congr 1; ring
      measurable_toFun := (measurable_fst.sub (hL.comp measurable_snd)).prodMk measurable_snd
      measurable_invFun := (measurable_fst.add (hL.comp measurable_snd)).prodMk measurable_snd }
  have hU : MeasurePreserving U (volume.prod ν) (volume.prod ν) := by
    have h := (MeasurePreserving.id ν).skew_product
      (measurable_snd.sub (hL.comp measurable_fst))
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_right volume (-L y)).map_eq)
    have hh := (Measure.measurePreserving_swap (μ := ν) (ν := volume)).comp
      (h.comp (Measure.measurePreserving_swap (μ := volume) (ν := ν)))
    change MeasurePreserving (fun p : ℝ × G => (p.1 - L p.2, p.2)) _ _
    simpa only [Function.comp_def, id_eq, sub_eq_add_neg, Prod.swap, Prod.fst, Prod.snd] using hh
  let κ : ℝ → ℂ := (Set.Ioc (0 : ℝ) 1).indicator (fun _ => 1)
  have hκ : Integrable κ := by
    exact (integrableOn_const (by simp : volume (Set.Ioc (0 : ℝ) 1) ≠ ⊤)).integrable_indicator measurableSet_Ioc
  have hiκ : (∫ s, κ s) = 1 := by
    simp [κ, integral_indicator measurableSet_Ioc, integral_const, Real.volume_Ioc]
  let K : ℝ × G → ℂ := fun p => κ (p.1 - L p.2) * w (a (p.1 - L p.2) * p.2)
  have hK : Integrable K (volume.prod ν) := by
    exact hU.integrable_comp_of_integrable (hT.integrable_comp_of_integrable (hκ.mul_prod hw))
  refine ⟨fun t => ∫ y, K (t, y) ∂ν, hK.integral_prod_left, ?_⟩
  intro φ hφ hb
  obtain ⟨C, hC⟩ := hb
  have hwφ : Integrable (fun y => w y * φ (L y)) ν :=
    hw.mul_bdd (hφ.measurable.comp hL).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hC _)
  have hf : Integrable (fun p : ℝ × G => κ p.1 * (w p.2 * φ (L p.2)))
      (volume.prod ν) := hκ.mul_prod hwφ
  have hp : (fun p : ℝ × G => κ p.1 * (w p.2 * φ (L p.2))) ∘ T ∘ U =
      fun p => K p * φ p.1 := by
    funext p
    dsimp [Function.comp_def, T, U, K]
    rw [hLa]
    simp only [sub_add_cancel]
    ring
  have hKφ : Integrable (fun p : ℝ × G => K p * φ p.1) (volume.prod ν) := by
    rw [← hp]
    exact hU.integrable_comp_of_integrable (hT.integrable_comp_of_integrable hf)
  have he := (hU.integral_comp U.measurableEmbedding _).trans
    (hT.integral_comp T.measurableEmbedding (fun p : ℝ × G => κ p.1 * (w p.2 * φ (L p.2))))
  change (∫ p, ((fun p : ℝ × G => κ p.1 * (w p.2 * φ (L p.2))) ∘ T ∘ U) p ∂volume.prod ν) = _ at he
  rw [hp, integral_prod _ hKφ] at he
  simp only [integral_mul_const] at he
  rw [integral_prod_mul κ (fun y => w y * φ (L y)), hiκ, one_mul] at he
  exact he.symm
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 512
 def realInto (F : Type) [Field F] [NumberField F] (v : InfinitePlace F) : ℝ →+* v.Completion :=
  if hv : v.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toRingHom
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex (v.not_isReal_iff_isComplex.mp hv)).symm.toRingHom.comp Complex.ofRealHom
private lemma realInto_norm {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (x : ℝ) :
    ‖realInto F v x‖ = ‖x‖ := by
  dsimp [realInto]
  split_ifs with hv
  · change ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm x‖ = |x|
    have hn := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
      (map_zero _) ((InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm x)
    simpa only [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      RingEquiv.apply_symm_apply, Real.norm_eq_abs] using hn.symm
  · have hn := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (v.not_isReal_iff_isComplex.mp hv)).symm (x : ℂ))
    change ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (v.not_isReal_iff_isComplex.mp hv)).symm (x : ℂ)‖ = |x|
    rw [← hn, show (InfinitePlace.Completion.extensionEmbedding v)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (v.not_isReal_iff_isComplex.mp hv)).symm (x : ℂ)) = (x : ℂ) from
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (v.not_isReal_iff_isComplex.mp hv)).apply_symm_apply (x : ℂ)]
    exact Complex.norm_real x
private lemma realInto_continuous {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) :
    Continuous (realInto F v) := by
  dsimp [realInto]
  split_ifs with hv
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (v.not_isReal_iff_isComplex.mp hv)).symm.continuous.comp Complex.continuous_ofReal
 def radial {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℝ) : (SLocalProduct F S)ˣ where
  val := ((fun v => realInto F v (Real.exp (s / (2 * Fintype.card (InfinitePlace F))))), 1)
  inv := ((fun v => realInto F v (Real.exp (-s / (2 * Fintype.card (InfinitePlace F))))), 1)
  val_inv := by
    apply Prod.ext
    · funext v
      change realInto F v _ * realInto F v _ = 1
      rw [← map_mul, ← Real.exp_add]
      rw [show _ + _ = (0 : ℝ) by ring, Real.exp_zero, map_one]
    · simp
  inv_val := by
    apply Prod.ext
    · funext v
      change realInto F v _ * realInto F v _ = 1
      rw [← map_mul, ← Real.exp_add]
      rw [show _ + _ = (0 : ℝ) by ring, Real.exp_zero, map_one]
    · simp
private lemma radial_continuous {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (radial S) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro v
    exact (realInto_continuous v).comp (by fun_prop)
  · apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro v
    exact (realInto_continuous v).comp (by fun_prop)
private lemma modulus_pos {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : (SLocalProduct F S)ˣ) :
    0 < ProbeWeight.modulus F S y := by
  apply mul_pos
  · apply Finset.prod_pos
    intro v _
    exact pow_pos (Units.norm_pos (Units.map
      ((Pi.evalMonoidHom (fun v : InfinitePlace F => v.Completion) v).comp
        (MonoidHom.fst _ _)) y)) _
  · apply Finset.prod_pos
    intro v _
    have hz : y.val.2 v ≠ 0 := by
      intro hz
      have he := congrArg (fun x : SLocalProduct F S => x.2 v) y.val_inv
      change y.val.2 v * y.inv.2 v = 1 at he
      rw [hz, zero_mul] at he
      exact zero_ne_one he
    exact norm_pos_iff.mpr hz

theorem modulus_mul
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y z : (SLocalProduct F S)ˣ) :
    ProbeWeight.modulus F S (y * z) =
      ProbeWeight.modulus F S y * ProbeWeight.modulus F S z := by
  have h1 : (∏ v : InfinitePlace F, ‖((y * z).val).1 v‖ ^ 2) =
      (∏ v, ‖(y.val).1 v‖ ^ 2) * ∏ v, ‖(z.val).1 v‖ ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [Units.val_mul, Prod.fst_mul]
    have h : ((y.val).1 * (z.val).1) v = (y.val).1 v * (z.val).1 v := Pi.mul_apply ..
    rw [h, norm_mul, mul_pow]
  have h2 : (∏ v : ↥S, ‖((y * z).val).2 v‖) =
      (∏ v, ‖(y.val).2 v‖) * ∏ v, ‖(z.val).2 v‖ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [Units.val_mul, Prod.snd_mul]
    have h : ((y.val).2 * (z.val).2) v = (y.val).2 v * (z.val).2 v := Pi.mul_apply ..
    rw [h, norm_mul]
  rw [ProbeWeight.modulus, ProbeWeight.modulus, ProbeWeight.modulus, h1, h2]
  ring

private lemma radial_modulus {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℝ) :
    ProbeWeight.modulus F S (radial S s) = Real.exp s := by
  have hn : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [ProbeWeight.modulus, radial, realInto_norm, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Pi.one_apply, norm_one, Finset.prod_const_one, mul_one]
  rw [Finset.prod_const, Finset.card_univ, ← pow_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp
 def prodUnitsD (M N : Type*) [Monoid M] [Monoid N]
    [TopologicalSpace M] [TopologicalSpace N] : (M × N)ˣ ≃ₜ* Mˣ × Nˣ where
  __ := MulEquiv.prodUnits
  continuous_toFun := Homeomorph.prodUnits.continuous
  continuous_invFun := Homeomorph.prodUnits.symm.continuous
 def prodCongrD {M N P Q : Type*} [Monoid M] [Monoid N] [Monoid P] [Monoid Q]
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] [TopologicalSpace Q]
    (e : M ≃ₜ* N) (f : P ≃ₜ* Q) : M × P ≃ₜ* N × Q where
  __ := e.toMulEquiv.prodCongr f.toMulEquiv
  continuous_toFun := e.continuous.prodMap f.continuous
  continuous_invFun := e.symm.continuous.prodMap f.symm.continuous
private lemma units_embedding {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Topology.IsEmbedding (Units.val : (SLocalProduct F S)ˣ → SLocalProduct F S) := by
  let e0 := (prodUnitsD (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)).trans
    (prodCongrD ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits)
  have hi := ((Topology.IsEmbedding.piMap (fun v : InfinitePlace F =>
    (Units.isEmbedding_val₀ (G₀ := v.Completion)))).prodMap
    (Topology.IsEmbedding.piMap (fun v : S =>
      (Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F)))))
  exact hi.comp e0.toHomeomorph.isEmbedding

theorem schwartzTensor_integrable_log_pushforward_density
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ)
    (hh : ProbeSheetVerticalDecay.IsSchwartzTensor F S h)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ q : ℝ → ℂ, Integrable q ∧
      ∀ φ : ℝ → ℂ, Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
        (∫ y : (SLocalProduct F S)ˣ,
          (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
            φ (Real.log (ProbeWeight.modulus F S y)) ∂ν) =
          ∫ t : ℝ, q t * φ t := by
  letI : MeasurableSpace (SLocalProduct F S) := borel _
  letI : BorelSpace (SLocalProduct F S) := ⟨rfl⟩
  letI : BorelSpace (SLocalProduct F S)ˣ := ⟨by
    change MeasurableSpace.comap Units.val (borel (SLocalProduct F S)) = borel _
    rw [(units_embedding S).isInducing.eq_induced, borel_comap]⟩
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : S) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : S) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  letI (v : InfinitePlace F) : SecondCountableTopology v.Completion := by
    by_cases hv : v.IsReal
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.secondCountableTopology
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (v.not_isReal_iff_isComplex.mp hv)).toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
  letI : SecondCountableTopology (SLocalProduct F S)ˣ := (units_embedding S).secondCountableTopology
  letI := hν
  letI : SFinite ν := inferInstance
  have hnorm : Continuous (fun x : SLocalProduct F S =>
      (∏ v : InfinitePlace F, ‖x.1 v‖ ^ (2 : ℕ)) * ∏ v : S, ‖x.2 v‖) := by
    fun_prop
  have hm : Measurable (ProbeWeight.modulus F S) := hnorm.measurable.comp Units.continuous_val.measurable
  have hrad : Measurable (radial S) := (radial_continuous S).measurable
  have hshift (s : ℝ) (y : (SLocalProduct F S)ˣ) :
      Real.log (ProbeWeight.modulus F S (radial S s * y)) =
        s + Real.log (ProbeWeight.modulus F S y) := by
    rw [modulus_mul, radial_modulus, Real.log_mul (Real.exp_ne_zero _) (modulus_pos S y).ne', Real.log_exp]
  have hw : Integrable (fun y : (SLocalProduct F S)ˣ =>
      h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) ν := by
    obtain ⟨c, gReal, gComplex, gFinite, hFinite, htensor⟩ := hh
    apply ProbeSheetGlobalIntegrability.tensor_units_mellin_integrable F S h c
      (fun v => (gReal v : ℝ → ℂ)) (fun v => (gComplex v : ℂ → ℂ))
      gFinite htensor (σ : ℂ) _ _ _ ν hν
    · intro v νv hνv
      letI := hνv
      exact ProbeSheetGlobalIntegrability.schwartz_realUnitsMellin_integrable
        (gReal v) νv (σ : ℂ) hσ
    · intro v νv hνv
      letI := hνv
      exact ProbeSheetFourierMellinBounds.schwartz_complexUnitsMellin_integrable_of_isHaarMeasure
        (gComplex v) νv (σ : ℂ) hσ
    · intro v νv hνv
      letI := hνv
      exact ProbeSheetGlobalIntegrability.finiteUnitsMellin_integrable F v.val
        (gFinite v) (hFinite v).1 (hFinite v).2 νv (σ : ℂ) hσ
  exact integrable_log_density_of_radial_section ν (fun y => Real.log (ProbeWeight.modulus F S y))
    (Real.measurable_log.comp hm) (radial S) hrad hshift _ hw

end
end DedekindZetaZeroFree.ProbeSheetLogDensity
