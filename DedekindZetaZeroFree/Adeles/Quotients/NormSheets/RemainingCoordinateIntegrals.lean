module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.NormSheetLogarithmicOperators

@[expose] public section

namespace DedekindZetaZeroFree.NormSheetRemainingCoordinates
noncomputable section
set_option linter.style.haveILetI false
open scoped Classical NumberField NNReal
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩
 local instance fieldUnitsBorel {K : Type*} [Field K] [TopologicalSpace K]
    [ContinuousInv₀ K] [MeasurableSpace K] [BorelSpace K] : BorelSpace Kˣ := ⟨by
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K),
    (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]⟩

local instance normOneMeasurable (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance normOneBorel (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

abbrev RemainingComplex (w : {v : InfinitePlace F // v.IsComplex}) :=
  {v : {v : InfinitePlace F // v.IsComplex} // v ≠ w}

abbrev RemainingUnits (A : SArithmeticData F)
    (w : {v : InfinitePlace F // v.IsComplex}) :=
  ((v : RemainingComplex w) → ℂˣ) × ((v : ↥A.Sf) → (v.val.adicCompletion F)ˣ)

def remainingUnitsHom (A : SArithmeticData F)
    (w : {v : InfinitePlace F // v.IsComplex}) : A.G →* RemainingUnits A w where
  toFun y := (fun v => Units.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.val.property).toMonoidHom
      (y.1 v.val.val), y.2)
  map_one' := by ext <;> simp
  map_mul' := by intros; ext <;> simp

def remainingProjection (A : SArithmeticData F)
    (w : {v : InfinitePlace F // v.IsComplex}) : A.G1 →* RemainingUnits A w :=
  (remainingUnitsHom A w).comp A.G1.subtype

def rawSheetProjection (A : SArithmeticData F)
    (w : {v : InfinitePlace F // v.IsComplex}) (T : ℝ) (t : A.G1) :
    RemainingUnits A w :=
  remainingUnitsHom A w
    ((ProbeSheetFourierMellinBounds.localUnitsRaw A).symm (ProbeSheetFourierMellinBounds.sheetPointRaw A T t))

def remainingProductMeasure (A : SArithmeticData F)
    (w : {v : InfinitePlace F // v.IsComplex})
    (νComplex : RemainingComplex w → Measure ℂˣ)
    (νFinite : (v : ↥A.Sf) → Measure (v.val.adicCompletion F)ˣ) :
    Measure (RemainingUnits A w) :=
  (Measure.pi νComplex).prod (Measure.pi νFinite)

private theorem continuous_remainingUnitsHom (A : SArithmeticData F)
    (w : {v : InfinitePlace F // v.IsComplex}) : Continuous (remainingUnitsHom A w) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    exact (Units.continuous_map
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex v.val.property).continuous).comp
        ((continuous_apply v.val.val).comp continuous_fst)
  · exact continuous_snd

private theorem rawSheetProjection_eq (A : SArithmeticData F)
    (w : {v : InfinitePlace F // v.IsComplex}) (T : ℝ) (t : A.G1) :
    rawSheetProjection A w T t = remainingProjection A w t *
      remainingUnitsHom A w ((ProbeSheetFourierMellinBounds.localUnitsRaw A).symm
        (ProbeSheetFourierMellinBounds.ellRaw A T)) := by
  simp [rawSheetProjection, ProbeSheetFourierMellinBounds.sheetPointRaw, remainingProjection,
    MonoidHom.comp_apply]

private theorem complex_norm (v : {v : InfinitePlace F // v.IsComplex}) (z : v.val.Completion) :
    ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property z‖ = ‖z‖ := by
  have h := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex v.property).dist_eq z 0
  change dist (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property z)
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property 0) = _ at h
  simpa [dist_zero_right] using h
 def fill (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (z : ℂˣ) (y : RemainingUnits A w) : A.G :=
  (fun v => Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v)).symm.toMonoidHom
    (if hv : v = w.val then z else y.1 ⟨⟨v, A.complex_place v⟩, by intro h; exact hv (congrArg Subtype.val h)⟩), y.2)
private theorem projection_fill (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (z : ℂˣ) (y : RemainingUnits A w) : remainingUnitsHom A w (fill A w z y) = y := by
  ext v
  · have hv : v.val.val ≠ w.val := fun h => v.property (Subtype.ext h)
    simp [remainingUnitsHom, fill, hv]
  · rfl
 theorem norm_fill (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (z : ℂˣ) (y : RemainingUnits A w) :
    A.norm (fill A w z y) = ‖z.val‖ ^ 2 *
      ((∏ v : RemainingComplex w, ‖(y.1 v).val‖ ^ 2) * ∏ v : ↥A.Sf, ‖(y.2 v).val‖) := by
  have he (v : InfinitePlace F) (u : ℂˣ) :
      ‖((Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v)).symm.toMonoidHom u).val)‖ = ‖u.val‖ := by
    rw [← complex_norm ⟨v, A.complex_place v⟩]
    simp
  unfold SArithmeticData.norm fill
  simp only [he]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w.val)]
  simp only [dif_pos rfl]
  rw [mul_assoc]
  congr 1
  congr 1
  have hprod : (∏ v ∈ Finset.univ.erase w.val,
    ‖(if hv : v = w.val then z else y.1 ⟨⟨v, A.complex_place v⟩, by intro h; exact hv (congrArg Subtype.val h)⟩).val‖ ^ 2) =
      ∏ v : {v : InfinitePlace F // v ≠ w.val}, ‖(y.1 ⟨⟨v.val, A.complex_place v.val⟩, by intro h; exact v.property (congrArg Subtype.val h)⟩).val‖ ^ 2 := by
    rw [Finset.prod_subtype (p := fun v => v ≠ w.val) (Finset.univ.erase w.val) (fun v => by simp)
      (fun v => ‖(if hv : v = w.val then z else y.1 ⟨⟨v, A.complex_place v⟩, by intro h; exact hv (congrArg Subtype.val h)⟩).val‖ ^ 2)]
    apply Finset.prod_congr rfl
    intro v hv
    simp [v.property]
  rw [hprod]
  let e : {v : InfinitePlace F // v ≠ w.val} ≃ RemainingComplex w :=
    { toFun := fun v => ⟨⟨v.val, A.complex_place v.val⟩, by intro h; exact v.property (congrArg Subtype.val h)⟩
      invFun := fun v => ⟨v.val.val, fun h => v.property (Subtype.ext h)⟩
      left_inv := by intro; rfl
      right_inv := by intro; rfl }
  exact Fintype.prod_equiv e _ _ (fun v => rfl)
 def remNorm (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (y : RemainingUnits A w) : ℝ :=
  ((∏ v : RemainingComplex w, ‖(y.1 v).val‖ ^ 2) * ∏ v : ↥A.Sf, ‖(y.2 v).val‖)
private theorem remNorm_pos (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (y : RemainingUnits A w) : 0 < remNorm A w y :=
  mul_pos (Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.mpr (y.1 v).ne_zero) _)
    (Finset.prod_pos fun v _ => norm_pos_iff.mpr (y.2 v).ne_zero)
 def radius (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (y : RemainingUnits A w) : ℝ := Real.sqrt (remNorm A w y)⁻¹
 theorem radius_pos (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (y : RemainingUnits A w) : 0 < radius A w y := Real.sqrt_pos.mpr (inv_pos.mpr (remNorm_pos A w y))
 def radiusUnit (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (y : RemainingUnits A w) : ℂˣ :=
  Units.mk0 (radius A w y : ℂ) (Complex.ofReal_ne_zero.mpr (radius_pos A w y).ne')
 theorem norm_radiusUnit (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (y : RemainingUnits A w) : ‖(radiusUnit A w y).val‖ ^ 2 * remNorm A w y = 1 := by
  simp only [radiusUnit, Units.val_mk0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (radius_pos A w y)]
  rw [radius, Real.sq_sqrt (inv_nonneg.mpr (remNorm_pos A w y).le), inv_mul_cancel₀ (remNorm_pos A w y).ne']
 def remainingSection (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (y : RemainingUnits A w) : A.G1 :=
  ⟨fill A w (radiusUnit A w y) y, by
    change A.norm _ = 1
    rw [norm_fill]
    exact norm_radiusUnit A w y⟩
private theorem surjective_remainingProjection (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex}) :
    Function.Surjective (remainingProjection A w) := by
  intro y
  exact ⟨remainingSection A w y, projection_fill A w _ y⟩
private theorem fill_projection (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (t : A.G1) : fill A w
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property).toMonoidHom (t.val.1 w.val))
      (remainingProjection A w t) = t.val := by
  apply Prod.ext
  · funext v
    by_cases hv : v = w.val
    · subst v
      dsimp only [fill]
      rw [dif_pos rfl]
      apply Units.ext
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property).symm
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property) (t.val.1 w.val).val) = _
      exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property).symm_apply_apply _)
    · dsimp only [fill]
      rw [dif_neg hv]
      apply Units.ext
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v)).symm
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v)) (t.val.1 v).val) = _
      exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v)).symm_apply_apply _
  · rfl
private theorem continuous_fill (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex}) :
    Continuous (fun p : ℂˣ × RemainingUnits A w => fill A w p.1 p.2) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    apply (Units.continuous_map
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place v)).symm.continuous).comp
    by_cases hv : v = w.val
    · simpa [fill, hv] using (continuous_fst : Continuous (fun p : ℂˣ × RemainingUnits A w => p.1))
    · simpa [fill, hv] using ((continuous_apply _).comp (continuous_fst.comp continuous_snd) :
        Continuous (fun p : ℂˣ × RemainingUnits A w => p.2.1 ⟨⟨v, A.complex_place v⟩, by intro h; exact hv (congrArg Subtype.val h)⟩))
  · exact continuous_snd.comp continuous_snd

private theorem continuous_radiusUnit (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex}) :
    Continuous (radiusUnit A w) := by
  have hn : Continuous (remNorm A w) := by unfold remNorm; fun_prop
  have hr : Continuous (radius A w) :=
    Real.continuous_sqrt.comp (hn.inv₀ fun y => (remNorm_pos A w y).ne')
  apply Units.continuous_iff.mpr
  constructor
  · exact Complex.continuous_ofReal.comp hr
  · change Continuous (fun y => (radius A w y : ℂ)⁻¹)
    exact (Complex.continuous_ofReal.comp hr).inv₀ fun y =>
      Complex.ofReal_ne_zero.mpr (radius_pos A w y).ne'
 def circleFill (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (p : Circle × RemainingUnits A w) : A.G1 :=
  ⟨fill A w (Circle.toUnits p.1 * radiusUnit A w p.2) p.2, by
    change A.norm _ = 1
    rw [norm_fill]
    simpa only [Units.val_mul, norm_mul, Circle.toUnits_apply, Units.val_mk0,
      Circle.norm_coe, one_mul, remNorm] using norm_radiusUnit A w p.2⟩
private theorem continuous_circleFill (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex}) :
    Continuous (circleFill A w) := by
  apply Continuous.subtype_mk
  change Continuous ((fun p : ℂˣ × RemainingUnits A w => fill A w p.1 p.2) ∘
    (fun x : Circle × RemainingUnits A w => (Circle.toUnits x.1 * radiusUnit A w x.2, x.2)))
  apply (continuous_fill A w).comp
  apply Continuous.prodMk _ continuous_snd
  apply Continuous.mul _ ((continuous_radiusUnit A w).comp continuous_snd)
  apply Continuous.comp _ continuous_fst
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · exact continuous_subtype_val.inv₀ fun z => Circle.coe_ne_zero z
private theorem projection_circleFill (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (p : Circle × RemainingUnits A w) : remainingProjection A w (circleFill A w p) = p.2 :=
  projection_fill A w _ _
private theorem circleFill_covers (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (t : A.G1) : ∃ z : Circle, circleFill A w (z, remainingProjection A w t) = t := by
  let y := remainingProjection A w t
  let u := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property).toMonoidHom (t.val.1 w.val)
  have hn : ‖u.val‖ ^ 2 * remNorm A w y = 1 := by
    change ‖u.val‖ ^ 2 * ((∏ v : RemainingComplex w, ‖(y.1 v).val‖ ^ 2) * ∏ v : ↥A.Sf, ‖(y.2 v).val‖) = 1
    rw [← norm_fill, fill_projection]
    exact t.property
  have hr := norm_radiusUnit A w y
  have hu : ‖u.val‖ = radius A w y := by
    have heq : ‖u.val‖ ^ 2 = radius A w y ^ 2 := by
      apply (mul_right_cancel₀ (remNorm_pos A w y).ne')
      simpa only [radiusUnit, Units.val_mk0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (radius_pos A w y)] using hn.trans hr.symm
    nlinarith [norm_nonneg u.val, radius_pos A w y]
  let z : Circle := ⟨(u / radiusUnit A w y).val, by
    apply mem_sphere_zero_iff_norm.mpr
    simp only [ Units.val_div_eq_div_val, norm_div, radiusUnit, Units.val_mk0,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (radius_pos A w y), hu,
      div_self (radius_pos A w y).ne']⟩
  refine ⟨z, Subtype.ext ?_⟩
  have hz : Circle.toUnits z = u / radiusUnit A w y := Units.ext rfl
  change fill A w (Circle.toUnits z * radiusUnit A w y) y = t.val
  rw [hz, div_mul_cancel]
  exact fill_projection A w t
private theorem compact_preimage_remainingProjection (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (K : Set (RemainingUnits A w)) (hK : IsCompact K) :
    IsCompact (remainingProjection A w ⁻¹' K) := by
  have heq : remainingProjection A w ⁻¹' K = circleFill A w '' (Set.univ ×ˢ K) := by
    ext t
    constructor
    · intro ht
      obtain ⟨z, hz⟩ := circleFill_covers A w t
      exact ⟨(z, remainingProjection A w t), ⟨Set.mem_univ _, ht⟩, hz⟩
    · rintro ⟨p, hp, rfl⟩
      simpa only [Set.mem_preimage, projection_circleFill] using hp.2
  rw [heq]
  exact (isCompact_univ.prod hK).image (continuous_circleFill A w)

theorem raw_remaining_projection_haar
    (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (dt : @Measure A.G1 (borel _))
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (νComplex : RemainingComplex w → Measure ℂˣ)
    (hνComplex : ∀ v, (νComplex v).IsHaarMeasure)
    (νFinite : (v : ↥A.Sf) → Measure (v.val.adicCompletion F)ˣ)
    (hνFinite : ∀ v, (νFinite v).IsHaarMeasure) :
    Continuous (remainingProjection A w) ∧
    Function.Surjective (remainingProjection A w) ∧
    IsCompact ((remainingProjection A w).ker : Set A.G1) ∧
    Filter.Tendsto (remainingProjection A w) (Filter.cocompact A.G1)
      (Filter.cocompact (RemainingUnits A w)) ∧
    ∃ c : ℝ≥0, c ≠ 0 ∧
      Measure.map (remainingProjection A w) dt =
        c • remainingProductMeasure A w νComplex νFinite ∧
      ∀ T : ℝ, 0 < T →
        Measure.map (rawSheetProjection A w T) dt =
          c • remainingProductMeasure A w νComplex νFinite  := by
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ v : ↥A.Sf, TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    fun v => TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI : ∀ v : ↥A.Sf, SecondCountableTopology (v.val.adicCompletion F) := fun v => inferInstance
  letI : ∀ v : ↥A.Sf, SecondCountableTopology (v.val.adicCompletion F)ᵐᵒᵖ :=
    fun v => MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : ∀ v : ↥A.Sf, SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    fun v => Units.isEmbedding_embedProduct.secondCountableTopology
  letI := hdt
  letI : ∀ v, (νComplex v).IsHaarMeasure := hνComplex
  letI : ∀ v, (νFinite v).IsHaarMeasure := hνFinite
  letI : ∀ v, SigmaFinite (νComplex v) := fun v => inferInstance
  letI : ∀ v, SigmaFinite (νFinite v) := fun v => inferInstance
  have hp : Continuous (remainingProjection A w) :=
    (continuous_remainingUnitsHom A w).comp continuous_subtype_val
  have hs : Function.Surjective (remainingProjection A w) := surjective_remainingProjection A w
  have hk : IsCompact ((remainingProjection A w).ker : Set A.G1) :=
    compact_preimage_remainingProjection A w {1} isCompact_singleton
  have ht : Filter.Tendsto (remainingProjection A w) (Filter.cocompact A.G1)
      (Filter.cocompact (RemainingUnits A w)) := by
    apply Filter.hasBasis_cocompact.tendsto_right_iff.mpr
    intro K hK
    exact (compact_preimage_remainingProjection A w K hK).compl_mem_cocompact
  letI : (remainingProductMeasure A w νComplex νFinite).IsHaarMeasure := by
    unfold remainingProductMeasure
    infer_instance
  letI : (Measure.map (remainingProjection A w) dt).IsHaarMeasure :=
    Measure.isHaarMeasure_map dt (remainingProjection A w) hp hs ht
  let c := Measure.haarScalarFactor (Measure.map (remainingProjection A w) dt)
    (remainingProductMeasure A w νComplex νFinite)
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have hm : Measure.map (remainingProjection A w) dt =
      c • remainingProductMeasure A w νComplex νFinite :=
    Measure.isMulLeftInvariant_eq_smul _ _
  refine ⟨hp, hs, hk, ht, c, hc, hm, ?_⟩
  intro T hT
  have heq : rawSheetProjection A w T =
      (fun y => remainingUnitsHom A w ((ProbeSheetFourierMellinBounds.localUnitsRaw A).symm
        (ProbeSheetFourierMellinBounds.ellRaw A T)) * y) ∘ remainingProjection A w := by
    funext t
    rw [rawSheetProjection_eq, mul_comm]
    rfl
  rw [heq, ← Measure.map_map (measurable_const_mul _) hp.measurable,
    hm, Measure.map_smul, map_mul_left_eq_self]
  exact (measurable_const_mul _).aemeasurable

theorem raw_remaining_tensor_integral_bound
    (A : SArithmeticData F) (w : {v : InfinitePlace F // v.IsComplex})
    (dt : @Measure A.G1 (borel _))
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (aComplex : {v : InfinitePlace F // v.IsComplex} → ℂ → ℝ)
    (aFinite : (v : ↥A.Sf) → v.val.adicCompletion F → ℝ)
    (hComplexContinuous : ∀ v, Continuous (aComplex v))
    (hFiniteContinuous : ∀ v, Continuous (aFinite v))
    (hComplexNonneg : ∀ v z, 0 ≤ aComplex v z)
    (hFiniteNonneg : ∀ v z, 0 ≤ aFinite v z)
    (νComplex : RemainingComplex w → Measure ℂˣ)
    (hνComplex : ∀ v, (νComplex v).IsHaarMeasure)
    (νFinite : (v : ↥A.Sf) → Measure (v.val.adicCompletion F)ˣ)
    (hνFinite : ∀ v, (νFinite v).IsHaarMeasure)
    (hComplexIntegrable : ∀ v : RemainingComplex w,
      Integrable (fun z : ℂˣ => aComplex v.val z.val) (νComplex v))
    (hFiniteIntegrable : ∀ v : ↥A.Sf,
      Integrable (fun z : (v.val.adicCompletion F)ˣ => aFinite v z.val) (νFinite v)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 < T →
      Integrable (fun t : A.G1 =>
        (∏ v ∈ Finset.univ.erase w,
          aComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F
            (ProbeSheetFourierMellinBounds.sheetPointRaw A T t).val.1).2 v)) *
        ∏ v : ↥A.Sf, aFinite v ((ProbeSheetFourierMellinBounds.sheetPointRaw A T t).val.2 v)) dt ∧
      (∫ t : A.G1,
        (∏ v ∈ Finset.univ.erase w,
          aComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F
            (ProbeSheetFourierMellinBounds.sheetPointRaw A T t).val.1).2 v)) *
        ∏ v : ↥A.Sf, aFinite v ((ProbeSheetFourierMellinBounds.sheetPointRaw A T t).val.2 v) ∂dt) ≤ B := by
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ v : ↥A.Sf, TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    fun v => TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI : ∀ v : ↥A.Sf, SecondCountableTopology (v.val.adicCompletion F) := fun v => inferInstance
  letI : ∀ v : ↥A.Sf, SecondCountableTopology (v.val.adicCompletion F)ᵐᵒᵖ :=
    fun v => MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : ∀ v : ↥A.Sf, SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    fun v => Units.isEmbedding_embedProduct.secondCountableTopology
  letI := hdt
  letI : ∀ v, (νComplex v).IsHaarMeasure := hνComplex
  letI : ∀ v, (νFinite v).IsHaarMeasure := hνFinite
  letI : ∀ v, SigmaFinite (νComplex v) := fun v => inferInstance
  letI : ∀ v, SigmaFinite (νFinite v) := fun v => inferInstance
  let f : RemainingUnits A w → ℝ := fun y =>
    (∏ v : RemainingComplex w, aComplex v.val (y.1 v).val) *
      ∏ v : ↥A.Sf, aFinite v (y.2 v).val
  have hf : Integrable f (remainingProductMeasure A w νComplex νFinite) :=
    (Integrable.fintype_prod hComplexIntegrable).mul_prod
      (Integrable.fintype_prod_dep hFiniteIntegrable)
  have hfcont : Continuous f := by
    apply Continuous.mul
    · exact continuous_finsetProd _ fun v _ =>
        (hComplexContinuous v.val).comp
          (Units.continuous_val.comp ((continuous_apply v).comp continuous_fst))
    · exact continuous_finsetProd _ fun v _ =>
        (hFiniteContinuous v).comp
          (Units.continuous_val.comp ((continuous_apply v).comp continuous_snd))
  obtain ⟨hp, _, _, _, c, hc, _, hmap⟩ :=
    raw_remaining_projection_haar A w dt hdt νComplex hνComplex νFinite hνFinite
  refine ⟨(c : ℝ) * (∫ y, f y ∂remainingProductMeasure A w νComplex νFinite), ?_, ?_⟩
  · apply mul_nonneg c.coe_nonneg
    apply integral_nonneg
    intro y
    exact mul_nonneg (Finset.prod_nonneg fun v _ => hComplexNonneg v.val _)
      (Finset.prod_nonneg fun v _ => hFiniteNonneg v _)
  · intro T hT
    have hpT : Continuous (rawSheetProjection A w T) := by
      change Continuous (fun t => rawSheetProjection A w T t)
      simp_rw [rawSheetProjection_eq]
      exact hp.mul continuous_const
    have hfmap : Integrable f (Measure.map (rawSheetProjection A w T) dt) := by
      rw [hmap T hT]
      exact hf.smul_measure_nnreal
    have heq : (fun t : A.G1 =>
        (∏ v ∈ Finset.univ.erase w,
          aComplex v ((InfiniteAdeleRing.ringEquiv_mixedSpace F
            (ProbeSheetFourierMellinBounds.sheetPointRaw A T t).val.1).2 v)) *
        ∏ v : ↥A.Sf, aFinite v ((ProbeSheetFourierMellinBounds.sheetPointRaw A T t).val.2 v)) =
        f ∘ rawSheetProjection A w T := by
      funext t
      dsimp [f, Function.comp_def]
      congr 1
      exact Finset.prod_subtype _ (fun v => by simp) _
    rw [heq]
    refine ⟨hfmap.comp_measurable hpT.measurable, ?_⟩
    have hi := integral_map (μ := dt) hpT.measurable.aemeasurable
      hfcont.aestronglyMeasurable
    rw [hmap T hT, integral_smul_nnreal_measure] at hi
    exact le_of_eq hi.symm

end
end DedekindZetaZeroFree.NormSheetRemainingCoordinates
