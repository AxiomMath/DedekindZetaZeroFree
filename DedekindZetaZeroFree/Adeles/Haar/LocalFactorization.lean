module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormOneFourierSheetEstimates
public import DedekindZetaZeroFree.Adeles.Haar.PolarProduct

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ProbeHaarFactorization
open MeasureTheory NumberField
open scoped Classical ENNReal
variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

lemma Measure.pi_update_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (i₀ : ι) (c : ℝ≥0∞)
    [∀ i, SigmaFinite (Function.update μ i₀ (c • μ i₀) i)] :
    Measure.pi (Function.update μ i₀ (c • μ i₀)) = c • Measure.pi μ := by
  refine Measure.pi_eq (fun s _hs => ?_)
  have hbox : ∏ i, Function.update μ i₀ (c • μ i₀) i (s i) = c * ∏ i, μ i (s i) := by
    have hstep : ∀ i, Function.update μ i₀ (c • μ i₀) i (s i) =
        (if i = i₀ then c else 1) * μ i (s i) := by
      intro i
      by_cases h : i = i₀
      · subst h; rw [Function.update_self, Measure.smul_apply, smul_eq_mul]; simp
      · rw [Function.update_of_ne h]; simp [h]
    have h1 : (∏ i, (if i = i₀ then c else 1)) = c := by
      rw [Finset.prod_eq_single (s := Finset.univ)
        (f := fun i => (if i = i₀ then c else 1)) (a := i₀)]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [Finset.prod_congr rfl (fun i _ => hstep i), Finset.prod_mul_distrib, h1]
  rw [Measure.smul_apply, Measure.pi_pi, hbox, smul_eq_mul]

private lemma polarUnit_continuous (A : SArithmeticData F) (w : InfinitePlace F) :
    Continuous (ThetaPositiveSheetMellin.polarUnit A w) := by
  unfold ThetaPositiveSheetMellin.polarUnit ThetaProfileHaarSheets.sqrtUnit
  apply Continuous.mul
  · apply (Units.continuous_map
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).symm.continuous).comp
    apply Units.isEmbedding_val₀.continuous_iff.mpr
    exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_subtype_val.comp continuous_fst))
  · exact (Units.continuous_map
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).symm.continuous).comp
      (show Continuous (fun p : ThetaProfileHaarSheets.PositiveAxis × Circle => p.2.toUnits) from
        Units.isEmbedding_val₀.continuous_iff.mpr
          (continuous_subtype_val.comp continuous_snd))

lemma productHaar_update_smul (A : SArithmeticData F)
    (μ : ∀ v : A.Sf, Measure (ThetaFiniteCutoff.LocalUnits A v))
    (ν : InfinitePlace F → Measure Circle)
    [∀ v, (μ v).IsHaarMeasure] [∀ w, (ν w).IsHaarMeasure]
    (w₀ : InfinitePlace F) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    ThetaPositiveSheetMellin.productHaar A μ (Function.update ν w₀ (c • ν w₀))
      = c • ThetaPositiveSheetMellin.productHaar A μ ν := by
  haveI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  haveI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => Units.isEmbedding_val₀.secondCountableTopology
  haveI : ∀ w : InfinitePlace F, LocallyCompactSpace w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  haveI : ∀ v : A.Sf, LocallyCompactSpace (v.val.adicCompletion F) :=
    (PoissonS.finite_components_locallyCompact F A.Sf).1
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : ∀ v : A.Sf, TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    fun v => TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  haveI : ∀ v : A.Sf, SecondCountableTopology (v.val.adicCompletion F) := fun v => inferInstance
  haveI : ∀ v : A.Sf, SecondCountableTopology (ThetaFiniteCutoff.LocalUnits A v) :=
    fun v => Units.isEmbedding_val₀.secondCountableTopology
  haveI : ∀ v : A.Sf, SigmaFinite (μ v) := fun v => inferInstance
  haveI : (c • ν w₀).IsHaarMeasure := by
    rw [← ENNReal.coe_toNNReal hct, ← ENNReal.smul_def]
    exact Measure.IsHaarMeasure.nnreal_smul _ (by
      intro h
      apply hc0
      rw [← ENNReal.coe_toNNReal hct, h]
      rfl)
  haveI : ∀ w, (Function.update ν w₀ (c • ν w₀) w).IsHaarMeasure := fun w => by
    by_cases h : w = w₀
    · subst w; simpa only [Function.update_self] using (inferInstance : (c • ν w₀).IsHaarMeasure)
    · simpa only [Function.update_of_ne h] using (inferInstance : (ν w).IsHaarMeasure)
  have hs (w : InfinitePlace F) :
      ThetaPositiveSheetMellin.archHaar A w (c • ν w) =
        c • ThetaPositiveSheetMellin.archHaar A w (ν w) := by
    unfold ThetaPositiveSheetMellin.archHaar
    rw [Measure.prod_smul_right, Measure.map_smul c (polarUnit_continuous A w).measurable.aemeasurable]
  have he : (fun w => ThetaPositiveSheetMellin.archHaar A w (Function.update ν w₀ (c • ν w₀) w)) =
      Function.update (fun w => ThetaPositiveSheetMellin.archHaar A w (ν w)) w₀
        (c • ThetaPositiveSheetMellin.archHaar A w₀ (ν w₀)) := by
    funext w
    by_cases h : w = w₀
    · subst w; simp only [Function.update_self, hs]
    · simp only [Function.update_of_ne h]
  haveI : ∀ w, SigmaFinite (ThetaPositiveSheetMellin.archHaar A w (ν w)) := fun w => inferInstance
  haveI : ∀ w, SigmaFinite (Function.update
      (fun w => ThetaPositiveSheetMellin.archHaar A w (ν w)) w₀
        (c • ThetaPositiveSheetMellin.archHaar A w₀ (ν w₀)) w) := by
    rw [← he]; infer_instance
  have hm : (Prod.instMeasurableSpace : MeasurableSpace A.G) =
      ThetaProfileHaarSheets.groupMeasurableSpace A :=
    (ThetaPositiveSheetMellin.groupMeasurableSpace_eq_prod A).symm
  unfold ThetaPositiveSheetMellin.productHaar
  rw [← hm, Measure.map_id', Measure.map_id', he, Measure.pi_update_smul,
    Measure.prod_smul_left]

theorem exists_productHaar_localUnits_eq (A : SArithmeticData F)
    (M : Measure (SLocalProduct F A.Sf)ˣ) [M.IsHaarMeasure] :
    ∃ (μ : ∀ v : A.Sf, Measure (ThetaFiniteCutoff.LocalUnits A v))
      (ν : InfinitePlace F → Measure Circle),
      (∀ v, (μ v).IsHaarMeasure) ∧ (∀ w, (ν w).IsHaarMeasure) ∧
      Measure.map (ProbeSheet.localUnits A)
        (ThetaPositiveSheetMellin.productHaar A μ ν) = M := by
  letI := ProbeSheet.locallyCompact_G A
  letI := ProbeSheet.secondCountable_G A
  letI : BorelSpace (SLocalProduct F A.Sf)ˣ := by
    constructor
    change (borel (SLocalProduct F A.Sf)).comap Units.val = borel _
    rw [← borel_comap, ← (ProbeSheet.units_val_isEmbedding A).isInducing.eq_induced]
  letI : LocallyCompactSpace (SLocalProduct F A.Sf)ˣ :=
    (ProbeSheet.localUnitsContinuous A).symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  letI : SecondCountableTopology (SLocalProduct F A.Sf)ˣ :=
    (ProbeSheet.localUnitsContinuous A).symm.toHomeomorph.secondCountableTopology
  letI : ∀ v : A.Sf, LocallyCompactSpace (v.val.adicCompletion F) :=
    (PoissonS.finite_components_locallyCompact F A.Sf).1
  let μ : ∀ v : A.Sf, Measure (ThetaFiniteCutoff.LocalUnits A v) := fun _ => Measure.haar
  let ν : InfinitePlace F → Measure Circle := fun _ => Measure.haar
  haveI : ∀ v, (μ v).IsHaarMeasure := fun v => by dsimp [μ]; infer_instance
  haveI : ∀ w, (ν w).IsHaarMeasure := fun w => by dsimp [ν]; infer_instance
  let M₀ := Measure.map (ProbeSheet.localUnits A) (ThetaPositiveSheetMellin.productHaar A μ ν)
  haveI : M₀.IsHaarMeasure :=
    (ProbeSheet.localUnitsContinuous A).isHaarMeasure_map _
  let c : NNReal := Measure.haarScalarFactor M M₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure M M₀).ne'
  let w₀ : InfinitePlace F := Classical.arbitrary _
  let ν' := Function.update ν w₀ (c • ν w₀)
  have hn : ∀ w, (ν' w).IsHaarMeasure := fun w => by
    by_cases h : w = w₀
    · subst w; dsimp [ν']; rw [Function.update_self]
      exact Measure.IsHaarMeasure.nnreal_smul _ hc
    · dsimp [ν']; rw [Function.update_of_ne h]; infer_instance
  refine ⟨μ, ν', fun _ => inferInstance, hn, ?_⟩
  have he : ThetaPositiveSheetMellin.productHaar A μ ν' =
      c • ThetaPositiveSheetMellin.productHaar A μ ν := by
    simpa only [ν', ENNReal.smul_def] using
      productHaar_update_smul A μ ν w₀ (c : ℝ≥0∞) (by exact_mod_cast hc) (by simp)
  have hm : Measurable (ProbeSheet.localUnits A) :=
    (ProbeSheet.localUnitsContinuous A).continuous.measurable
  rw [he, Measure.map_smul c hm.aemeasurable]
  exact (Measure.isMulLeftInvariant_eq_smul M M₀).symm

end DedekindZetaZeroFree.ProbeHaarFactorization

end
