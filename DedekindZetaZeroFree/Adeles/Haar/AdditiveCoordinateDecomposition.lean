module

public import DedekindZetaZeroFree.Adeles.Haar.FiniteRestrictedProductMeasure
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicRationalSplitting

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.AdditiveCoordinate
open KPAdelicCoverRestrictedProduct
local notation "KPAdeles" => Adeles
variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
set_option backward.isDefEq.respectTransparency false

def Away : AddSubgroup (KPAdeles F) :=
  (adeleEval F (Sum.inr q)).toAddMonoidHom.ker

def single : q.adicCompletion F →+ KPAdeles F where
  toFun := KPRationalAdelicSplitting.localAdele F (Sum.inr q)
  map_zero' := by
    apply Prod.ext <;> simp [KPRationalAdelicSplitting.localAdele]
  map_add' x y := by
    apply Prod.ext
    · change (0 : InfiniteAdeleRing F) = 0 + 0
      simp
    · exact RestrictedProduct.single_add _ _ _ _

@[simp] theorem eval_single (y : q.adicCompletion F) :
    adeleEval F (Sum.inr q) (single F q y) = y := by
  change RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) q y q = y
  exact RestrictedProduct.single_eq_same _ _ _

theorem continuous_eval : Continuous (adeleEval F (Sum.inr q)) :=
  (RestrictedProduct.continuous_eval q).comp continuous_snd

theorem continuous_single : Continuous (single F q) := by
  let s : Set (HeightOneSpectrum (𝓞 F)) := {q}ᶜ
  have hs : Filter.cofinite ≤ Filter.principal s :=
    Filter.le_principal_iff.mpr (Set.finite_singleton q).compl_mem_cofinite
  let f : q.adicCompletion F → RestrictedProduct (fun w => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set _)) (Filter.principal s) := fun x =>
    ⟨Pi.single q x, by
      intro w hw
      have hwq : w ≠ q := hw
      simpa [Pi.single_eq_of_ne hwq] using (w.adicCompletionIntegers F).zero_mem⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (_root_.continuous_single q)
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hs).comp hf)

theorem away_isClosed : IsClosed (Away F q : Set (KPAdeles F)) :=
  isClosed_singleton.preimage (continuous_eval F q)

instance : LocallyCompactSpace (Away F q) :=
  (away_isClosed F q).locallyCompactSpace

def join : (Away F q × q.adicCompletion F) ≃+ KPAdeles F where
  toFun p := p.1.val + single F q p.2
  invFun x := (⟨x - single F q (adeleEval F (Sum.inr q) x), by
    change adeleEval F (Sum.inr q) (_ - _) = 0
    rw [map_sub, eval_single, sub_self]⟩, adeleEval F (Sum.inr q) x)
  left_inv p := by
    have hp : adeleEval F (Sum.inr q) p.1.val = 0 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change _ + _ - single F q (adeleEval F (Sum.inr q) (p.1.val + single F q p.2)) = _
      rw [map_add, hp, eval_single F q, zero_add, add_sub_cancel_right]
    · change adeleEval F (Sum.inr q) (p.1.val + single F q p.2) = _
      rw [map_add, hp, eval_single F q, zero_add]
  right_inv x := sub_add_cancel _ _
  map_add' p r := by simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, map_add]; abel

theorem continuous_join : Continuous (join F q) :=
  (continuous_subtype_val.comp continuous_fst).add ((continuous_single F q).comp continuous_snd)

theorem continuous_join_symm : Continuous (join F q).symm :=
  ((continuous_id.sub ((continuous_single F q).comp (continuous_eval F q))).subtype_mk _).prodMk
    (continuous_eval F q)

local instance : SecondCountableTopology (InfiniteAdeleRing F) :=
  (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.isEmbedding.secondCountableTopology

instance : SecondCountableTopology (Away F q) :=
  (away_isClosed F q).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

local instance : SecondCountableTopology (q.adicCompletion F) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : TopologicalSpace.SeparableSpace (q.adicCompletion F) :=
    ⟨⟨Set.range (algebraMap F (q.adicCompletion F)), Set.countable_range _,
      HeightOneSpectrum.denseRange_algebraMap F q⟩⟩
  infer_instance

local instance : SigmaCompactSpace (InfiniteAdeleRing F) :=
  (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.isClosedEmbedding.sigmaCompactSpace

instance : SigmaCompactSpace (Away F q) :=
  (away_isClosed F q).sigmaCompactSpace

local instance : (KPAdditiveHaar.adelicMeasure F).IsAddHaarMeasure :=
  KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F

local instance : (Measure.map (join F q).symm (KPAdditiveHaar.adelicMeasure F)).IsAddHaarMeasure :=
  (join F q).symm.isAddHaarMeasure_map _ (continuous_join_symm F q) (continuous_join F q)

def awayMeasure (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure] : Measure (Away F q) :=
  (Measure.addHaarScalarFactor
    (Measure.map (join F q).symm (KPAdditiveHaar.adelicMeasure F))
    ((Measure.addHaar : Measure (Away F q)).prod μ) : ℝ≥0∞) • Measure.addHaar

theorem split_measure (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure] :
    Measure.map (join F q).symm (KPAdditiveHaar.adelicMeasure F) =
      (awayMeasure F q μ).prod μ := by
  letI := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  letI : (Measure.map (join F q).symm (KPAdditiveHaar.adelicMeasure F)).IsAddHaarMeasure :=
    (join F q).symm.isAddHaarMeasure_map _ (continuous_join_symm F q) (continuous_join F q)
  rw [awayMeasure, Measure.prod_smul_left]
  exact Measure.isAddLeftInvariant_eq_smul _ _

instance awayMeasure_isAddHaarMeasure (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure] :
    (awayMeasure F q μ).IsAddHaarMeasure := by
  unfold awayMeasure
  apply Measure.IsAddHaarMeasure.smul
  · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (Measure.map (join F q).symm (KPAdditiveHaar.adelicMeasure F))
      ((Measure.addHaar : Measure (Away F q)).prod μ)).ne'
  · exact ENNReal.coe_ne_top

theorem join_measurePreserving (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure] :
    MeasurePreserving (join F q) ((awayMeasure F q μ).prod μ)
      (KPAdditiveHaar.adelicMeasure F) := by
  refine ⟨(continuous_join F q).measurable, ?_⟩
  rw [← split_measure F q μ, Measure.map_map (continuous_join F q).measurable
    (continuous_join_symm F q).measurable]
  simp only [Function.comp_def, AddEquiv.apply_symm_apply]
  exact @Measure.map_id' (KPAdeles F) _ (KPAdditiveHaar.adelicMeasure F)

end DedekindZetaZeroFree.FourierContinuation.AdditiveCoordinate

end
