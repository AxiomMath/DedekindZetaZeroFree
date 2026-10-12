module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.BoxFiberIntegral

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming adelic_measure_box → adelic_measure_box
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming finite_measure_sigmaFinite → finite_measure_sigmaFinite
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming arch_measure_sigmaFinite → arch_measure_sigmaFinite
local instance currentArchMeasurable (F : Type) [Field F] [NumberField F] : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance currentArchBorel (F : Type) [Field F] [NumberField F] : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
namespace DedekindZetaZeroFree.FourierContinuation.CurrentBoxProductHaar
open KPLocalPrincipalSeries KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable (F : Type) [Field F] [NumberField F]
set_option backward.isDefEq.respectTransparency false

theorem chart_integral (Q : Finset (KPFinitePlace F))
    (f : (∀ q : Q, q.val.adicCompletion F) → ℂ) :
    (∫ x : KPAdditiveHaar.Chart F Q, f x.1 ∂KPAdditiveHaar.chartMeasure F Q) =
      ∫ x, f x ∂Measure.pi (fun q : Q => localNormalizedHaar F q.val) := by
  let : ∀ q : {q : KPFinitePlace F // q ∉ Q},
      IsProbabilityMeasure (KPAdditiveHaar.integerProbabilityMeasure F q.val) :=
    fun q => KPAdditiveHaar.integerProbabilityMeasure_isProbabilityMeasure F q.val
  have h := integral_fun_fst
    (μ := Measure.pi (fun q : Q => localNormalizedHaar F q.val))
    (ν := Measure.infinitePi (fun q : {q : KPFinitePlace F // q ∉ Q} =>
      KPAdditiveHaar.integerProbabilityMeasure F q.val)) f
  simpa only [KPAdditiveHaar.chartMeasure, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using h

theorem box_product_integral (Q : Finset (KPFinitePlace F))
    (hD : localDifferentSupport F ⊆ (Q : Set _))
    (f : InfiniteAdeleRing F → ℂ) (g : (∀ q : Q, q.val.adicCompletion F) → ℂ) :
    (∫ x : KPGlobalTorusFunctionData.Adeles F, f x.1 * g (fun q => x.2 q.val)
      ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
      (∫ x, f x ∂KPAdditiveHaar.archMeasure F) *
      (∫ y, g y ∂Measure.pi (fun q : Q => localNormalizedHaar F q.val)) := by
  let := finite_measure_sigmaFinite F
  let := arch_measure_sigmaFinite F
  let e : (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ≃ₜ
      KPGlobalTorusFunctionData.Adeles F := Homeomorph.refl _
  have he : @MeasurableEmbedding (InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (KPGlobalTorusFunctionData.Adeles F)
      inferInstance inferInstance (fun a => a) := e.measurableEmbedding
  rw [adelic_measure_box F Q, he.integral_map]
  change (∫ x : InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F,
    f x.1 * g (fun q => x.2 q.val) ∂_) = _
  rw [integral_prod_mul f (fun a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F => g (fun q => a q.val)),
    KPAdditiveHaar.finiteMeasure_chart F Q hD,
    (KPAdditiveHaar.chartMap_isOpenEmbedding F Q).measurableEmbedding.integral_map]
  have hc : (fun b : KPAdditiveHaar.Chart F Q =>
      g (fun q => KPAdditiveHaar.chartMap F Q b q.val)) = fun b => g b.1 := by
    funext b
    apply congrArg g
    funext q
    change (if h : q.val ∈ Q then b.1 ⟨q.val,h⟩ else _) = b.1 q
    rw [dite_eq_left q.property]
  rw [hc, chart_integral]

theorem finite_head_integrable (Q : Finset (KPFinitePlace F))
    (hD : localDifferentSupport F ⊆ (Q : Set _))
    (g : (∀ q : Q, q.val.adicCompletion F) → ℂ)
    (hg : Integrable g (Measure.pi (fun q : Q => localNormalizedHaar F q.val))) :
    Integrable (fun a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F => g (fun q => a q.val))
      ((KPAdditiveHaar.finiteMeasure F).restrict (Set.range (KPAdditiveHaar.chartMap F Q))) := by
  rw [KPAdditiveHaar.finiteMeasure_chart F Q hD,
    (KPAdditiveHaar.chartMap_isOpenEmbedding F Q).measurableEmbedding.integrable_map_iff]
  have hc : (fun b : KPAdditiveHaar.Chart F Q =>
      g (fun q => KPAdditiveHaar.chartMap F Q b q.val)) = fun b => g b.1 := by
    funext b
    apply congrArg g
    funext q
    change (if h : q.val ∈ Q then b.1 ⟨q.val,h⟩ else _) = b.1 q
    rw [dite_eq_left q.property]
  change Integrable (fun b => g (fun q => KPAdditiveHaar.chartMap F Q b q.val)) _
  rw [hc]
  let : ∀ q : {q : KPFinitePlace F // q ∉ Q},
      IsProbabilityMeasure (KPAdditiveHaar.integerProbabilityMeasure F q.val) :=
    fun q => KPAdditiveHaar.integerProbabilityMeasure_isProbabilityMeasure F q.val
  exact hg.comp_fst _

theorem box_product_integrable (Q : Finset (KPFinitePlace F))
    (hD : localDifferentSupport F ⊆ (Q : Set _))
    (f : InfiniteAdeleRing F → ℂ) (g : (∀ q : Q, q.val.adicCompletion F) → ℂ)
    (hf : Integrable f (KPAdditiveHaar.archMeasure F))
    (hg : Integrable g (Measure.pi (fun q : Q => localNormalizedHaar F q.val))) :
    Integrable (fun x : KPGlobalTorusFunctionData.Adeles F => f x.1 * g (fun q => x.2 q.val))
      ((KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) := by
  let := finite_measure_sigmaFinite F
  let := arch_measure_sigmaFinite F
  let e : (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ≃ₜ
      KPGlobalTorusFunctionData.Adeles F := Homeomorph.refl _
  have he : @MeasurableEmbedding (InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (KPGlobalTorusFunctionData.Adeles F)
      inferInstance inferInstance (fun a => a) := e.measurableEmbedding
  rw [adelic_measure_box F Q, he.integrable_map_iff]
  exact hf.mul_prod (finite_head_integrable F Q hD g hg)

end DedekindZetaZeroFree.FourierContinuation.CurrentBoxProductHaar

end
