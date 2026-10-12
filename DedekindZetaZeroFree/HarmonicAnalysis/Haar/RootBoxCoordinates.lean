module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ArchimedeanProductIntegration
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicBoxProductIntegration

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentBoxCoordinateHaar
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
variable (Q : Finset (KPFinitePlace F))
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def Root : InfinitePlace F ⊕ Q → Type
  | .inl _ => ℂ
  | .inr q => q.val.adicCompletion F
instance rootMeasurable : ∀ i, MeasurableSpace (Root F Q i)
  | .inl _ => inferInstanceAs (MeasurableSpace ℂ)
  | .inr q => inferInstanceAs (MeasurableSpace (q.val.adicCompletion F))
def rootMeasure : ∀ i, Measure (Root F Q i)
  | .inl _ => (2 : ENNReal) • KPCplxCharacterHaar.euclideanArea
  | .inr q => localNormalizedHaar F q.val
def coordinate (y : KPGlobalTorusFunctionData.Adeles F) : ∀ i, Root F Q i
  | .inl w => CurrentArchProductHaar.coordinate F w y.1
  | .inr q => y.2 q.val

theorem product_integral (hD : localDifferentSupport F ⊆ (Q : Set _))
    (f : ∀ i, Root F Q i → ℂ) :
    (∫ y : KPGlobalTorusFunctionData.Adeles F, ∏ i, f i (coordinate F Q y i)
      ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
      ∏ i, ∫ x, f i x ∂rootMeasure F Q i := by
  simp only [Fintype.prod_sum_type]
  change (∫ y : KPGlobalTorusFunctionData.Adeles F,
    (∏ w, f (.inl w) (CurrentArchProductHaar.coordinate F w y.1)) *
    (∏ q : Q, f (.inr q) (y.2 q.val)) ∂_) = _
  have h := CurrentBoxProductHaar.box_product_integral F Q hD
    (fun x => ∏ w, f (.inl w) (CurrentArchProductHaar.coordinate F w x))
    (fun x => ∏ q : Q, f (.inr q) (x q))
  refine h.trans ?_
  rw [CurrentArchProductHaar.arch_product_integral]
  have hp := integral_fintype_prod_eq_prod (fun q : Q => f (.inr q))
    (μ := fun q : Q => localNormalizedHaar F q.val)
  exact congrArg (fun x => (∏ w, ∫ z, f (.inl w) z
    ∂((2 : ENNReal) • KPCplxCharacterHaar.euclideanArea)) * x) hp

theorem product_integrable (hD : localDifferentSupport F ⊆ (Q : Set _))
    (f : ∀ i, Root F Q i → ℂ)
    (hf : ∀ i, Integrable (f i) (rootMeasure F Q i)) :
    Integrable (fun y : KPGlobalTorusFunctionData.Adeles F => ∏ i, f i (coordinate F Q y i))
      ((KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) := by
  simp only [Fintype.prod_sum_type]
  change Integrable (fun y : KPGlobalTorusFunctionData.Adeles F =>
    (∏ w, f (.inl w) (CurrentArchProductHaar.coordinate F w y.1)) *
    (∏ q : Q, f (.inr q) (y.2 q.val))) _
  exact CurrentBoxProductHaar.box_product_integrable F Q hD
    (fun x => ∏ w, f (.inl w) (CurrentArchProductHaar.coordinate F w x))
    (fun x => ∏ q : Q, f (.inr q) (x q))
    (CurrentArchProductHaar.arch_product_integrable F _ (fun w => hf (.inl w)))
    (Integrable.fintype_prod_dep (fun q => hf (.inr q)))

end DedekindZetaZeroFree.FourierContinuation.CurrentBoxCoordinateHaar

end
