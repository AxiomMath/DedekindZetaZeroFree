module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RootBoxCoordinates
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.FinitePlaceNormalization
public import DedekindZetaZeroFree.Eisenstein.Induction.ParameterBoxes.CompactLevel

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def fullIndex (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q) :
    InfinitePlace F ⊕ Q ≃ (fullLevel R P C Q hQ).val where
  toFun
    | .inl w => ⟨.inl w, by simp [fullLevel, LiteralSource.cofactorSourceLevel]⟩
    | .inr q => ⟨.inr q.val, by simpa [fullLevel, LiteralSource.cofactorSourceLevel] using q.property⟩
  invFun j := by
    rcases j with ⟨j,hj⟩
    cases j with
    | inl w => exact .inl w
    | inr q => exact .inr ⟨q, by simpa [fullLevel, LiteralSource.cofactorSourceLevel] using hj⟩
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with ⟨j,hj⟩; cases j <;> rfl

def fullProfile (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (f : ∀ j : (fullLevel R P C Q hQ).val, RootPoint R j.val → ℂ) :
    ∀ i, CurrentBoxCoordinateHaar.Root F Q i → ℂ
  | .inl w => f (fullIndex R P C Q hQ (.inl w))
  | .inr q => f (fullIndex R P C Q hQ (.inr q))

theorem fullProfile_product (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (f : ∀ j : (fullLevel R P C Q hQ).val, RootPoint R j.val → ℂ)
    (y : KPGlobalTorusFunctionData.Adeles F) :
    (∏ j, f j (rootCoordinate R y j.val)) =
      ∏ i, fullProfile R P C Q hQ f i
        (@CurrentBoxCoordinateHaar.coordinate F _ _
          (primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12) Q y i) := by
  rw [← (fullIndex R P C Q hQ).prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  cases i <;> rfl

theorem fullProfile_integral (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (f : ∀ j : (fullLevel R P C Q hQ).val, RootPoint R j.val → ℂ)
    (i : InfinitePlace F ⊕ Q) :
    (∫ x, fullProfile R P C Q hQ f i x ∂CurrentBoxCoordinateHaar.rootMeasure F Q i) =
      ∫ x, f (fullIndex R P C Q hQ i) x
        ∂arithmeticRootMeasure R N (fullIndex R P C Q hQ i).val := by
  cases i with
  | inl w => rfl
  | inr q =>
    change (∫ x, f (fullIndex R P C Q hQ (.inr q)) x ∂localNormalizedHaar F q.val) =
      ∫ x, f (fullIndex R P C Q hQ (.inr q)) x ∂N.finiteHaar q.val
    rw [CurrentFiniteHaarBinding.finiteHaar_eq N q.val]

theorem full_product_integral (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (hD : localDifferentSupport F ⊆ (Q : Set _))
    (f : ∀ j : (fullLevel R P C Q hQ).val, RootPoint R j.val → ℂ) :
    (∫ y : KPGlobalTorusFunctionData.Adeles F, ∏ j, f j (rootCoordinate R y j.val)
      ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
      ∏ j, ∫ x, f j x ∂arithmeticRootMeasure R N j.val := by
  letI := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  simp_rw [fullProfile_product R P C Q hQ f]
  rw [CurrentBoxCoordinateHaar.product_integral F Q hD]
  simp_rw [fullProfile_integral R N P C Q hQ f]
  exact (fullIndex R P C Q hQ).prod_comp (fun j => ∫ x, f j x ∂arithmeticRootMeasure R N j.val)

theorem full_product_integrable (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (hD : localDifferentSupport F ⊆ (Q : Set _))
    (f : ∀ j : (fullLevel R P C Q hQ).val, RootPoint R j.val → ℂ)
    (hf : ∀ j, Integrable (f j) (arithmeticRootMeasure R N j.val)) :
    Integrable (fun y : KPGlobalTorusFunctionData.Adeles F => ∏ j, f j (rootCoordinate R y j.val))
      ((KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) := by
  letI := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  simp_rw [fullProfile_product R P C Q hQ f]
  apply CurrentBoxCoordinateHaar.product_integrable F Q hD
  intro i
  cases i with
  | inl w => exact hf (fullIndex R P C Q hQ (.inl w))
  | inr q =>
    have h := hf (fullIndex R P C Q hQ (.inr q))
    change Integrable _ (N.finiteHaar q.val) at h
    rw [CurrentFiniteHaarBinding.finiteHaar_eq N q.val] at h
    exact h

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
