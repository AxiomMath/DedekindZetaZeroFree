module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensors.ReferenceNonvanishing

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.DetectedDictionary
open MomentSources TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (M : ∀ q, LocalImageData R q)

abbrev ReferencePoint : KPHilbert.Place F → Type
  | Sum.inl _ => KPCplxCharacterHaar.ComplexGL2
  | Sum.inr q => KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q ×
      KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q

def referenceEvaluation (p : KPHilbert.Place F) :
    ReferencePoint R p → actualLocal R M p →ₗ[ℂ] ℂ := by
  cases p with
  | inl w =>
      exact fun g => {
        toFun := fun y => y.val.val g
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  | inr q =>
      exact fun a => {
        toFun := fun y => (y.val.val a.1).val a.2
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }

theorem referenceEvaluation_separates (p : KPHilbert.Place F)
    (y : actualLocal R M p) (hy : ∀ a, referenceEvaluation R M p a y = 0) : y = 0 := by
  cases p with
  | inl w =>
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact hy g
  | inr q =>
      apply Subtype.ext
      apply Subtype.ext
      funext g
      apply Subtype.ext
      funext t
      exact hy (g, t)

theorem exists_reference_coordinate (p : KPHilbert.Place F) :
    ∃ a : ReferencePoint R p, referenceEvaluation R M p a (reference R M p) ≠ 0 := by
  by_contra h
  push_neg at h
  exact reference_ne_zero R M p (referenceEvaluation_separates R M p _ h)

def referenceCoordinate (p : KPHilbert.Place F) : ReferencePoint R p :=
  (exists_reference_coordinate R M p).choose

def referenceForm (p : KPHilbert.Place F) : actualLocal R M p →ₗ[ℂ] ℂ :=
  (referenceEvaluation R M p (referenceCoordinate R M p) (reference R M p))⁻¹ •
    referenceEvaluation R M p (referenceCoordinate R M p)

@[simp] theorem referenceForm_reference (p : KPHilbert.Place F) :
    referenceForm R M p (reference R M p) = 1 := by
  simp only [referenceForm, LinearMap.smul_apply, smul_eq_mul]
  exact inv_mul_cancel₀ (exists_reference_coordinate R M p).choose_spec

def sourceReferenceForm (p : KPHilbert.Place F) : plusLocal R M p →ₗ[ℂ] ℂ :=
  (referenceForm R M p).comp (sourceQuotient R M p)

@[simp] theorem sourceReferenceForm_reference (p : KPHilbert.Place F) :
    sourceReferenceForm R M p (referenceSource R M p) = 1 :=
  referenceForm_reference R M p

theorem sourceReferenceForm_kernel (p : KPHilbert.Place F)
    (x : plusLocal R M p) (hx : sourceQuotient R M p x = 0) :
    sourceReferenceForm R M p x = 0 := by
  change referenceForm R M p (sourceQuotient R M p x) = 0
  rw [hx, map_zero]

end DedekindZetaZeroFree.FourierContinuation.DetectedDictionary

end
