module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField MeasureTheory
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def PeriodIntegrable (dq : Measure (KPAdditiveQuotient F)) (f : Functions R)
    (g : Group R) : Prop :=
  Integrable (fun q => f
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
      star (adelicTraceQuotientCharacter F q : ℂ)) dq

def rightTranslateSum {I : Type*} (s : Finset I) (c : I → ℂ) (a : I → Group R) :
    Functions R →ₗ[ℂ] Functions R :=
  ∑ i ∈ s, c i • KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 (a i)

lemma rightTranslateSum_apply {I : Type*} (s : Finset I) (c : I → ℂ)
    (a : I → Group R) (f : Functions R) (g : Group R) :
    rightTranslateSum R s c a f g = ∑ i ∈ s, c i * f (g * a i) := by
  simp [rightTranslateSum, KPLiteralRaw.rightAction]

lemma fourier_rightAction (dq : Measure (KPAdditiveQuotient F))
    (f : Functions R) (g a : Group R) :
    fourier R dq (KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a f) g =
      fourier R dq f (g * a) := by
  change (∫ q, f
    ((KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) * a) *
      star (adelicTraceQuotientCharacter F q : ℂ) ∂dq) = _
  simp only [MomentSources.fourier, mul_assoc]

theorem fourier_rightTranslateSum (dq : Measure (KPAdditiveQuotient F))
    {I : Type*} (s : Finset I) (c : I → ℂ) (a : I → Group R)
    (f : Functions R) (g : Group R)
    (h : ∀ i ∈ s, PeriodIntegrable R dq f (g * a i)) :
    fourier R dq (rightTranslateSum R s c a f) g =
      ∑ i ∈ s, c i * fourier R dq f (g * a i) := by
  unfold MomentSources.fourier
  simp_rw [rightTranslateSum_apply, Finset.sum_mul, mul_assoc]
  refine (integral_finset_sum s (fun i hi => (h i hi).const_mul (c i))).trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_const_mul _ _

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
