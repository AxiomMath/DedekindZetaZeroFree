module

public import DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

section Core
variable (T : Realization R Q) (M : ∀ q, LocalImageData R q)
variable (e : ∀ p, actualLocal R M p) (bad : Finset (KPHilbert.Place F))
variable (A : RestrictedTensorSimple.Core (actualLocal R M) e bad →ₗ[ℂ] Functions R)
variable (hA : ∀ x, A x ∈ translateSpan T)

def coreIntoSpan : RestrictedTensorSimple.Core (actualLocal R M) e bad →ₗ[ℂ] translateSpan T :=
  A.codRestrict (translateSpan T) hA

def corePeriod (g : Group R) :
    RestrictedTensorSimple.Core (actualLocal R M) e bad →ₗ[ℂ] ℂ :=
  (period T g).comp (coreIntoSpan T M e bad A hA)

@[simp] theorem corePeriod_apply (g : Group R)
    (x : RestrictedTensorSimple.Core (actualLocal R M) e bad) :
    corePeriod T M e bad A hA g x = MomentSources.fourier R Q.dq (A x) g := rfl

end Core

theorem exists_detected_pure {J : Type*} [Fintype J] {V : J → Type*}
    [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (L : PiTensorProduct ℂ V →ₗ[ℂ] ℂ) (z : PiTensorProduct ℂ V)
    (hz : L z ≠ 0) : ∃ x : ∀ j, V j, L (PiTensorProduct.tprod ℂ x) ≠ 0 := by
  by_contra hn
  have hzero : ∀ x : ∀ j, V j, L (PiTensorProduct.tprod ℂ x) = 0 := by
    simpa only [not_exists, not_not] using hn
  have hall : ∀ w : PiTensorProduct ℂ V, L w = 0 := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod c x => simp only [map_smul, hzero x, smul_zero]
    | add z w hz hw => simp only [map_add, hz, hw, add_zero]
  exact hz (hall z)

end DedekindZetaZeroFree.FourierContinuation

end
