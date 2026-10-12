module

public import DedekindZetaZeroFree.Theta.Profiles.RadialJetsAndLocalNorms

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

structure FrozenTensor (v : R.A.UnitQuotient) where
  level : RestrictedTensorSimple.Level C.factorization.bad
  component : ∀ p : level.val, actualLocal R C.factorization.finiteData p
  frozen : level.val = C.factorization.bad
  selected : C.factorization.selected v =
    RestrictedTensorSimple.stageInclusion _ C.factorization.references C.factorization.bad level
      (PiTensorProduct.tprod ℂ component)

def frozenTensor (v : R.A.UnitQuotient) : FrozenTensor R C v :=
  let s := (C.factorization.selected_frozen_stage v).choose
  let x := (C.factorization.selected_frozen_stage v).choose_spec.choose
  ⟨s, x, (C.factorization.selected_frozen_stage v).choose_spec.choose_spec.1,
    (C.factorization.selected_frozen_stage v).choose_spec.choose_spec.2⟩

variable {R C}

theorem FrozenTensor.function_eq {v : R.A.UnitQuotient} (X : FrozenTensor R C v) :
    C.factorization.coreMap
      (RestrictedTensorSimple.stageInclusion _ C.factorization.references C.factorization.bad
        X.level (PiTensorProduct.tprod ℂ X.component)) = C.realization.theta v := by
  rw [← X.selected]
  exact C.factorization.selected_eq v

theorem FrozenTensor.forward_exact {v : R.A.UnitQuotient} (X : FrozenTensor R C v) :
    fourier R C.sources.dq (C.realization.theta v) 1 =
      ∏ p : X.level.val, C.factorization.ell p (X.component p) := by
  rw [← X.function_eq]
  exact C.factorization.product_exact X.level X.component

theorem FrozenTensor.local_forward_ne_zero {v : R.A.UnitQuotient}
    (X : FrozenTensor R C v) (p : X.level.val) :
    C.factorization.ell p (X.component p) ≠ 0 := by
  have hn : (∏ p : X.level.val, C.factorization.ell p (X.component p)) ≠ 0 := by
    rw [← X.forward_exact]
    exact ThetaExpansion.first_root_forward_period_ne_zero R C v
  exact (Finset.prod_ne_zero_iff.mp hn) p (Finset.mem_univ p)

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
