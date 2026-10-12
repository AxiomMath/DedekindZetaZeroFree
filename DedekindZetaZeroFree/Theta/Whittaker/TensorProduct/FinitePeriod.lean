module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.FrozenTensor

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {N : TraceHaarTransport R} {C : JointDigitDescentSources R N}

def finiteLift (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) : Group R :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)

theorem FrozenTensor.finite_mem {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (q : R.A.Sf) : Sum.inr q.val ∈ X.level.val := by
  rw [X.frozen, C.factorization.bad_exact]
  exact Or.inr ⟨q.val, rfl, q.property⟩

def FrozenTensor.finiteUpdate {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (q : R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)) :
    ∀ p : X.level.val, actualLocal R C.factorization.finiteData p :=
  Function.update X.component ⟨Sum.inr q.val, X.finite_mem q⟩
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      q.val (C.factorization.finiteData q.val).inducing
      (C.factorization.finiteData q.val).inducing.polarization
      (C.factorization.finiteData q.val).haar (C.factorization.finiteData q.val).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) a)
      (X.component ⟨Sum.inr q.val, X.finite_mem q⟩))

theorem FrozenTensor.finite_function {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (q : R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val))
    (g : Group R) :
    C.factorization.coreMap
      (RestrictedTensorSimple.stageInclusion _ C.factorization.references C.factorization.bad
        X.level (PiTensorProduct.tprod ℂ (X.finiteUpdate q a))) g =
      C.realization.theta v (g * finiteLift q.val a) := by
  rw [FrozenTensor.finiteUpdate, C.factorization.finite_intertwining]
  rw [X.function_eq]
  rfl

theorem FrozenTensor.finite_period_integrable {v : R.A.UnitQuotient}
    (X : FrozenTensor R C v) (q : R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)) :
    Integrable (fun t => C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out t) *
        finiteLift q.val a) * star (adelicTraceQuotientCharacter F t : ℂ)) C.sources.dq :=
  C.factorization.period_integrable v (finiteLift q.val a)

theorem FrozenTensor.finite_period_exact {v : R.A.UnitQuotient}
    (X : FrozenTensor R C v) (q : R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)) :
    fourier R C.sources.dq (C.realization.theta v) (finiteLift q.val a) =
      ∏ p : X.level.val, C.factorization.ell p (X.finiteUpdate q a p) := by
  have hi := X.finite_period_integrable q a
  rw [← C.factorization.product_exact X.level (X.finiteUpdate q a)]
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [mul_one, X.finite_function]

theorem FrozenTensor.finite_normalized_product {v : R.A.UnitQuotient}
    (X : FrozenTensor R C v) (q : R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)) :
    fourier R C.sources.dq (C.realization.theta v) (finiteLift q.val a) /
        fourier R C.sources.dq (C.realization.theta v) 1 =
      ∏ p : X.level.val,
        C.factorization.ell p (X.finiteUpdate q a p) /
          C.factorization.ell p (X.component p) := by
  rw [X.finite_period_exact, X.forward_exact, Finset.prod_div_distrib]

theorem FrozenTensor.finite_normalized_single {v : R.A.UnitQuotient}
    (X : FrozenTensor R C v) (q : R.A.Sf)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)) :
    fourier R C.sources.dq (C.realization.theta v) (finiteLift q.val a) /
        fourier R C.sources.dq (C.realization.theta v) 1 =
      C.factorization.ell (Sum.inr q.val)
        (X.finiteUpdate q a ⟨Sum.inr q.val, X.finite_mem q⟩) /
          C.factorization.ell (Sum.inr q.val)
            (X.component ⟨Sum.inr q.val, X.finite_mem q⟩) := by
  rw [X.finite_normalized_product]
  exact Finset.prod_eq_single (s := Finset.univ)
    (f := fun p : X.level.val => C.factorization.ell p (X.finiteUpdate q a p) /
      C.factorization.ell p (X.component p)) ⟨Sum.inr q.val, X.finite_mem q⟩ (by
      intro p _ hp
      rw [FrozenTensor.finiteUpdate, Function.update_of_ne hp]
      exact div_self (X.local_forward_ne_zero p)) (by simp)

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
