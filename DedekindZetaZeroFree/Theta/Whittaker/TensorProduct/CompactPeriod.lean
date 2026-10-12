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

lemma FrozenTensor.arch_mem {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (w : InfinitePlace F) : Sum.inl w ∈ X.level.val := by
  rw [X.frozen, C.factorization.bad_exact]
  exact Or.inl ⟨w, rfl⟩

def FrozenTensor.compactUpdate {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2) :
    ∀ p : X.level.val, actualLocal R C.factorization.finiteData p :=
  Function.update X.component ⟨Sum.inl w, X.arch_mem w⟩
    (KPGlobalResidualConstruction.complexCoreSU2Action k
      (X.component ⟨Sum.inl w, X.arch_mem w⟩))

lemma FrozenTensor.compact_function {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2) (g : Group R) :
    C.factorization.coreMap
      (RestrictedTensorSimple.stageInclusion _ C.factorization.references C.factorization.bad
        X.level (PiTensorProduct.tprod ℂ (X.compactUpdate w k))) g =
      C.realization.theta v
        (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) := by
  rw [FrozenTensor.compactUpdate, C.factorization.complex_intertwining, X.function_eq]

lemma FrozenTensor.compact_period_integrable {v : R.A.UnitQuotient}
    (X : FrozenTensor R C v) (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2) :
    Integrable (fun t => C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out t) *
        KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) *
        star (adelicTraceQuotientCharacter F t : ℂ)) C.sources.dq :=
  C.factorization.period_integrable v _

lemma FrozenTensor.compact_period_exact {v : R.A.UnitQuotient}
    (X : FrozenTensor R C v) (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2) :
    MomentSources.fourier R C.sources.dq (C.realization.theta v)
      (KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) =
      ∏ p : X.level.val, C.factorization.ell p (X.compactUpdate w k p) := by
  have hi := X.compact_period_integrable w k
  rw [← C.factorization.product_exact X.level (X.compactUpdate w k)]
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [mul_one, X.compact_function]

theorem FrozenTensor.compact_normalized_single {v : R.A.UnitQuotient}
    (X : FrozenTensor R C v) (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2) :
    MomentSources.fourier R C.sources.dq (C.realization.theta v)
        (KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) /
      MomentSources.fourier R C.sources.dq (C.realization.theta v) 1 =
      C.factorization.ell (Sum.inl w) (X.compactUpdate w k ⟨Sum.inl w, X.arch_mem w⟩) /
        C.factorization.ell (Sum.inl w) (X.component ⟨Sum.inl w, X.arch_mem w⟩) := by
  rw [X.compact_period_exact, X.forward_exact, ← Finset.prod_div_distrib]
  exact Finset.prod_eq_single (s := Finset.univ)
    (f := fun p : X.level.val => C.factorization.ell p (X.compactUpdate w k p) /
      C.factorization.ell p (X.component p)) ⟨Sum.inl w, X.arch_mem w⟩ (by
      intro p _ hp
      rw [FrozenTensor.compactUpdate, Function.update_of_ne hp]
      exact div_self (X.local_forward_ne_zero p)) (by simp)

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
