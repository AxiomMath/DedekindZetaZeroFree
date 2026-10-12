module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.WordGeometry
public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.ProductFaithfulness

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct KPLiteralScalarHCCompactOrbit
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {N : TraceHaarTransport R} {C : JointDigitDescentSources R N}

def archCoefficient (v : R.A.UnitQuotient) (w : InfinitePlace F) (g : ComplexGL2) : ℂ :=
  fourier R C.sources.dq (C.realization.theta v)
    (archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 (Function.update 1 w g)) /
      fourier R C.sources.dq (C.realization.theta v) 1

theorem archCoefficient_image (v : R.A.UnitQuotient) (w : InfinitePlace F) :
    archCoefficient (C := C) v w ∈ KPCplxJacquetFunctional.jacquetEvaluation.range := by
  obtain ⟨f,hf⟩ := selected_residue_jacquet_image R C.sources C.realization v w
  refine ⟨(fourier R C.sources.dq (C.realization.theta v) 1)⁻¹ • f, ?_⟩
  funext g
  simp only [map_smul,Pi.smul_apply,smul_eq_mul,archCoefficient,div_eq_mul_inv]
  change _ * KPCplxJacquetFunctional.jacquetEvaluation f g =
    fourier R C.sources.dq (C.realization.theta v)
      (archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 (Function.update (fun _ => 1) w g)) * _
  rw [hf]
  exact mul_comm _ _

theorem FrozenTensor.compact_mixed_product {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (k : InfinitePlace F → ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    fourier R C.sources.dq (C.realization.theta v)
      ((finiteBase (R := R) a).val * archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
        (fun w => complexSU2Embedding (k w))) =
      fourier R C.sources.dq (C.realization.theta v) 1 *
        (∏ q : R.A.Sf, fourier R C.sources.dq (C.realization.theta v) (finiteLift q.val (a q.val)) /
          fourier R C.sources.dq (C.realization.theta v) 1) *
        ∏ w : InfinitePlace F, archCoefficient (C := C) v w (complexSU2Embedding (k w)) := by
  have hp := X.mixed_word_exact k a
  rw [X.mixed_word_geometry k a] at hp
  rw [hp]
  have hratio : (∏ p : X.level.val, C.factorization.ell p (mixedAction (C := C) k a p.val (X.component p))) =
      (∏ p : X.level.val, C.factorization.ell p (X.component p)) *
      ∏ p : X.level.val, C.factorization.ell p (mixedAction (C := C) k a p.val (X.component p)) /
        C.factorization.ell p (X.component p) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    field_simp [X.local_forward_ne_zero p]
  rw [hratio,← X.forward_exact]
  have he := Equiv.prod_comp X.placeEquiv (fun p : X.level.val =>
    C.factorization.ell p (mixedAction (C := C) k a p.val (X.component p)) /
      C.factorization.ell p (X.component p))
  rw [← he,Fintype.prod_sum_type]
  have hc : (∏ w : InfinitePlace F,
      C.factorization.ell (Sum.inl w) (mixedAction (C := C) k a (Sum.inl w) (X.component (X.placeEquiv (Sum.inl w)))) /
        C.factorization.ell (Sum.inl w) (X.component (X.placeEquiv (Sum.inl w)))) =
      ∏ w : InfinitePlace F, archCoefficient (C := C) v w (complexSU2Embedding (k w)) := by
    apply Finset.prod_congr rfl
    intro w _
    unfold archCoefficient
    rw [KPLiteralScalarHCCompactAction.archMatrixInsertion_compact_single]
    simpa only [FrozenTensor.compactUpdate,Function.update_self,mixedAction,FrozenTensor.placeEquiv,
      Equiv.coe_fn_mk] using (X.compact_normalized_single w (k w)).symm
  have hfin : (∏ q : R.A.Sf,
      C.factorization.ell (Sum.inr q.val) (mixedAction (C := C) k a (Sum.inr q.val) (X.component (X.placeEquiv (Sum.inr q)))) /
        C.factorization.ell (Sum.inr q.val) (X.component (X.placeEquiv (Sum.inr q)))) =
      ∏ q : R.A.Sf, fourier R C.sources.dq (C.realization.theta v) (finiteLift q.val (a q.val)) /
        fourier R C.sources.dq (C.realization.theta v) 1 := by
    apply Finset.prod_congr rfl
    intro q _
    simpa only [FrozenTensor.finiteUpdate,Function.update_self,mixedAction,FrozenTensor.placeEquiv,
      Equiv.coe_fn_mk] using (X.finite_normalized_single q (a q.val)).symm
  simp only [FrozenTensor.placeEquiv,Equiv.coe_fn_mk] at hc hfin ⊢
  rw [hc,hfin]
  ring

theorem fullMatrix_product (v : R.A.UnitQuotient)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (g : InfinitePlace F → ComplexGL2) :
    fourier R C.sources.dq (C.realization.theta v)
      ((finiteBase (R := R) a).val * archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 g) =
      fourier R C.sources.dq (C.realization.theta v) 1 *
        (∏ q : R.A.Sf, fourier R C.sources.dq (C.realization.theta v) (finiteLift q.val (a q.val)) /
          fourier R C.sources.dq (C.realization.theta v) 1) *
        ∏ w : InfinitePlace F, archCoefficient (C := C) v w (g w) := by
  let P := fun g : InfinitePlace F → ComplexGL2 => fourier R C.sources.dq (C.realization.theta v)
    ((finiteBase (R := R) a).val * archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 g)
  let b := fourier R C.sources.dq (C.realization.theta v) 1 *
    ∏ q : R.A.Sf, fourier R C.sources.dq (C.realization.theta v) (finiteLift q.val (a q.val)) /
      fourier R C.sources.dq (C.realization.theta v) 1
  let Q := fun g : InfinitePlace F → ComplexGL2 => b * ∏ w, archCoefficient (C := C) v w (g w)
  have he : P = Q := by
    apply product_eq_of_compact_slices
    · intro w g₀
      obtain ⟨f,hf⟩ := finiteBase_residue_jacquet_image R C.sources C.realization v w
        (finiteBase (R := R) a) g₀
      exact ⟨f,funext (fun g => (hf g).symm)⟩
    · intro w g₀
      obtain ⟨f,hf⟩ := archCoefficient_image (C := C) v w
      let c := b * ∏ u ∈ Finset.univ.erase w, archCoefficient (C := C) v u (g₀ u)
      refine ⟨c • f, ?_⟩
      funext g
      simp only [map_smul,Pi.smul_apply,smul_eq_mul]
      rw [hf]
      dsimp only [Q]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      simp only [Function.update_self]
      have hr : (∏ u ∈ Finset.univ.erase w, archCoefficient (C := C) v u (Function.update g₀ w g u)) =
          ∏ u ∈ Finset.univ.erase w, archCoefficient (C := C) v u (g₀ u) := by
        apply Finset.prod_congr rfl
        intro u hu
        rw [Function.update_of_ne (Finset.mem_erase.mp hu).1]
      rw [hr]
      dsimp only [c]
      ring
    · intro k
      exact (frozenTensor R C v).compact_mixed_product k a
  exact congrFun he g

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
