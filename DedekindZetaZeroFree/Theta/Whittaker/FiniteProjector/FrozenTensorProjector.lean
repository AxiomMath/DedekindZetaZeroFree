module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.GlobalFiniteProjector

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

def rootSlotSum (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (q : R.A.Sf) (hq : Sum.inr q.val ∈ s.val)
    {I : Type} [Fintype I] (c : I → ℂ) (t : I → q.val.adicCompletion F) :
    ∀ p : s.val, actualLocal R D.finiteData p :=
  Function.update x ⟨Sum.inr q.val, hq⟩
    (translateSum (actualFiniteAction R D q.val) (actualFiniteRoot R q.val)
      Finset.univ c t (x ⟨Sum.inr q.val, hq⟩))

theorem tensor_rootSlotSum (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (q : R.A.Sf) (hq : Sum.inr q.val ∈ s.val)
    {I : Type} [Fintype I] (c : I → ℂ) (t : I → q.val.adicCompletion F) :
    tensorFunction R D s (rootSlotSum R D s x q hq c t) =
      rightTranslateSum R Finset.univ c (fun i => finiteRoot R q.val (t i))
        (tensorFunction R D s x) := by
  let m := (D.coreMap.comp (RestrictedTensorSimple.stageInclusion _ D.references D.bad s)).compMultilinearMap
    (PiTensorProduct.tprod ℂ)
  let j : s.val := ⟨Sum.inr q.val, hq⟩
  change m (Function.update x j _) = _
  rw [← MultilinearMap.toLinearMap_apply, translateSum_apply, map_sum]
  simp only [map_smul]
  funext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rightTranslateSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change tensorFunction R D s (Function.update x j
    (actualFiniteAction R D q.val
      (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) (t i)) (x j))) g = _
  have hi := D.finite_intertwining q.val
    (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) (t i)) s hq x g
  rw [ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R] at hi
  exact hi

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
