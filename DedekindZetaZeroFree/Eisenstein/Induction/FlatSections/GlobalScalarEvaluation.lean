module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.FiniteTensorEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages FaithfulSource.RepairedInducing ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000

theorem scalar_raw (x : PlusCore R N P C) (g : Raw R) :
    scalarSourceEvaluator R N P C x
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) =
      LiteralSource.rawCoreInsertion R.A P C (coreEquiv R N P C x) g := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, y, rfl⟩ := Module.DirectLimit.exists_of x
  obtain ⟨u, hu⟩ := exists_reference_stage R N P C g
  let t : RestrictedTensorSimple.Level (bad R P C) :=
    ⟨s.val ∪ u.val, s.property.trans Finset.subset_union_left⟩
  have hst : s ≤ t := Finset.subset_union_left
  have ht : ∀ p, p ∉ t.val → localValue R N P C p (g p)
      (plusReference R N P C p) = reference R P C p := by
    intro p hp
    exact hu p (fun h => hp (Finset.mem_union_right _ h))
  have he : RestrictedTensorSimple.stageInclusion (Plus R N P C)
      (plusReference R N P C) (bad R P C) t
      (RestrictedTensorSimple.transition _ _ _ s t hst y) =
      RestrictedTensorSimple.stageInclusion _ _ _ s y := Module.DirectLimit.of_f
  have h := scalar_stage_raw R N P C t
    (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C) (bad R P C) s t hst y) g ht
  rw [he] at h
  exact h

theorem scalar_eq (x : PlusCore R N P C) :
    scalarSourceEvaluator R N P C x =
      LiteralSource.quotientCoreEvaluator R.A P C (coreEquiv R N P C x) := by
  funext g
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g => exact scalar_raw R N P C x g

theorem sourceFlat_value_eq (x : PlusCore R N P C) (z : ℂ)
    (g : KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12) :
    (sourceFlat R N P C x).val z g =
      (LiteralSource.coreFlatInsertion R P C (coreEquiv R N P C x)).val z g := by
  change Complex.exp (z * (iwasawaLogHeight R g : ℂ)) * scalarSourceEvaluator R N P C x g =
    Complex.exp (z * (iwasawaLogHeight R g : ℂ)) *
      LiteralSource.quotientCoreEvaluator R.A P C (coreEquiv R N P C x) g
  rw [scalar_eq]

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
