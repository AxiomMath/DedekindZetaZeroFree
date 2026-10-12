module

public import DedekindZetaZeroFree.Eisenstein.Residues.UpperConstantTerm.Linearity
public import DedekindZetaZeroFree.Algebra.TensorProducts.SurjectiveMapKernels

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw KPRankOneShellRepair
open _root_.DedekindZetaZeroFree.KPLiteralResidueKernelTests renaming tensor_kernel_le_span → tensor_kernel_le_span
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
attribute [local irreducible] actualCanonicalForwardMap

abbrev FiniteQuotientFiber : KPHilbert.Place F → Type
  | Sum.inl w => Plus R.A P C (Sum.inl w)
  | Sum.inr q => (actualCanonicalForwardMap F ζ hζ q (C.canonical q)
      (C.polarization q) (μ q) (hμ q)).toLinearMap.range

instance finiteQuotientFiberAdd (v : KPHilbert.Place F) :
    AddCommGroup (FiniteQuotientFiber R P C μ hμ v) := by
  cases v with
  | inl w => exact plusAdd R.A P C (Sum.inl w)
  | inr q =>
    letI : AddCommGroup (KPLocalPrincipalSeries.sectionSpace
      (C.canonical q).borel (C.polarization q) .minus 0) := inferInstance
    exact Submodule.addCommGroup _
instance finiteQuotientFiberModule (v : KPHilbert.Place F) :
    Module ℂ (FiniteQuotientFiber R P C μ hμ v) := by
  cases v with
  | inl w => exact plusModule R.A P C (Sum.inl w)
  | inr q =>
    letI : AddCommGroup (KPLocalPrincipalSeries.sectionSpace
      (C.canonical q).borel (C.polarization q) .minus 0) := inferInstance
    exact Submodule.module _

def finiteQuotientMap (v : KPHilbert.Place F) :
    Plus R.A P C v →ₗ[ℂ] FiniteQuotientFiber R P C μ hμ v := by
  cases v with
  | inl w => exact LinearMap.id
  | inr q => exact (actualCanonicalForwardMap F ζ hζ q (C.canonical q)
      (C.polarization q) (μ q) (hμ q)).toLinearMap.rangeRestrict

theorem finiteQuotientMap_surjective (v : KPHilbert.Place F) :
    Function.Surjective (finiteQuotientMap R P C μ hμ v) := by
  cases v with
  | inl w => exact Function.surjective_id
  | inr q => rintro ⟨f,u,rfl⟩; exact ⟨u,rfl⟩

theorem upperStage_finiteQuotient_kernel (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level (bad R.A P C)) :
    (PiTensorProduct.map (fun j : t.val => finiteQuotientMap R P C μ hμ j.val)).ker ≤
      ((coreResidueUpperLinear R P C).comp
        (RestrictedTensorSimple.stageInclusion _ _ _ t)).ker := by
  let A := (coreResidueUpperLinear R P C).comp
    (RestrictedTensorSimple.stageInclusion _ _ _ t)
  have hs : Submodule.span ℂ {v | ∃ x : ∀ j : t.val, Plus R.A P C j.val,
      (∃ j : t.val, finiteQuotientMap R P C μ hμ j.val (x j) = 0) ∧
        PiTensorProduct.tprod ℂ x = v} ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, ⟨⟨v,hv⟩, hx⟩, rfl⟩
    change A (PiTensorProduct.tprod ℂ x) = 0
    cases v with
    | inl w =>
      have hx0 : x ⟨Sum.inl w,hv⟩ = 0 := hx
      rw [(PiTensorProduct.tprod ℂ).map_coord_zero _ hx0, map_zero]
    | inr q =>
      have hf : actualCanonicalForwardMap F ζ hζ q (C.canonical q) (C.polarization q)
          (μ q) (hμ q) (x ⟨Sum.inr q,hv⟩) = 0 := by
        exact congrArg Subtype.val hx
      funext g
      change (coreResidueUpperLinear R P C)
        (RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ x)) g = 0
      have he : slotCore R P C t x q hv (x ⟨Sum.inr q,hv⟩) =
          RestrictedTensorSimple.stageInclusion _ _ _ t (PiTensorProduct.tprod ℂ x) := by
        rw [slotCore_apply, Function.update_eq_self]
      rw [← he]
      exact coreResidue_upper_finite_kernel R P C N t x q hv (μ q) (hμ q) _ hf g
  exact (tensor_kernel_le_span
    (fun j : t.val => finiteQuotientMap R P C μ hμ j.val)
    (fun j => finiteQuotientMap_surjective R P C μ hμ j.val)).trans hs

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
