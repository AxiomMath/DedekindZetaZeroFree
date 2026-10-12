module

public import DedekindZetaZeroFree.Moments.Reflected.SmoothEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPGlobalResidualConstruction KPLiteralChamber
open KPLiteralScalarArchUniformBands KPAdelicCoverRestrictedProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
variable (s : RestrictedTensorSimple.Level (bad R P C))
variable (hs : ∀ w : InfinitePlace F, Sum.inl w ∈ s.val)
variable (r : Raw R) (hr : ∀ w : InfinitePlace F, r (.inl w) = 1)

include hs hr
theorem reflected_section_pure
    (x : ∀ j : s.val, actualLocal R (imageData R N P C) j.val)
    (a : InfinitePlace F → ComplexGL2) :
    (reflectedStage R N P C s (r * sectionTuple F ζ hζ a) (PiTensorProduct.tprod ℂ x)).val.val 1 =
      (∏ w : InfinitePlace F, (x ⟨.inl w,hs w⟩).val.val (a w)) *
        CurrentMinusSlot.finiteScalar R N P C s x r := by
  rw [CurrentMinusSlot.reflected_pure]
  have hf : CurrentMinusSlot.finiteValues R N P C s x (r * sectionTuple F ζ hζ a) =
      CurrentMinusSlot.finiteValues R N P C s x r := by
    funext j
    rcases j with ⟨j,hj⟩
    cases j with
    | inl w => rfl
    | inr q =>
      change (x ⟨.inr q,hj⟩).val.val (KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (r (.inr q) * 1)) = _
      rw [mul_one]
      rfl
  simp only [CurrentMinusSlot.finiteScalar,hf]
  congr 1
  let e : InfinitePlace F ↪ s.val := ⟨fun w => ⟨.inl w,hs w⟩,by intro u v h; exact Sum.inl_injective (congrArg Subtype.val h)⟩
  let q := CurrentMinusSlot.archFactor R N P C s x (r * sectionTuple F ζ hζ a)
  have hi (w : InfinitePlace F) : q (e w) = (x ⟨.inl w,hs w⟩).val.val (a w) := by
    change (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ ((r * sectionTuple F ζ hζ a) (.inl w)).epsilon : ℂ) * (x ⟨.inl w,hs w⟩).val.val (complexMatrix R w ((r * sectionTuple F ζ hζ a) (.inl w))) = _
    have he : (r * sectionTuple F ζ hζ a) (.inl w) = (sectionTuple F ζ hζ a) (.inl w) := by
      change r (.inl w) * _ = _
      rw [hr w,one_mul]
    rw [he]
    have hm : complexMatrix R w ((sectionTuple F ζ hζ a) (.inl w)) = a w := by
      exact EisensteinReferenceSections.SourceSmooth.complexMatrix_section F ζ hζ w (a w)
    rw [hm]
    simp [sectionTuple,KPLocalCover.sectionMap]
  calc
    _ = ∏ j ∈ Finset.univ.map e, q j := by
      apply Eq.symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro j hj hjn
      rcases j with ⟨j,hj⟩
      cases j with
      | inr v => rfl
      | inl w => exact False.elim (hjn (Finset.mem_map.mpr ⟨w,Finset.mem_univ _,rfl⟩))
    _ = _ := by rw [Finset.prod_map]; simp only [hi]

end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
