module

public import DedekindZetaZeroFree.Theta.Periods.FinitePlaces.FaithfulTensorInsertion
public import DedekindZetaZeroFree.Theta.Profiles.ResidueSphericality
public import DedekindZetaZeroFree.Algebra.TensorProducts.PureTensorSlotCancellation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance currentDetectedSphericalPlaceDecidable : DecidableEq (KPHilbert.Place F) := Classical.decEq _

namespace TensorDetected

theorem finite_not_bad (D : TensorDetected R N) (q : KPFinitePlace F)
    (hq : q ∉ R.A.Sf) : Sum.inr q ∉ D.bad := by
  intro h
  rcases (D.bad_exact _).mp h with ⟨w, hw⟩ | ⟨p, hp, hps⟩
  · cases hw
  · cases hp
    exact hq hps

theorem reference_compact_fixed (D : TensorDetected R N) (q : KPFinitePlace F)
    (hq : q ∉ R.A.Sf)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (hk : k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
      (D.finiteData q).haar (D.finiteData q).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) k)
      (D.references (Sum.inr q)) = D.references (Sum.inr q) := by
  obtain ⟨v, hv⟩ := D.detected
  obtain ⟨s, x, hs, hx⟩ := D.selected_frozen_stage v
  have hqs : Sum.inr q ∉ s.val := by
    rw [hs]
    exact D.finite_not_bad q hq
  let t : RestrictedTensorSimple.Level D.bad :=
    ⟨insert (Sum.inr q) s.val, s.property.trans (Finset.subset_insert _ _)⟩
  let y : ∀ j : t.val, actualLocal R D.finiteData j :=
    fun j => if h : j.val ∈ s.val then x ⟨j.val, h⟩ else D.references j
  let i : t.val := ⟨Sum.inr q, Finset.mem_insert_self _ _⟩
  have hy : y i = D.references (Sum.inr q) := by simp [y, i, hqs]
  have htrans : RestrictedTensorSimple.stageInclusion _ D.references D.bad t (PiTensorProduct.tprod ℂ y) =
      D.selected v := by
    rw [hx, ← RestrictedTensorSimple.insert_pure (actualLocal R D.finiteData)
      D.references s.val t.val (Finset.subset_insert _ _) x]
    exact Module.DirectLimit.of_f
  let a := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
    (D.finiteData q).haar (D.finiteData q).haar_integer
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) k)
  have hcore : RestrictedTensorSimple.stageInclusion _ D.references D.bad t
      (PiTensorProduct.tprod ℂ (Function.update y i (a (y i)))) =
        RestrictedTensorSimple.stageInclusion _ D.references D.bad t (PiTensorProduct.tprod ℂ y) := by
    apply D.core_injective
    funext g
    rw [D.finite_intertwining q k t i.property y g, htrans, D.selected_eq]
    exact theta_exterior_spherical D.realization v q hq k hk g
  have htensor : PiTensorProduct.tprod ℂ (Function.update y i (a (y i))) =
      PiTensorProduct.tprod ℂ y :=
    RestrictedTensorSimple.stageInclusion_injective (actualLocal R D.finiteData)
      D.references D.bad D.reference_ne_zero t hcore
  have hnonzero : PiTensorProduct.tprod ℂ y ≠ 0 := by
    intro hz
    apply hv
    have he : D.coreMap (D.selected v) = 0 := by
      rw [← htrans, hz, map_zero, map_zero]
    rw [← D.selected_eq, he]
    simp [MomentSources.fourier]
  have he := pure_tensor_update_cancel y hnonzero i (a (y i)) htensor
  simpa only [hy] using he

def spherical (D : TensorDetected R N) : TensorSpherical R N where
  toTensorDetected := D
  spherical_reference q hq :=
    ⟨D.reference_ne_zero _ (D.finite_not_bad q hq), D.reference_compact_fixed q hq⟩

@[simp] theorem spherical_toTensorDetected (D : TensorDetected R N) :
    D.spherical.toTensorDetected = D := rfl

end TensorDetected
end DedekindZetaZeroFree.FourierContinuation

end
