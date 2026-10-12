module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLocalExceptionalConstruction KPLocalPrincipalSeries
open KPRankOneShellRepair KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def rationalSlotContraction (s : RestrictedTensorSimple.Level (bad A P C))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (v : ∀ j : s.val, Fiber A P C j.val) :
    LocalFiber F ζ hζ P C q →ₗ[ℂ] ℂ :=
  ((rationalEvaluation A).comp ((comparison A P C).comp
    (RestrictedTensorSimple.stageInclusion _ _ _ s))).comp
      ((PiTensorProduct.tprod ℂ).toLinearMap v ⟨Sum.inr q,hq⟩)

@[simp] theorem rationalSlotContraction_apply
    (s : RestrictedTensorSimple.Level (bad A P C)) (q : KPFinitePlace F)
    (hq : Sum.inr q ∈ s.val) (v : ∀ j : s.val, Fiber A P C j.val)
    (w : LocalFiber F ζ hζ P C q) :
    rationalSlotContraction A P C s q hq v w =
      (comparison A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
        (PiTensorProduct.tprod ℂ (Function.update v ⟨Sum.inr q,hq⟩ w)))).val.val 1 := rfl

def rationalScatteringSlice (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw A)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val) (y : q.adicCompletion F) : ℂ :=
  rationalSlotContraction A P C s q hq
    (fun j => localValue A P C j.val (g j.val) (x j))
    ((x ⟨Sum.inr q,hq⟩).val ((C.canonical q).borel.liftedW⁻¹ *
      (C.canonical q).borel.upperRoot (Multiplicative.ofAdd y) *
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q))))

def finiteScatteringRaw (q : KPFinitePlace F) (y : q.adicCompletion F) :
    KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) :=
  (KPRankOneOpenCellKernel.signedWeylRaw F ζ hζ q)⁻¹ *
    KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) y

theorem finiteScatteringRaw_quotient (q : KPFinitePlace F) (y : q.adicCompletion F) :
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (finiteScatteringRaw A q y) =
      (C.canonical q).borel.liftedW⁻¹ *
        (C.canonical q).borel.upperRoot (Multiplicative.ofAdd y) := by
  rw [finiteScatteringRaw, map_mul, map_inv,
    (C.canonical q).openCell (C.polarization q) |>.weyl_eq,
    (C.canonical q).openCell (C.polarization q) |>.upper_eq]
  rfl

theorem rawStageInsertion_scattering
    (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw A)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val) (y : q.adicCompletion F) :
    rawStageInsertion A P C s (PiTensorProduct.tprod ℂ x)
      (localToRestricted F ζ hζ (Sum.inr q) (finiteScatteringRaw A q y) * g) =
      rationalScatteringSlice A P C s x g q hq y := by
  rw [rawStageInsertion_pure]
  unfold rationalScatteringSlice
  rw [rationalSlotContraction_apply]
  have he : (fun j : s.val => localValue A P C j.val
      ((localToRestricted F ζ hζ (Sum.inr q) (finiteScatteringRaw A q y) * g) j.val) (x j)) =
      Function.update (fun j : s.val => localValue A P C j.val (g j.val) (x j))
        ⟨Sum.inr q,hq⟩ ((x ⟨Sum.inr q,hq⟩).val ((C.canonical q).borel.liftedW⁻¹ *
          (C.canonical q).borel.upperRoot (Multiplicative.ofAdd y) *
          KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q)))) := by
    funext j
    by_cases hj : j.val = Sum.inr q
    · have hji : j = ⟨Sum.inr q,hq⟩ := Subtype.ext hj
      subst j
      rw [Function.update_self]
      simp only [RestrictedProduct.mul_apply, localToRestricted,
        RestrictedProduct.mulSingleMonoidHom_apply,
        RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_same]
      change (x ⟨Sum.inr q,hq⟩).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (_ * _)) = _
      rw [map_mul, finiteScatteringRaw_quotient]
    · rw [Function.update_of_ne (fun h => hj (congrArg Subtype.val h))]
      simp only [RestrictedProduct.mul_apply, localToRestricted,
        RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
        Pi.mulSingle_eq_of_ne hj, one_mul]
  exact congrArg (fun v => (comparison A P C
    (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ v))).val.val 1) he

theorem finiteScatteringRaw_tail
    (s : RestrictedTensorSimple.Level (bad A P C)) (g : Raw A)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (hg : ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v)
    (y : q.adicCompletion F) :
    ∀ v, v ∉ s.val → localValue A P C v
      ((localToRestricted F ζ hζ (Sum.inr q) (finiteScatteringRaw A q y) * g) v)
      (plusReference A P C v) = reference A P C v := by
  intro v hv
  have hne : v ≠ Sum.inr q := fun h => hv (h ▸ hq)
  simpa only [RestrictedProduct.mul_apply, localToRestricted,
    RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply,
    Pi.mulSingle_eq_of_ne hne, one_mul] using hg v hv

theorem rawCoreInsertion_scattering_stage
    (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw A)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (hg : ∀ v, v ∉ s.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v)
    (y : q.adicCompletion F) :
    rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (PiTensorProduct.tprod ℂ x))
      (localToRestricted F ζ hζ (Sum.inr q) (finiteScatteringRaw A q y) * g) =
      rationalScatteringSlice A P C s x g q hq y := by
  exact (rawCoreInsertion_stage A P C s _ _
    (finiteScatteringRaw_tail A P C s g q hq hg y)).trans
      (rawStageInsertion_scattering A P C s x g q hq y)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
