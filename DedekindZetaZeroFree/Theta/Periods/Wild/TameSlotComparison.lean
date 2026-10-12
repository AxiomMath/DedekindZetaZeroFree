module

public import DedekindZetaZeroFree.Theta.Periods.Wild.JointPeriodDescent
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.TameExteriorLines
public import DedekindZetaZeroFree.Theta.Whittaker.Uniqueness.NormalizedExteriorProducts

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildTameSlotTransport
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open KPWildActualExteriorFactorization
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem stageTuple_update_outside (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (p : s.val) (hp : p.val ∉ places W) (v : actualLocal R D.finiteData p)
    (y : ∀ q : W, fiber D W q) :
    stageTuple D W s (Function.update x p v) y =
      Function.update (stageTuple D W s x y) p v := by
  funext r
  by_cases hr : r = p
  · subst r
    simp only [stageTuple, hp, dite_false, Function.update_self]
  · rw [Function.update_of_ne hr]
    by_cases hm : r.val ∈ places W
    · simp only [stageTuple, hm, dite_true]
    · simp only [stageTuple, hm, dite_false, Function.update_of_ne hr]

def multiplier (D : TensorDetected R N) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) (p : s.val)
    (v : actualLocal R D.finiteData p) : ℂ :=
  (coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x)⁻¹ *
    coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s
      (Function.update x p v)

theorem slot_compare (D : TensorDetected R N) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (p : s.val) (hp : WildCurrentTameExterior.tameSlot p.val)
    (z : ∀ p : s.val, actualLocal R D.finiteData p) (v : actualLocal R D.finiteData p) :
    coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s (Function.update z p v) =
      coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s
        (Function.update z p (x p)) * multiplier D s x p v := by
  let L := coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s
  let ell : actualLocal R D.finiteData p →ₗ[ℂ] ℂ := (L x)⁻¹ • L.toLinearMap x p
  have hell : ell ∈ D.toTensorHC.sliceLine p.val :=
    (D.toTensorHC.sliceLine p.val).smul_mem _ (D.toTensorHC.slice_mem s x p)
  have hn : ell (x p) = 1 := by
    simp only [ell, LinearMap.smul_apply, smul_eq_mul, MultilinearMap.toLinearMap_apply,
      Function.update_eq_self]
    exact inv_mul_cancel₀ hx
  exact FiniteComparison.slot_eq_normalized (D.toTensorHC.sliceLine p.val)
    (WildCurrentTameExterior.tame_line_finrank D p.val hp) ell (L.toLinearMap z p)
    hell (D.toTensorHC.slice_mem s z p) (x p) hn v

theorem period_tame_update_pure (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (p : s.val) (hp : WildCurrentTameExterior.tameSlot p.val) (ho : p.val ∉ places W)
    (v : actualLocal R D.finiteData p) (y : ∀ q : W, fiber D.toTensorActions W q) :
    WildCurrentJointPeriod.period D.toTensorActions W s hW (Function.update x p v) (PiTensorProduct.tprod ℂ y) =
      WildCurrentJointPeriod.period D.toTensorActions W s hW x (PiTensorProduct.tprod ℂ y) * multiplier D s x p v := by
  have ha := period_pure D.toTensorActions W s hW (Function.update x p v) y
  have hb := period_pure D.toTensorActions W s hW x y
  have hu := stageTuple_update_outside D.toTensorActions W s x p ho v y
  have he : Function.update (stageTuple D.toTensorActions W s x y) p (x p) =
      stageTuple D.toTensorActions W s x y := by
    apply Function.update_eq_self_iff.mpr
    simp only [stageTuple, ho, dite_false]
  rw [ha, hu, slot_compare D s x hx p hp, he, hb]
end DedekindZetaZeroFree.FourierContinuation.WildTameSlotTransport

end
