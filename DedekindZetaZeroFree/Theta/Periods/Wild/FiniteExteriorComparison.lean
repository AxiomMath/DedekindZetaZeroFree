module

public import DedekindZetaZeroFree.Theta.Periods.Wild.JointFormBorelKernel
public import DedekindZetaZeroFree.Theta.Periods.Wild.TameSlotComparison

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open WildTameSlotTransport
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem period_slot_compare (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (u : ∀ p : s.val, actualLocal R D.finiteData p)
    (p : s.val) (hp : WildCurrentTameExterior.tameSlot p.val) (ho : p.val ∉ places W)
    (v : actualLocal R D.finiteData p) (z : AmbientTensor F W (fiber D.toTensorActions W)) :
    WildCurrentJointPeriod.period D.toTensorActions W s hW (Function.update u p v) z =
      WildCurrentJointPeriod.period D.toTensorActions W s hW (Function.update u p (x p)) z * multiplier D s x p v := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul, smul_eq_mul]
    rw [period_pure, period_pure,
      stageTuple_update_outside D.toTensorActions W s u p ho v y,
      stageTuple_update_outside D.toTensorActions W s u p ho (x p) y,
      slot_compare D s x hx p hp]
    ring
  | add z w hz hw =>
    simp only [map_add, hz, hw]
    ring

theorem period_finite_tame (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (t : Finset s.val) (ht : ∀ p ∈ t, WildCurrentTameExterior.tameSlot p.val)
    (ho : ∀ p ∈ t, p.val ∉ places W)
    (v : ∀ p : s.val, actualLocal R D.finiteData p)
    (z : AmbientTensor F W (fiber D.toTensorActions W)) :
    WildCurrentJointPeriod.period D.toTensorActions W s hW (t.piecewise v x) z =
      WildCurrentJointPeriod.period D.toTensorActions W s hW x z * ∏ p ∈ t, multiplier D s x p (v p) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert p t hpt ih =>
    have hp := ht p (Finset.mem_insert_self p t)
    have hop := ho p (Finset.mem_insert_self p t)
    have he : (insert p t).piecewise v x = Function.update (t.piecewise v x) p (v p) := by
      funext q
      by_cases hq : q = p
      · subst q; simp
      · simp [Finset.piecewise, hq]
    have hr : Function.update (t.piecewise v x) p (x p) = t.piecewise v x := by
      apply Function.update_eq_self_iff.mpr
      simp [hpt]
    rw [he, period_slot_compare D W s hW x hx _ p hp hop, hr,
      ih (fun q hq => ht q (Finset.mem_insert_of_mem hq))
        (fun q hq => ho q (Finset.mem_insert_of_mem hq)), Finset.prod_insert hpt]
    ring

theorem finite_tame_kernel (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (t : Finset s.val) (ht : ∀ p ∈ t, WildCurrentTameExterior.tameSlot p.val)
    (ho : ∀ p ∈ t, p.val ∉ places W)
    (v : ∀ p : s.val, actualLocal R D.finiteData p)
    (z : AmbientTensor F W (fiber D.toTensorActions W))
    (hz : WildCurrentJointPeriod.period D.toTensorActions W s hW x z = 0) :
    WildCurrentJointPeriod.period D.toTensorActions W s hW (t.piecewise v x) z = 0 := by
  rw [period_finite_tame D W s hW x hx t ht ho v z, hz, zero_mul]

def extendTuple (D : TensorActions R N) (s t : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    ∀ p : t.val, actualLocal R D.finiteData p :=
  fun p ↦ if hp : p.val ∈ s.val then x ⟨p.val, hp⟩ else D.references p

theorem stage_extend (D : TensorActions R N) (s t : RestrictedTensorSimple.Level D.bad)
    (hst : s.val ⊆ t.val) (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) t
      (extendTuple D s t x) =
    coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x := by
  change D.toTensorHC.literalPeriod 1
    (RestrictedTensorSimple.stageInclusion _ D.references D.bad t
      (PiTensorProduct.tprod ℂ (extendTuple D s t x))) =
    D.toTensorHC.literalPeriod 1
    (RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x))
  apply congrArg (D.toTensorHC.literalPeriod 1)
  change RestrictedTensorSimple.stageInclusion _ D.references D.bad t
    (PiTensorProduct.tprod ℂ (fun p ↦ if hp : p.val ∈ s.val then x ⟨p.val, hp⟩ else D.references p)) = _
  rw [← RestrictedTensorSimple.insert_pure (actualLocal R D.finiteData)
    D.references s.val t.val hst x]
  exact Module.DirectLimit.of_f

theorem period_extend (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s t : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (hst : s.val ⊆ t.val) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (z : AmbientTensor F W (fiber D W)) :
    WildCurrentJointPeriod.period D W t (hW.trans hst) (extendTuple D s t x) z =
    WildCurrentJointPeriod.period D W s hW x z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul, smul_eq_mul]
    apply congrArg (fun a : ℂ ↦ c * a)
    rw [period_pure, period_pure]
    have he : stageTuple D W t (extendTuple D s t x) y =
        extendTuple D s t (stageTuple D W s x y) := by
      funext p
      by_cases hp : p.val ∈ places W
      · simp [stageTuple, extendTuple, hp, hW hp]
      · simp [stageTuple, extendTuple, hp]
    rw [he, stage_extend D s t hst]
  | add z w hz hw => simp only [map_add, hz, hw]

end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
