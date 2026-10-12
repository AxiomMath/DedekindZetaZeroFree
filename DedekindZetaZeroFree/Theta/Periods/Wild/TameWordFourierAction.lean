module

public import DedekindZetaZeroFree.Theta.Periods.Wild.FiniteExteriorComparison
public import DedekindZetaZeroFree.Theta.Periods.Wild.ExteriorFourierAction

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open WildCurrentGlobalMap
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

structure TameAction (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) where
  q : KPFinitePlace F
  mem : Sum.inr q ∈ s.val
  outside : Sum.inr q ∉ places W
  tame : WildCurrentTameExterior.tameSlot (Sum.inr q)
  raw : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)

def wordTuple (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    List (TameAction D W s) → (∀ p : s.val, actualLocal R D.finiteData p)
  | [] => x
  | a :: l => outsideTuple D s (wordTuple D W s x l) a.q a.mem a.raw

def wordGroup (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) :
    List (TameAction D W s) → KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12
  | [] => 1
  | a :: l =>
    KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inr a.q) a.raw) * wordGroup D W s l

theorem word_fourier (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (l : List (TameAction D W s)) (z : AmbientTensor F W (fiber D W))
    (g : KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12) :
    fourier R D.sources.dq (globalMap D W s hW (wordTuple D W s x l) z) g =
    fourier R D.sources.dq (globalMap D W s hW x z) (g * wordGroup D W s l) := by
  induction l generalizing g with
  | nil => simp [wordTuple, wordGroup]
  | cons a l ih =>
    simp only [wordTuple, wordGroup]
    rw [outside_fourier D W s hW (wordTuple D W s x l) a.q a.mem a.outside a.raw z g,
      ih, mul_assoc]

theorem wordTuple_outside (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (l : List (TameAction D W s)) (p : s.val)
    (hp : ¬ (WildCurrentTameExterior.tameSlot p.val ∧ p.val ∉ places W)) :
    wordTuple D W s x l p = x p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hn : p ≠ ⟨Sum.inr a.q, a.mem⟩ := by
      intro he
      subst p
      exact hp ⟨a.tame, a.outside⟩
    simpa only [wordTuple, outsideTuple, Function.update_of_ne hn] using ih

theorem word_period_kernel (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (l : List (TameAction D.toTensorActions W s))
    (z : AmbientTensor F W (fiber D.toTensorActions W))
    (hz : WildCurrentJointPeriod.period D.toTensorActions W s hW x z = 0) :
    WildCurrentJointPeriod.period D.toTensorActions W s hW
      (wordTuple D.toTensorActions W s x l) z = 0 := by
  let t : Finset s.val := Finset.univ.filter
    (fun p ↦ WildCurrentTameExterior.tameSlot p.val ∧ p.val ∉ places W)
  have he : t.piecewise (wordTuple D.toTensorActions W s x l) x =
      wordTuple D.toTensorActions W s x l := by
    funext p
    by_cases hp : p ∈ t
    · simp [hp]
    · have hn : ¬ (WildCurrentTameExterior.tameSlot p.val ∧ p.val ∉ places W) := by
        simpa [t] using hp
      simp [hp, wordTuple_outside D.toTensorActions W s x l p hn]
  rw [← he]
  exact finite_tame_kernel D W s hW x hx t
    (fun p hp ↦ (Finset.mem_filter.mp hp).2.1)
    (fun p hp ↦ (Finset.mem_filter.mp hp).2.2) _ z hz

theorem finite_word_right_kernel (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (l : List (TameAction D.toTensorActions W s))
    (z : AmbientTensor F W (fiber D.toTensorActions W))
    (hz : WildCurrentJointPeriod.period D.toTensorActions W s hW x z = 0) :
    fourier R D.sources.dq (globalMap D.toTensorActions W s hW x z)
      (wordGroup D.toTensorActions W s l) = 0 := by
  have he := word_fourier D.toTensorActions W s hW x l z 1
  rw [one_mul] at he
  exact he.symm.trans (word_period_kernel D W s hW x hx l z hz)
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
