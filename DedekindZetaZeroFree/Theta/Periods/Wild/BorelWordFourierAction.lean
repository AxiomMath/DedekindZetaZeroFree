module

public import DedekindZetaZeroFree.Theta.Periods.Wild.FiniteActionContinuity

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open WildCurrentGlobalMap KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance insideBorelDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

structure BorelAction (R : PrincipalMellin.ActualRecipe S η) (W : Finset (KPFinitePlace F)) where
  q : W
  raw : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)
  affine : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) raw ∈
    KPKirillovGenuineSectionCharts.P F R.A.zeta12 R.A.primitive_zeta12 q.val

def insideSingle {W : Finset (KPFinitePlace F)} (a : BorelAction R W) :
    ProductAffine F R.A.zeta12 R.A.primitive_zeta12 W :=
  Function.update 1 a.q ⟨KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12
    (Sum.inr a.q.val) a.raw, a.affine⟩

def insideAffine {W : Finset (KPFinitePlace F)} : List (BorelAction R W) →
    ProductAffine F R.A.zeta12 R.A.primitive_zeta12 W
  | [] => 1
  | a :: l => insideSingle a * insideAffine l

def insideGroup {W : Finset (KPFinitePlace F)} : List (BorelAction R W) → Group R
  | [] => 1
  | a :: l => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr a.q.val) a.raw) * insideGroup l

theorem ambient_insideSingle (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (a : BorelAction R W) :
    ambientAction F R.A.zeta12 R.A.primitive_zeta12 W (fiber D W) (action D W) (insideSingle a) =
    slotMap D W a.q
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr a.q.val) a.raw) := by
  apply congrArg PiTensorProduct.map
  funext q
  by_cases hq : q = a.q
  · subst q
    simp only [insideSingle, Function.update_self]
  · simp only [insideSingle, Function.update_of_ne hq, Pi.one_apply, Subgroup.coe_one, map_one]
    rfl

theorem inside_single_fourier (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) (a : BorelAction R W)
    (z : AmbientTensor F W (fiber D W)) (g : Group R) :
    fourier R D.sources.dq (globalMap D W s hW x
      (ambientAction F R.A.zeta12 R.A.primitive_zeta12 W (fiber D W) (action D W) (insideSingle a) z)) g =
    fourier R D.sources.dq (globalMap D W s hW x z)
      (g * scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr a.q.val) a.raw)) := by
  rw [ambient_insideSingle]
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with u
  rw [globalMap_finite]
  simp only [mul_assoc]

theorem inside_word_fourier (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) (l : List (BorelAction R W))
    (z : AmbientTensor F W (fiber D W)) (g : Group R) :
    fourier R D.sources.dq (globalMap D W s hW x
      (ambientAction F R.A.zeta12 R.A.primitive_zeta12 W (fiber D W) (action D W) (insideAffine l) z)) g =
    fourier R D.sources.dq (globalMap D W s hW x z) (g * insideGroup l) := by
  induction l generalizing g with
  | nil => simp [insideAffine, insideGroup]
  | cons a l ih =>
    simp only [insideAffine, insideGroup, map_mul, Module.End.mul_apply]
    rw [inside_single_fourier, ih, mul_assoc]

theorem joint_kernel_raw_borel_word (D : TensorDetected R N)
    (W : Finset (KPFinitePlace F)) (s : RestrictedTensorSimple.Level D.bad)
    (hW : places W ⊆ s.val) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : ∀ p, a p ≠ 1 → ∃ q : KPFinitePlace F, p = Sum.inr q ∧
      Sum.inr q ∉ places W ∧ WildCurrentTameExterior.tameSlot (Sum.inr q))
    (l : List (BorelAction R W))
    (f : ∀ v, ScalarSections F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) v)
    (e : JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W (character W)
      (fiber D.toTensorActions W) (action D.toTensorActions W))
    (he : WildCurrentJointForm.jointForm D.toTensorActions W s hW x e = 0) :
    fourier R D.sources.dq (globalMap D.toTensorActions W s hW x
      (tensorEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
        (depth (R := R) W) (depth_valid (R := R) W) (character W)
        (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W)
        (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e)))
      (rawGlobal (R := R) a * insideGroup l) = 0 := by
  rw [← inside_word_fourier D.toTensorActions W s hW x l]
  apply raw_tame_kernel D W s hW x hx a ha
  exact WildCurrentJointForm.kernel_finite_borel D.toTensorActions W s hW x (insideAffine l) f e he
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
