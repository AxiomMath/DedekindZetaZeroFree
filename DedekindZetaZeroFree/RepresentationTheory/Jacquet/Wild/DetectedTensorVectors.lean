module

public import DedekindZetaZeroFree.Theta.Periods.Wild.JointFormBorelKernel

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentJointPeriod
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
variable (D : TensorActions R N) (T : Finset (KPFinitePlace F))
variable (s : RestrictedTensorSimple.Level D.bad) (hT : places T ⊆ s.val)
variable (x : ∀p : s.val,actualLocal R D.finiteData p)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def detectedFiniteTuple (q : T) : fiber D T q := x ⟨Sum.inr q.val,hT (placeEquiv T q).property⟩

theorem stageTuple_detected : stageTuple D T s x (detectedFiniteTuple D T s hT x) = x := by
  funext p
  rcases p with ⟨p,hp⟩
  cases p with
  | inl w => simp [stageTuple,places]
  | inr q =>
    by_cases hq : q ∈ T
    · exact stageTuple_at D T s hT x (detectedFiniteTuple D T s hT x) ⟨q,hq⟩
    · simp [stageTuple,places,hq]

def detectedJacquetTuple (q : T) :
    Jacquet F R.A.zeta12 R.A.primitive_zeta12 T (character T) (fiber D T) (action D T) q :=
  rootCoinvariantsMk (action D T q)
    (KPLocalSmoothRepresentation.upperRoot F R.A.zeta12 R.A.primitive_zeta12 q.val)
    (character T q) (detectedFiniteTuple D T s hT x q)

theorem detectedJacquet_pure :
    WildCurrentJointForm.jointForm D T s hT x (PiTensorProduct.tprod ℂ (detectedJacquetTuple D T s hT x)) =
      coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x := by
  have hp : tensorQuotient F R.A.zeta12 R.A.primitive_zeta12 T (character T) (fiber D T) (action D T)
      (PiTensorProduct.tprod ℂ (detectedFiniteTuple D T s hT x)) =
      PiTensorProduct.tprod ℂ (detectedJacquetTuple D T s hT x) :=
    PiTensorProduct.map_tprod _ _
  have hj := LinearMap.congr_fun (WildCurrentJointForm.jointForm_comp D T s hT x)
    (PiTensorProduct.tprod ℂ (detectedFiniteTuple D T s hT x))
  change WildCurrentJointForm.jointForm D T s hT x
    (tensorQuotient F R.A.zeta12 R.A.primitive_zeta12 T (character T) (fiber D T) (action D T)
      (PiTensorProduct.tprod ℂ (detectedFiniteTuple D T s hT x))) = _ at hj
  rw [hp,period_pure,stageTuple_detected] at hj
  exact hj

end DedekindZetaZeroFree.FourierContinuation.WildCurrentJointPeriod

end
