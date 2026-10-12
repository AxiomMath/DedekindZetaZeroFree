module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RestrictedTensors.FiniteStageCyclicity

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

def insertedSeed (D : Dictionary R N) (s t : RestrictedTensorSimple.Level D.bad)
    (v : ∀ p : s.val, actualLocal R D.finiteData p) :
    ∀ p : t.val, actualLocal R D.finiteData p :=
  fun p => if h : p.val ∈ s.val then v ⟨p.val, h⟩ else D.references p

theorem insertedSeed_ne_zero (D : Dictionary R N)
    (s t : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (v : ∀ p : s.val, actualLocal R D.finiteData p) (hv : ∀ p, v p ≠ 0) :
    ∀ p, insertedSeed D s t v p ≠ 0 := by
  intro p
  unfold insertedSeed
  split_ifs with h
  · exact hv ⟨p.val, h⟩
  · exact D.reference_ne_zero p (fun hp => h (hs.symm ▸ hp))

theorem insertedSeed_pin (D : Dictionary R N)
    (s t : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (v : ∀ p : s.val, actualLocal R D.finiteData p)
    (hseed : D.selected D.probe = RestrictedTensorSimple.stageInclusion _
      D.references D.bad s (PiTensorProduct.tprod ℂ v)) :
    RestrictedTensorSimple.stageInclusion _ D.references D.bad t
      (PiTensorProduct.tprod ℂ (insertedSeed D s t v)) = D.selected D.probe := by
  have hst : s ≤ t := fun p hp => t.property (hs ▸ hp)
  have he := RestrictedTensorSimple.insert_pure (actualLocal R D.finiteData)
    D.references s.val t.val hst v
  have hm := congrArg (RestrictedTensorSimple.stageInclusion
    (actualLocal R D.finiteData) D.references D.bad t) he
  convert hm.symm.trans (Module.DirectLimit.of_f.trans hseed.symm) using 1
  congr 1
  congr 1
  funext p
  simp only [insertedSeed]
  split_ifs <;> rfl

theorem insertedSeed_cyclic (D : Dictionary R N)
    (s t : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (v : ∀ p : s.val, actualLocal R D.finiteData p) (hv : ∀ p, v p ≠ 0) :
    tupleOrbitSpan (fun p : t.val => localOperation R D.finiteData p)
      (insertedSeed D s t v) = ⊤ :=
  actual_stage_cyclic R D.finiteData t.val _ (insertedSeed_ne_zero D s t hs v hv)

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
