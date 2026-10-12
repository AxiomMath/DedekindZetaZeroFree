module

public import DedekindZetaZeroFree.Theta.Periods.FinitePlaces.FaithfulTensorInsertion

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentInsertion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def filler (D : TensorDetected R N) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j) :
    ∀ p, actualLocal R D.finiteData p :=
  fun p => if hp : p ∈ s.val then x ⟨p,hp⟩ else D.references p

def insertion (D : TensorDetected R N) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j)
    (t : Finset (KPHilbert.Place F)) (ht : t ⊆ s.val) :=
  D.coreMap.comp ((RestrictedTensorSimple.stageInclusion _ D.references D.bad s).comp
    (RestrictedTensorSimple.insert (actualLocal R D.finiteData) (filler D s x) t s.val ht))

theorem insertion_injective (D : TensorDetected R N) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j)
    (hx : ∀ j, x j ≠ 0) (t : Finset (KPHilbert.Place F)) (ht : t ⊆ s.val) :
    Function.Injective (insertion D s x t ht) := by
  have he : ∀ p ∉ (∅ : Finset (KPHilbert.Place F)), filler D s x p ≠ 0 := by
    intro p _
    by_cases hp : p ∈ s.val
    · simpa [filler,hp] using hx ⟨p,hp⟩
    · simpa [filler,hp] using D.reference_ne_zero p (fun hb => hp (s.property hb))
  exact D.core_injective.comp ((RestrictedTensorSimple.stageInclusion_injective _
    D.references D.bad D.reference_ne_zero s).comp
      (RestrictedTensorSimple.insert_injective _ (filler D s x) ∅ he
        ⟨t,Finset.empty_subset t⟩ ⟨s.val,Finset.empty_subset s.val⟩ ht))

theorem insertion_pure (D : TensorDetected R N) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j)
    (t : Finset (KPHilbert.Place F)) (ht : t ⊆ s.val)
    (y : ∀ j : t, actualLocal R D.finiteData j) :
    insertion D s x t ht (PiTensorProduct.tprod ℂ y) =
      D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
        (PiTensorProduct.tprod ℂ (fun j : s.val =>
          if h : j.val ∈ t then y ⟨j.val,h⟩ else x j))) := by
  simp only [insertion,LinearMap.comp_apply,RestrictedTensorSimple.insert_pure]
  congr 3
  funext j
  by_cases hj : j.val ∈ t
  · simp [hj]
  · simp [hj,filler,j.property]

end DedekindZetaZeroFree.FourierContinuation.WildCurrentInsertion

end
