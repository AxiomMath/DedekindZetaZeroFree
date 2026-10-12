module

public import Mathlib.RepresentationTheory.Invariants

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Rep/ChangeOfGroup.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

public noncomputable section

universe u uG uH uK uL uV uW uU

namespace Representation

section Monoid

variable {R : Type u} {G : Type uG} {H : Type uH} {K : Type uK}
  {V : Type uV} {W : Type uW} {U : Type uU}
  [Semiring R] [Monoid G] [Monoid H] [Monoid K]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [AddCommMonoid U] [Module R U]

instance isTrivial_comp (σ : Representation R H W) [σ.IsTrivial] (f : G →* H) :
    Representation.IsTrivial (σ.comp f) :=
  ⟨fun g ↦ IsTrivial.out (f g)⟩

end Monoid

section Norm

variable {R : Type u} {G : Type uG} {H : Type uH} {V : Type uV} {W : Type uW}
  [Semiring R] [Group G] [Group H] [Fintype G] [Fintype H]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

theorem IsIntertwiningMap.comp_norm {ρ : Representation R G V} {σ : Representation R H W}
    {e : G ≃* H} {φ : V →ₗ[R] W} (hφ : ρ.IsIntertwiningMap (σ.comp (e : G →* H)) φ) :
    φ ∘ₗ ρ.norm = σ.norm ∘ₗ φ := by
  ext x
  simpa [Representation.norm] using
    Fintype.sum_equiv e.toEquiv (fun g ↦ φ (ρ g x)) (fun h ↦ σ h (φ x))
      fun g ↦ hφ.isIntertwining g x

end Norm

end Representation

end
