module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

variable {G V : Type*} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

def SmoothVector (ρ : Representation ℂ G V) (v : V) : Prop :=
  ∃ J : OpenSubgroup G, ∀ j ∈ J, ρ j v = v

def SmoothRepresentation (ρ : Representation ℂ G V) : Prop :=
  ∀ v, SmoothVector ρ v

def fixedSubmodule (ρ : Representation ℂ G V) (J : Subgroup G) : Submodule ℂ V where
  carrier := {v | ∀ j : J, ρ (j : G) v = v}
  zero_mem' := by intro j; simp
  add_mem' := by intro x y hx hy j; simp [hx j, hy j]
  smul_mem' := by intro a x hx j; simp [hx j]

structure CompactOpenLevel (G : Type*) [Group G] [TopologicalSpace G] where
  toOpenSubgroup : OpenSubgroup G
  isCompact : IsCompact (toOpenSubgroup : Set G)

instance : CoeTC (CompactOpenLevel G) (OpenSubgroup G) where
  coe := CompactOpenLevel.toOpenSubgroup

def Admissible (ρ : Representation ℂ G V) : Prop :=
  ∀ J : CompactOpenLevel G, Module.Finite ℂ (fixedSubmodule ρ (J.toOpenSubgroup : Subgroup G))

def rightTranslate (g : G) (f : G → ℂ) : G → ℂ := fun x => f (x * g)

@[simp] theorem mem_fixedSubmodule (ρ : Representation ℂ G V) (J : Subgroup G) (v : V) :
    v ∈ fixedSubmodule ρ J ↔ ∀ j ∈ J, ρ j v = v := by
  constructor
  · intro h j hj; exact h ⟨j, hj⟩
  · intro h j; exact h j j.property

def rightTranslationRepresentation : Representation ℂ G (G → ℂ) where
  toFun g :=
    { toFun := rightTranslate g
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by
    ext f x
    change f (x * 1) = f x
    simp
  map_mul' g h := by
    ext f x
    change f (x * (g * h)) = f ((x * g) * h)
    rw [mul_assoc]

@[simp] theorem rightTranslationRepresentation_apply (g : G) (f : G → ℂ) (x : G) :
    rightTranslationRepresentation g f x = f (x * g) := rfl

end DedekindZetaZeroFree
