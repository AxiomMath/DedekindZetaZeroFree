module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Intertwining

@[expose] public section

namespace DedekindZetaZeroFree.CovariantSampling

variable {G : Type*} [Group G]

def V_J (C J : Subgroup G) (chi : C →* ℂ) : Submodule ℂ (G → ℂ) where
  carrier := {f | (∀ (c : C) (g : G), f (c.val * g) = chi c * f g) ∧
    (∀ (j : J) (g : G), f (g * j.val) = f g)}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh
    constructor
    · intro c g
      change f (c.val * g) + h (c.val * g) = chi c * (f g + h g)
      rw [hf.1, hh.1, mul_add]
    · intro j g
      change f (g * j.val) + h (g * j.val) = f g + h g
      rw [hf.2, hh.2]
  smul_mem' := by
    intro a f hf
    constructor
    · intro c g
      change a * f (c.val * g) = chi c * (a * f g)
      rw [hf.1, mul_left_comm]
    · intro j g
      change a * f (g * j.val) = a * f g
      rw [hf.2]

@[simp] theorem mem_V_J (C J : Subgroup G) (chi : C →* ℂ) (f : G → ℂ) :
    f ∈ V_J C J chi ↔
      (∀ (c : C) (g : G), f (c.val * g) = chi c * f g) ∧
      (∀ (j : J) (g : G), f (g * j.val) = f g) := Iff.rfl

theorem covariance {C J : Subgroup G} {chi : C →* ℂ}
    (f : V_J C J chi) (c : C) (g : G) :
    f.val (c.val * g) = chi c * f.val g := f.property.1 c g

theorem right_fixed {C J : Subgroup G} {chi : C →* ℂ}
    (f : V_J C J chi) (j : J) (g : G) :
    f.val (g * j.val) = f.val g := f.property.2 j g

def rightTranslate (C K J : Subgroup G) (chi : C →* ℂ)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
    (k : K) : V_J C J chi →ₗ[ℂ] V_J C J chi where
  toFun f := ⟨fun g => f.val (g * k.val), by
    constructor
    · intro c g
      simpa only [mul_assoc] using f.property.1 c (g * k.val)
    · intro j g
      let j' : J := ⟨k.val⁻¹ * j.val * k.val, hnormalize k j⟩
      have heq : (g * j.val) * k.val = (g * k.val) * j'.val := by
        dsimp [j']
        simp only [mul_assoc, mul_inv_cancel_left]
      change f.val ((g * j.val) * k.val) = f.val (g * k.val)
      rw [heq]
      exact f.property.2 j' (g * k.val)⟩
  map_add' f h := by rfl
  map_smul' a f := by rfl

@[simp] theorem rightTranslate_apply (C K J : Subgroup G) (chi : C →* ℂ)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
    (k : K) (f : V_J C J chi) (g : G) :
    (rightTranslate C K J chi hnormalize k f).val g = f.val (g * k.val) := rfl

def rho_J (C K J : Subgroup G) (chi : C →* ℂ)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J) :
    Representation ℂ K (V_J C J chi) where
  toFun := rightTranslate C K J chi hnormalize
  map_one' := by
    ext f g
    simp [rightTranslate]
  map_mul' k l := by
    ext f g
    simp [rightTranslate, mul_assoc]

@[simp] theorem rho_J_apply (C K J : Subgroup G) (chi : C →* ℂ)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
    (k : K) (f : V_J C J chi) (g : G) :
    (rho_J C K J chi hnormalize k f).val g = f.val (g * k.val) := rfl

def sampleMap (C K J : Subgroup G) (chi : C →* ℂ)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (tau : Representation ℂ K W) (n : ℕ) (r : Fin n → G) :
    tau.IntertwiningMap (rho_J C K J chi hnormalize) →ₗ[ℂ]
      (Fin n → Module.Dual ℂ W) where
  toFun T i :=
    { toFun := fun w => (T w).val (r i)
      map_add' := by
        intro w v
        simp only [map_add, Submodule.coe_add, Pi.add_apply]
      map_smul' := by
        intro a w
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply] }
  map_add' T U := by
    ext i w
    rfl
  map_smul' a T := by
    ext i w
    rfl

@[simp] theorem sampleMap_apply (C K J : Subgroup G) (chi : C →* ℂ)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (tau : Representation ℂ K W) (n : ℕ) (r : Fin n → G)
    (T : tau.IntertwiningMap (rho_J C K J chi hnormalize)) (i : Fin n) (w : W) :
    sampleMap C K J chi hnormalize tau n r T i w = (T w).val (r i) := rfl

end DedekindZetaZeroFree.CovariantSampling
