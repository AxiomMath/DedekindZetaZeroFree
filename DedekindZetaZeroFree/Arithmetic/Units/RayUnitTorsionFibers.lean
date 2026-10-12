module

public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitLogLattice

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))

def rayUnitLogMap : U K m →* Multiplicative (rayUnitLogLattice K m) :=
  AddMonoidHom.toMultiplicativeRight
    (rayUnitLogEmbedding K m).rangeRestrict.toAddMonoidHom

@[simp] theorem rayUnitLogMap_coe (u : U K m) :
    ((rayUnitLogMap K m u).toAdd : logHyperplane K) =
      logAbs K (Additive.ofMul (u : (𝓞 K)ˣ)) := rfl

def rayUnitTorsion : Subgroup (U K m) := (rayUnitLogMap K m).ker

theorem rayUnitTorsion_eq_comap :
    rayUnitTorsion K m =
      (NumberField.Units.torsion K).comap (U K m).subtype := by
  ext u
  change rayUnitLogMap K m u = 1 ↔ (u : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K
  rw [NumberField.Units.mem_torsion]
  constructor
  · intro h v
    have hz : logAbs K (Additive.ofMul (u : (𝓞 K)ˣ)) = 0 := by
      simpa using congrArg (fun x : Multiplicative (rayUnitLogLattice K m) =>
        (x.toAdd : logHyperplane K)) h
    have hv : Real.log (v ((u : (𝓞 K)ˣ) : K)) = 0 :=
      congrFun (congrArg Subtype.val hz) v
    exact NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero.mp
      (by rw [hv, mul_zero])
  · intro h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change Real.log (v ((u : (𝓞 K)ˣ) : K)) = 0
    rw [h v, Real.log_one]

instance finite_rayUnitTorsion : Finite (rayUnitTorsion K m) := by
  let f : rayUnitTorsion K m → NumberField.Units.torsion K := fun u =>
    ⟨(u.val : (𝓞 K)ˣ), by
      exact show u.val ∈ (NumberField.Units.torsion K).comap (U K m).subtype from
        (rayUnitTorsion_eq_comap K m) ▸ u.property⟩
  apply Finite.of_injective f
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : NumberField.Units.torsion K => (x : (𝓞 K)ˣ)) h

def rayUnitTorsionCard : ℕ := Nat.card (rayUnitTorsion K m)

theorem rayUnitTorsionCard_pos : 0 < rayUnitTorsionCard K m := by
  exact Nat.card_pos

theorem nonempty_rayUnitLogFiberEquiv (γ : rayUnitLogLattice K m) :
    Nonempty ({u : U K m // (rayUnitLogMap K m u).toAdd = γ} ≃
      rayUnitTorsion K m) := by
  have hs : Function.Surjective (rayUnitLogMap K m) := by
    intro γ
    obtain ⟨u, hu⟩ := (rayUnitLogEmbedding K m).surjective_rangeRestrict γ.toAdd
    exact ⟨u.toMul, congrArg Multiplicative.ofAdd hu⟩
  refine ⟨(Equiv.subtypeEquivRight (fun u => ?_)).trans
    (MonoidHom.fiberEquivKerOfSurjective hs (Multiplicative.ofAdd γ))⟩
  change (rayUnitLogMap K m u).toAdd = γ ↔
    rayUnitLogMap K m u = Multiplicative.ofAdd γ
  exact Multiplicative.toAdd.injective.eq_iff.symm

def rayUnitLogFiberEquiv (γ : rayUnitLogLattice K m) :
    {u : U K m // (rayUnitLogMap K m u).toAdd = γ} ≃ rayUnitTorsion K m :=
  Classical.choice (nonempty_rayUnitLogFiberEquiv K m γ)

theorem exists_rayUnitLogTorsionEquiv :
    ∃ e : U K m ≃ rayUnitLogLattice K m × rayUnitTorsion K m,
      ∀ u : U K m, (e u).1 = (rayUnitLogMap K m u).toAdd := by
  let f : U K m → rayUnitLogLattice K m := fun u => (rayUnitLogMap K m u).toAdd
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (rayUnitLogFiberEquiv K m)).trans
      (Equiv.sigmaEquivProd _ _)), ?_⟩
  intro u
  rfl

def rayUnitLogTorsionEquiv : U K m ≃ rayUnitLogLattice K m × rayUnitTorsion K m :=
  (exists_rayUnitLogTorsionEquiv K m).choose

@[simp] theorem rayUnitLogTorsionEquiv_fst (u : U K m) :
    (rayUnitLogTorsionEquiv K m u).1 = (rayUnitLogMap K m u).toAdd :=
  (exists_rayUnitLogTorsionEquiv K m).choose_spec u

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
