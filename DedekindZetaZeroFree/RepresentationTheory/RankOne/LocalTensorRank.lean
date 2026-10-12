module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.WildTensorRankPure
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (V : ι → Type) [∀i,AddCommGroup (V i)] [∀i,Module ℂ (V i)]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem coordinate_injective (x : ∀i,V i) (hx : ∀i,x i≠0) (q : ι) :
    Function.Injective ((PiTensorProduct.tprod ℂ).toLinearMap x q) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change v=0
  by_contra hn
  let u := Function.update x q v
  have hu : ∀i,u i≠0 := by
    intro i
    by_cases hi:i=q
    · subst i;simpa [u] using hn
    · simpa [u,hi] using hx i
  let φ : ∀i,Module.Dual ℂ (V i) := fun i =>
    Classical.choose (Module.Projective.exists_dual_eq_one ℂ (hu i))
  have hφ (i) : φ i (u i)=1 :=
    Classical.choose_spec (Module.Projective.exists_dual_eq_one ℂ (hu i))
  let L := PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ φ)
  have he : L (PiTensorProduct.tprod ℂ u)=1 := by
    simp [L,PiTensorProduct.dualDistrib_apply,hφ]
  change PiTensorProduct.tprod ℂ u=0 at hv
  have hz := congrArg L hv
  rw [map_zero] at hz
  exact one_ne_zero (he.symm.trans hz)

theorem local_rank_le_one (x : ∀i,V i) (hx : ∀i,x i≠0)
    (J : (⨂[ℂ] i,V i) →ₗ[ℂ] ℂ) (hJ : Function.Injective J) (q : ι) :
    Module.rank ℂ (V q)≤1 := by
  let l := J.comp ((PiTensorProduct.tprod ℂ).toLinearMap x q)
  have hi : Function.Injective l := hJ.comp (coordinate_injective V x hx q)
  simpa using LinearMap.rank_le_of_injective l hi

theorem local_rank_le_one_of_detected (x : ∀i,V i)
    (J : (⨂[ℂ] i,V i) →ₗ[ℂ] ℂ) (hJ : Function.Injective J)
    (hx : J (PiTensorProduct.tprod ℂ x)≠0) (q : ι) :
    Module.rank ℂ (V q)≤1 := by
  apply local_rank_le_one V x _ J hJ q
  intro i hi
  apply hx
  rw [(PiTensorProduct.tprod ℂ).map_coord_zero i hi,map_zero]

end DedekindZetaZeroFree.FourierContinuation.WildTensorRankPure

end
