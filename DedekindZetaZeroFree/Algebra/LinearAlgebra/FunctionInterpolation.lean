module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

public section

noncomputable section

open scoped Classical

namespace DedekindZetaZeroFree.FiniteFunctionSpaces

private def pointEvaluation {X : Type*} (S : Submodule ℂ (X → ℂ)) (x : X) :
    Module.Dual ℂ S := (LinearMap.proj x).comp S.subtype

theorem exists_finite_evaluation_interpolation {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (n : ℕ) (x : Fin n → X) (b : Fin n → S),
      ∀ (f : S) (y : X), f.val y = ∑ i, f.val (x i) * (b i).val y := by
  have htop : Submodule.span ℂ (Set.range (pointEvaluation S)) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro f hf
    have hx : ∃ x, f.val x ≠ 0 := by
      by_contra! hn
      exact hf (Subtype.ext (funext hn))
    obtain ⟨x, hx⟩ := hx
    exact ⟨pointEvaluation S x, ⟨x, rfl⟩, hx⟩
  have hfg : (Submodule.span ℂ (Set.range (pointEvaluation S))).FG := by
    rw [htop]
    exact Module.Finite.fg_top
  obtain ⟨s, hs, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  choose x hx using fun e : s => hs e.property
  let E := Fintype.equivFin s
  let p : Fin (Fintype.card s) → X := fun i => x (E.symm i)
  have hr : Set.range (fun i => pointEvaluation S (p i)) =
      (s : Set (Module.Dual ℂ S)) := by
    ext e
    constructor
    · rintro ⟨i, rfl⟩
      dsimp [p]
      rw [hx]
      exact (E.symm i).property
    · intro he
      exact ⟨E ⟨e, he⟩, by simpa [p] using hx ⟨e, he⟩⟩
  have hp : Submodule.span ℂ (Set.range (fun i => pointEvaluation S (p i))) = ⊤ := by
    rw [hr, ← he, htop]
  let B := Module.finBasis ℂ S
  have hc : ∀ j, ∃ c : Fin (Fintype.card s) → ℂ,
      ∑ i, c i • pointEvaluation S (p i) = B.coord j := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    rw [hp]
    exact Submodule.mem_top
  choose c hc using hc
  refine ⟨Fintype.card s, p, fun i => ∑ j, c j i • B j, ?_⟩
  intro f y
  have hb := congrArg (fun z : S => z.val y) (B.sum_repr f)
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul] at hb
  rw [← hb]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hj := congrArg (fun l : Module.Dual ℂ S => l f) (hc j)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    pointEvaluation, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, Module.Basis.coord_apply] at hj
  rw [← hj, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end DedekindZetaZeroFree.FiniteFunctionSpaces
