module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
open scoped Classical BigOperators
namespace DedekindZetaZeroFree.ResidualFlatRange.FiniteScalarEvaluation

private def pointEvaluation {X : Type*} (S : Submodule ℂ (X → ℂ)) (x : X) :
    Module.Dual ℂ S := (LinearMap.proj x).comp S.subtype

private theorem finite_evaluation_dual_span {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (m : ℕ) (x : Fin m → X),
      Submodule.span ℂ (Set.range (fun i => pointEvaluation S (x i))) = ⊤ := by
  have htop : Submodule.span ℂ (Set.range (pointEvaluation S)) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro h hh
    have hx : ∃ x, h.val x ≠ 0 := by
      by_contra! hn
      apply hh
      apply Subtype.ext
      funext x
      exact hn x
    obtain ⟨x, hx⟩ := hx
    exact ⟨pointEvaluation S x, ⟨x, rfl⟩, hx⟩
  have hfg : (Submodule.span ℂ (Set.range (pointEvaluation S))).FG := by
    rw [htop]
    exact Module.Finite.fg_top
  obtain ⟨s, hs, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  have hx : ∀ e : s, ∃ x, pointEvaluation S x = e.val := by
    intro e
    exact hs e.property
  choose x hx using hx
  let E := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => x (E.symm i), ?_⟩
  have hr : Set.range (fun i => pointEvaluation S (x (E.symm i))) = (s : Set (Module.Dual ℂ S)) := by
    ext e
    constructor
    · rintro ⟨i, rfl⟩
      dsimp only
      rw [hx]
      exact (E.symm i).property
    · intro he
      refine ⟨E ⟨e, he⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      exact hx ⟨e, he⟩
  rw [hr, ← he, htop]

theorem finite_evaluation_reconstruction {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (n m : ℕ) (x : Fin m → X) (A : Fin n → Fin m → ℂ)
      (b : Fin n → S),
      ∀ (h : S) (y : X), h.val y = ∑ j, (∑ i, A j i * h.val (x i)) * (b j).val y := by
  obtain ⟨m, x, hx⟩ := finite_evaluation_dual_span S
  let b := Module.finBasis ℂ S
  have hc : ∀ j, ∃ A : Fin m → ℂ,
      ∑ i, A i • pointEvaluation S (x i) = b.coord j := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    rw [hx]
    exact Submodule.mem_top
  choose A hA using hc
  refine ⟨Module.finrank ℂ S, m, x, A, b, ?_⟩
  intro h y
  have hr := congrArg (fun z : S => z.val y) (b.sum_repr h)
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul] at hr
  rw [← hr]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he := congrArg (fun e : Module.Dual ℂ S => e h) (hA j)
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    pointEvaluation, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, Module.Basis.coord_apply] using he.symm

end DedekindZetaZeroFree.ResidualFlatRange.FiniteScalarEvaluation

end
