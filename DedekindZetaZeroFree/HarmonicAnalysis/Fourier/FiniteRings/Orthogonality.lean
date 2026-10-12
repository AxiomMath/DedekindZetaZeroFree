module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped BigOperators Classical

variable {R : Type*} [CommRing R] [Fintype R] [hR : Nontrivial R]

def IsPrimitiveRingAddChar (e : AddChar R ℂ) : Prop :=
  ∀ J : Ideal R, (∀ x ∈ J, e x = 1) → J = ⊥

def finiteRingFourier (e : AddChar R ℂ) (f : R → ℂ) (k : R) : ℂ :=
  ∑ x : R, f x * e (k * x)

include hR in

theorem finiteRingFourier_orthogonality (e : AddChar R ℂ)
    (he : IsPrimitiveRingAddChar e) (y : R) :
    ∑ k : R, e (k * y) = if y = 0 then (Fintype.card R : ℂ) else 0 := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [if_neg hy]
    have hn : e.mulShift y ≠ 1 := by
      intro h
      have hJ : Ideal.span ({y} : Set R) = ⊥ := he _ (by
        intro x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        have ha := congrArg (fun c : AddChar R ℂ => c a) h
        simpa [AddChar.mulShift_apply, mul_comm] using ha)
      have hyJ := Ideal.mem_span_singleton_self y
      rw [hJ, Ideal.mem_bot] at hyJ
      exact hy hyJ
    simpa [AddChar.mulShift_apply, mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one hn)

include hR in

theorem finiteRingFourier_parseval (e : AddChar R ℂ)
    (he : IsPrimitiveRingAddChar e) (f : R → ℂ) :
    ∑ k : R, ‖finiteRingFourier e f k‖ ^ 2 =
      (Fintype.card R : ℝ) * ∑ x : R, ‖f x‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj']
  calc
    ∑ k : R, finiteRingFourier e f k * starRingEnd ℂ (finiteRingFourier e f k) =
        ∑ k : R, ∑ x : R, ∑ z : R,
          (f x * starRingEnd ℂ (f z)) * e (k * (x - z)) := by
      simp only [finiteRingFourier, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      calc
        (f x * e (k * x)) * (starRingEnd ℂ (f z) * starRingEnd ℂ (e (k * z))) =
            (f x * starRingEnd ℂ (f z)) * (e (k * x) * starRingEnd ℂ (e (k * z))) := by ring
        _ = _ := by
          rw [← e.map_neg_eq_conj, ← e.map_add_eq_mul]
          congr 2
          ring
    _ = ∑ x : R, ∑ z : R, ∑ k : R,
          (f x * starRingEnd ℂ (f z)) * e (k * (x - z)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x : R, ∑ z : R, (f x * starRingEnd ℂ (f z)) *
          (if x - z = 0 then (Fintype.card R : ℂ) else 0) := by
      simp_rw [← Finset.mul_sum, finiteRingFourier_orthogonality e he]
    _ = (Fintype.card R : ℂ) * ∑ x : R, f x * starRingEnd ℂ (f x) := by
      simp [sub_eq_zero, Finset.mul_sum, mul_comm]

end

end DedekindZetaZeroFree.Hecke
