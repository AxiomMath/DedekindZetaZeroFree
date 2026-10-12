module

public import DedekindZetaZeroFree.Theta.Periods.PureTensorDetection
public import DedekindZetaZeroFree.Theta.Whittaker.Uniqueness.NormalizedExteriorProducts

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.KPFrozenDetection
open RestrictedTensorSimple
open KPWildActualExteriorFactorization.FiniteComparison

universe u v
variable {J : Type u} (V : J → Type v)
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
variable (e : ∀ j, V j) (bad : Finset J)

def stagePeriod (L : Core V e bad →ₗ[ℂ] ℂ) (s : Level bad) :
    MultilinearMap ℂ (fun j : s.val => V j) ℂ :=
  (L.comp (stageInclusion V e bad s)).compMultilinearMap (PiTensorProduct.tprod ℂ)

@[simp] theorem stagePeriod_apply (L : Core V e bad →ₗ[ℂ] ℂ)
    (s : Level bad) (x : ∀ j : s.val, V j) :
    stagePeriod V e bad L s x = L (stageInclusion V e bad s (PiTensorProduct.tprod ℂ x)) := rfl

theorem detected_initial_of_exterior_comparison
    (L : Core V e bad →ₗ[ℂ] ℂ)
    (ell : ∀ j, V j →ₗ[ℂ] ℂ)
    (hnorm : ∀ j ∉ bad, ell j (e j) = 1)
    (hslot : ∀ (s : Level bad) (j : s.val), (j : J) ∉ bad →
      ∀ (x : ∀ i : s.val, V i) (a : V j),
      stagePeriod V e bad L s (Function.update x j a) =
        stagePeriod V e bad L s (Function.update x j (e j)) * ell j a)
    (z : Core V e bad) (hz : L z ≠ 0) :
    ∃ x : ∀ j : bad, V j,
      L (stageInclusion V e bad ⟨bad, le_rfl⟩ (PiTensorProduct.tprod ℂ x)) ≠ 0 := by
  letI : Nonempty (Level bad) := ⟨⟨bad, le_rfl⟩⟩
  obtain ⟨s, w, rfl⟩ := Module.DirectLimit.exists_of z
  obtain ⟨y, hy⟩ := FourierContinuation.exists_detected_pure
    (L.comp (stageInclusion V e bad s)) w hz
  let x : ∀ j : bad, V j := fun j => y ⟨j, s.property j.property⟩
  let base : ∀ j : s.val, V j := fun j =>
    if h : (j : J) ∈ bad then x ⟨j, h⟩ else e j
  let E : Finset s.val := Finset.univ.filter (fun j => (j : J) ∉ bad)
  have hn : ∀ j ∈ E, ell j (base j) = 1 := by
    intro j hj
    have hj' : (j : J) ∉ bad := (Finset.mem_filter.mp hj).2
    simp only [base, dif_neg hj']
    exact hnorm j hj'
  have hc : ∀ j ∈ E, ∀ t : ∀ i : s.val, V i, ∀ a : V j,
      stagePeriod V e bad L s (Function.update t j a) =
        stagePeriod V e bad L s (Function.update t j (base j)) * ell j a := by
    intro j hj t a
    have hj' : (j : J) ∉ bad := (Finset.mem_filter.mp hj).2
    simpa only [base, dif_neg hj'] using hslot s j hj' t a
  have hp := replace_eq_product_of_slot_comparison
    (stagePeriod V e bad L s) E base y (fun j => ell j) hn hc
  have hpiece : E.piecewise y base = y := by
    funext j
    by_cases hj : (j : J) ∈ bad
    · have hjE : j ∉ E := by simp [E, hj]
      rw [Finset.piecewise_eq_of_notMem _ _ _ hjE]
      simp only [base, dif_pos hj, x]
    · have hjE : j ∈ E := by simp [E, hj]
      exact Finset.piecewise_eq_of_mem _ _ _ hjE
  rw [hpiece] at hp
  have hb : stagePeriod V e bad L s base ≠ 0 := by
    intro hb
    rw [hb, zero_mul] at hp
    exact hy hp
  have hinc : stageInclusion V e bad s (PiTensorProduct.tprod ℂ base) =
      stageInclusion V e bad ⟨bad, le_rfl⟩ (PiTensorProduct.tprod ℂ x) := by
    rw [← insert_pure V e bad s.val s.property x]
    change stageInclusion V e bad s
      (transition V e bad ⟨bad, le_rfl⟩ s s.property (PiTensorProduct.tprod ℂ x)) = _
    exact Module.DirectLimit.of_f
  refine ⟨x, ?_⟩
  simpa only [stagePeriod_apply, hinc] using hb

end DedekindZetaZeroFree.KPFrozenDetection

end
