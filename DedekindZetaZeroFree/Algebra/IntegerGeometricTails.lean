module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneMellinShellReassembly

open scoped Topology

set_option maxHeartbeats 800000 in

theorem finite_geometric_tail (c : ℤ → ℂ) (C r : ℂ)
    (hr : r ≠ 0) (hrnorm : ‖r‖ < 1) (nmin n₀ : ℤ) (hle : nmin ≤ n₀)
    (htail : ∀ j : ℤ, n₀ ≤ j → c j = C) :
    HasSum (fun k : ℕ => c (nmin + (k : ℤ)) * r ^ (nmin + (k : ℤ)))
      ((∑ j ∈ Finset.Ico nmin n₀, c j * r ^ j) +
        C * r ^ n₀ / (1 - r)) := by
  let d : ℕ := (n₀ - nmin).toNat
  have hd : nmin + (d : ℤ) = n₀ := by
    dsimp [d]
    omega
  have hgeom : HasSum (fun k : ℕ => C * r ^ n₀ * r ^ k)
      (C * r ^ n₀ / (1 - r)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one hrnorm).mul_left (C * r ^ n₀)
  have hshift : HasSum
      (fun k : ℕ => c (nmin + ((k + d : ℕ) : ℤ)) *
        r ^ (nmin + ((k + d : ℕ) : ℤ)))
      (C * r ^ n₀ / (1 - r)) := by
    apply hgeom.congr_fun
    intro k
    have he : nmin + ((k + d : ℕ) : ℤ) = n₀ + (k : ℤ) := by
      push_cast
      omega
    rw [he, htail _ (by omega), zpow_add₀ hr, zpow_natCast]
    ring
  have hfinite :
      (∑ k ∈ Finset.range d, c (nmin + (k : ℤ)) * r ^ (nmin + (k : ℤ))) =
      ∑ j ∈ Finset.Ico nmin n₀, c j * r ^ j := by
    apply Finset.sum_bij (fun (k : ℕ) _ => nmin + (k : ℤ))
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico]
      omega
    · intro k hk l hl he
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      refine ⟨(j - nmin).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro k hk
      rfl
  simpa only [hfinite] using
    hshift.sum_range_add (f := fun k : ℕ =>
      c (nmin + (k : ℤ)) * r ^ (nmin + (k : ℤ))) (k := d)

end DedekindZetaZeroFree.KPRankOneMellinShellReassembly
