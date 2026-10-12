module

public import DedekindZetaZeroFree.Moments.Comparison.NonprincipalFrequencySum
public import DedekindZetaZeroFree.Moments.Principal.FixedMellinWeightErrorEstimates

@[expose] public section

namespace DedekindZetaZeroFree

theorem mellin_probe_growth
    (I f : ℝ → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hI : ∀ ε : ℝ, 0 < ε →
      I =O[Filter.atTop] (fun x : ℝ => x ^ (933 / 2000 + ε : ℝ)))
    (hcomparison : (fun x : ℝ => I x - c * f x) =O[Filter.atTop]
      (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2500))) :
    (∀ ε : ℝ, 0 < ε →
      f =O[Filter.atTop] (fun x : ℝ => x ^ (933 / 2000 + ε : ℝ))) ∧
    (∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => ((x ^ (8 / 15 : ℝ) : ℝ) : ℂ) * f x) =O[Filter.atTop]
        (fun x : ℝ => x ^ (5999 / 6000 + ε : ℝ))) := by
  have hf : ∀ ε : ℝ, 0 < ε →
      f =O[Filter.atTop] (fun x : ℝ => x ^ (933 / 2000 + ε : ℝ)) := by
    intro ε hε
    have hpower : (fun x : ℝ => x ^ ((7 / 15 : ℝ) - 1 / 2500))
        =O[Filter.atTop] (fun x : ℝ => x ^ (933 / 2000 + ε : ℝ)) := by
      apply Filter.Eventually.isBigO
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      apply Real.rpow_le_rpow_of_exponent_le hx
      linarith
    exact (Asymptotics.isBigO_const_mul_left_iff hc).mp
      ((hI ε hε).sub_iff_right.mp (hcomparison.trans hpower))
  refine ⟨hf, ?_⟩
  intro ε hε
  have hweight : (fun x : ℝ => ((x ^ (8 / 15 : ℝ) : ℝ) : ℂ))
      =O[Filter.atTop] (fun x : ℝ => x ^ (8 / 15 : ℝ)) := by
    exact Complex.isBigO_ofReal_left.mpr (Asymptotics.isBigO_refl _ _)
  exact Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow
    (8 / 15) (933 / 2000 + ε) (5999 / 6000 + ε)
    hweight (hf ε hε) (by linarith)

end DedekindZetaZeroFree
