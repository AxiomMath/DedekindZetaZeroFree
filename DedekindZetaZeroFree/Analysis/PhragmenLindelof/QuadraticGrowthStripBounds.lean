module

public import Mathlib.Analysis.Complex.PhragmenLindelof

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Asymptotics Topology

theorem quadratic_exp_growth_isBigO_double_exp (a b : ℝ) (hab : a < b)
    (f : ℂ → ℂ)
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, a < s.re ∧ s.re < b →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2)) :
    ∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ D : ℝ,
      f =O[Filter.comap (fun s : ℂ => |s.im|) Filter.atTop ⊓
        Filter.principal {s : ℂ | a < s.re ∧ s.re < b}]
        (fun s : ℂ => Real.exp (D * Real.exp (c * |s.im|))) := by
  obtain ⟨M, B, hM, hB, hg⟩ := hgrowth
  let c : ℝ := (Real.pi / (b - a)) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hclt : c < Real.pi / (b - a) := by
    dsimp [c]
    linarith [div_pos Real.pi_pos (sub_pos.mpr hab)]
  let D : ℝ := (2 * B / c ^ 2) * Real.exp c
  have hpoly (t : ℝ) (ht : 0 ≤ t) :
      B * (1 + t) ^ 2 ≤ D * Real.exp (c * t) := by
    have hct : 0 ≤ c * (1 + t) := mul_nonneg hc.le (by linarith)
    have hquad := Real.quadratic_le_exp_of_nonneg hct
    have hsq : (1 + t) ^ 2 ≤ 2 * Real.exp (c * (1 + t)) / c ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq hB
    dsimp [D]
    calc
      B * (1 + t) ^ 2 ≤ B * (2 * Real.exp (c * (1 + t)) / c ^ 2) := hmul
      _ = (2 * B / c ^ 2 * Real.exp c) * Real.exp (c * t) := by
        rw [mul_add, mul_one, Real.exp_add]
        ring
  refine ⟨c, hclt, D, Asymptotics.IsBigO.of_bound M ?_⟩
  filter_upwards [Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall
    (fun s : ℂ => fun hs : a < s.re ∧ s.re < b => hs))] with s hs
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (hg s hs).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (hpoly |s.im| (abs_nonneg _))) hM)

theorem norm_le_on_closed_strip_of_quadratic_exp_growth (a b C : ℝ)
    (hab : a < b) (f : ℂ → ℂ)
    (hhol : DiffContOnCl ℂ f {s : ℂ | a < s.re ∧ s.re < b})
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, a < s.re ∧ s.re < b →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hleft : ∀ s : ℂ, s.re = a → ‖f s‖ ≤ C)
    (hright : ∀ s : ℂ, s.re = b → ‖f s‖ ≤ C) :
    ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b → ‖f s‖ ≤ C := by
  intro s hs
  exact PhragmenLindelof.vertical_strip hhol
    (quadratic_exp_growth_isBigO_double_exp a b hab f hgrowth)
    hleft hright hs.1 hs.2

end DedekindZetaZeroFree
