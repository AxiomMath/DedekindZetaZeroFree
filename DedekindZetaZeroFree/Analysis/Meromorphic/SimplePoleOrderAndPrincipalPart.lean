module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace DedekindZetaZeroFree.ResidueContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem order_ge_neg_one_of_clearing {f N : ℂ → E} {c : ℂ}
    (hf : MeromorphicAt f c) (hN : AnalyticAt ℂ N c)
    (he : N =ᶠ[𝓝[≠] c] (fun s => (s - c) • f s)) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt f c := by
  have ho := hN.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr he] at ho
  change 0 ≤ meromorphicOrderAt ((fun s => s - c) • f) c at ho
  rw [meromorphicOrderAt_smul
    (show MeromorphicAt (fun s : ℂ => s - c) c from
      (analyticAt_id.sub (analyticAt_const (v := c))).meromorphicAt) hf,
    meromorphicOrderAt_id_sub_const] at ho
  cases h : meromorphicOrderAt f c with
  | top => exact le_top
  | coe n =>
    rw [h] at ho
    have hn : (0 : ℤ) ≤ 1 + n := by exact_mod_cast ho
    exact WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ n by omega)

end DedekindZetaZeroFree.ResidueContinuity

end
