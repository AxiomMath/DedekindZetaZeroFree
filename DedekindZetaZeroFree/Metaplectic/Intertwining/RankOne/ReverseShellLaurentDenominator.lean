module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellData

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalPrincipalSeries KPRankOneOpenCellKernel
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]

 def shiftNumerator (p : ShellNumerator) (i j : ℤ) (c : ℂ) : ShellNumerator :=
  c • p.mapDomain (fun ij => (ij.1 + i, ij.2 + j))

private theorem evaluate_add (p s : ShellNumerator) (r Q : ℂ) :
    evaluateNumerator (p + s) r Q = evaluateNumerator p r Q + evaluateNumerator s r Q := by
  unfold evaluateNumerator
  apply Finsupp.sum_add_index'
  · intro ij; simp
  · intro ij a b; ring

private theorem evaluate_neg (p : ShellNumerator) (r Q : ℂ) :
    evaluateNumerator (-p) r Q = -evaluateNumerator p r Q := by
  have h := evaluate_add p (-p) r Q
  have hzero : evaluateNumerator (0 : ShellNumerator) r Q = 0 := by
    simp [evaluateNumerator]
  rw [add_neg_cancel, hzero] at h
  linear_combination -h

private theorem evaluate_shift (p : ShellNumerator) (i j : ℤ) (c r Q : ℂ)
    (hr : r ≠ 0) (hQ : Q ≠ 0) :
    evaluateNumerator (shiftNumerator p i j c) r Q =
      c * r ^ i * Q ^ j * evaluateNumerator p r Q := by
  unfold shiftNumerator evaluateNumerator
  rw [Finsupp.sum_smul_index (fun _ => by simp)]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  simp only [zpow_add₀ hr, zpow_add₀ hQ]
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  ring

theorem combine_laurent_shell_numerators (p₀ pA pInf : ShellNumerator) :
    ∃ p : ShellNumerator, ∀ r Q : ℂ, r ≠ 0 → Q ≠ 0 →
      shellDenominator F q r Q ≠ 0 →
      evaluateNumerator p r Q / shellDenominator F q r Q =
        (evaluateNumerator p₀ r Q / ((1 - t F q r) * smallFactor F q r Q) +
          evaluateNumerator pA r Q / (1 - t F q r)) +
        evaluateNumerator pInf r Q / ((1 - t F q r) * infinityFactor F q Q) := by
  classical
  let k : ℂ := (residueCardinality (LocalField F q) : ℂ) ^ (-3 : ℤ)
  let b : ℂ := (residueCardinality (LocalField F q) : ℂ)
  let mInf : ShellNumerator → ShellNumerator := fun s => s + -shiftNumerator s 0 (-3) k
  let mSmall : ShellNumerator → ShellNumerator := fun s => s + -shiftNumerator s (-6) 3 b
  refine ⟨(mInf p₀ + mInf (mSmall pA)) + mSmall pInf, ?_⟩
  intro r Q hr hQ hd
  have eInf (s : ShellNumerator) :
      evaluateNumerator (mInf s) r Q = evaluateNumerator s r Q * infinityFactor F q Q := by
    dsimp [mInf]
    rw [evaluate_add, evaluate_neg, evaluate_shift s 0 (-3) k r Q hr hQ]
    simp only [zpow_zero]
    dsimp [infinityFactor, k]
    ring
  have eSmall (s : ShellNumerator) :
      evaluateNumerator (mSmall s) r Q = evaluateNumerator s r Q * smallFactor F q r Q := by
    dsimp [mSmall]
    rw [evaluate_add, evaluate_neg, evaluate_shift s (-6) 3 b r Q hr hQ]
    simp only [smallFactor, t, mul_inv_rev, inv_inv, zpow_neg, zpow_natCast, inv_pow]
    dsimp [b]
    norm_num only [zpow_neg, zpow_natCast]
    ring_nf
    rw [inv_pow r 6]
    rfl
  rw [evaluate_add, evaluate_add, eInf, eInf, eSmall, eSmall]
  change (1 - t F q r) * smallFactor F q r Q * infinityFactor F q Q ≠ 0 at hd
  have h1 : 1 - t F q r ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).1).1
  have hs : smallFactor F q r Q ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).1).2
  have hi : infinityFactor F q Q ≠ 0 := (mul_ne_zero_iff.mp hd).2
  change _ / ((1 - t F q r) * smallFactor F q r Q * infinityFactor F q Q) = _
  field_simp
  <;> ring

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion
