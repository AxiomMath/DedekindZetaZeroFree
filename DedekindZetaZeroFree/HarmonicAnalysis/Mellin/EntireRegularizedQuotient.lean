module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.OriginContinuationCharts

@[expose] public section

noncomputable section
open Filter
open scoped NumberField Classical ContDiff Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def originMellinShift (s : ℂ) : ℕ :=
  Nat.ceil (max 0 (-s.re)) + 1

theorem originMellinShift_spec (s : ℂ) :
    -(originMellinShift s : ℝ) < s.re := by
  have hceil : max 0 (-s.re) ≤ ((Nat.ceil (max 0 (-s.re)) : ℕ) : ℝ) := Nat.le_ceil _
  have hcast : ((originMellinShift s : ℕ) : ℝ) =
      ((Nat.ceil (max 0 (-s.re)) : ℕ) : ℝ) + 1 := by
    rw [originMellinShift, Nat.cast_add, Nat.cast_one]
  have hmax : -s.re ≤ max 0 (-s.re) := le_max_right _ _
  linarith

def originMellinQ (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  originMellinChart h (originMellinShift s) s

private theorem originMellinChart_eq_of_lt (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {m n : ℕ} {s : ℂ}
    (hm : -(m : ℝ) < s.re) (hn : -(n : ℝ) < s.re) :
    originMellinChart h m s = originMellinChart h n s := by
  suffices key : ∀ n m : ℕ, m ≤ n → -(m : ℝ) < s.re → -(n : ℝ) < s.re →
      originMellinChart h n s = originMellinChart h m s by
    have hk1 : m ≤ max m n := le_max_left _ _
    have hk2 : n ≤ max m n := le_max_right _ _
    have hmk : -((max m n : ℕ) : ℝ) < s.re := by
      have : ((m : ℕ) : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast hk1
      linarith
    exact (key (max m n) m hk1 hm hmk).symm.trans (key (max m n) n hk2 hn hmk)
  intro n
  induction n with
  | zero =>
      intro m hm _ _
      rw [Nat.le_zero.mp hm]
  | succ n ih =>
      intro m hm hms hns
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · rfl
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        have hn' : -(n : ℝ) < s.re := by
          have : ((m : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hmn
          linarith
        rw [originMellinChart_succ h hh hc n s hn']
        exact ih m hmn hms hn'

theorem originMellinQ_differentiable (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Differentiable ℂ (originMellinQ h) := by
  intro s
  have hn : -((originMellinShift s : ℕ) : ℝ) < s.re := originMellinShift_spec s
  have hchart : DifferentiableAt ℂ
      (originMellinChart h (originMellinShift s)) s :=
    originMellinChart_differentiableAt h hh hc (originMellinShift s) s hn
  refine hchart.congr_of_eventuallyEq ?_
  have hmem : {z : ℂ | -((originMellinShift s : ℕ) : ℝ) < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hn
  filter_upwards [hmem] with z hz
  exact originMellinChart_eq_of_lt h hh hc (originMellinShift_spec z) hz

theorem originMellinQ_eq_chart (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (n : ℕ) (s : ℂ)
    (hs : -(n : ℝ) < s.re) :
    originMellinQ h s = originMellinChart h n s := by
  exact originMellinChart_eq_of_lt h hh hc (originMellinShift_spec s) hs

theorem originMellinQ_eq_mellin_div_Gammaℂ (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (s : ℂ) (hs : 0 < s.re) :
    originMellinQ h s = mellin h s / Complex.Gammaℂ s := by
  rw [originMellinQ_eq_chart h hh hc 0 s (by simpa using hs)]
  simp [originMellinChart, div_eq_mul_inv]

end DedekindZetaZeroFree.LargeSieve.Vendor

end
