module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

noncomputable section

open scoped NumberField Classical ContDiff

def S (b : ℝ) (N : ℕ) (h : ℝ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1),
    sSup ((fun x : ℝ => ‖iteratedDeriv i h x‖) '' Set.Icc 0 b)

def PositiveSideSupport (b : ℝ) (h : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, b < x → h x = 0

def EulerIter : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, f => f
  | j + 1, f => fun x => if 0 < x then (x : ℂ) * deriv (EulerIter j f) x else 0

@[simp] theorem EulerIter_zero (f : ℝ → ℂ) : EulerIter 0 f = f := rfl

theorem EulerIter_succ_of_pos (j : ℕ) (f : ℝ → ℂ) (x : ℝ) (hx : 0 < x) :
    EulerIter (j + 1) f x = (x : ℂ) * deriv (EulerIter j f) x := by
  simp [EulerIter, hx]

theorem S_finite (b : ℝ) (hb : 0 < b) (N : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) :
    ∀ i ∈ Finset.range (N + 1),
      BddAbove ((fun x : ℝ => ‖iteratedDeriv i h x‖) '' Set.Icc 0 b) := by
  intro i _
  have hcont : Continuous (fun x : ℝ => ‖iteratedDeriv i h x‖) :=
    (hh.continuous_iteratedDeriv i (by simp)).norm
  exact (isCompact_Icc.image hcont).bddAbove

theorem S_nonneg (b : ℝ) (hb : 0 < b) (N : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) : 0 ≤ S b N h := by
  unfold S
  exact Finset.sum_nonneg fun i _ =>
    Real.sSup_nonneg fun y ⟨x, _, hy⟩ => hy ▸ norm_nonneg _

end

end DedekindZetaZeroFree.LargeSieve.Vendor
