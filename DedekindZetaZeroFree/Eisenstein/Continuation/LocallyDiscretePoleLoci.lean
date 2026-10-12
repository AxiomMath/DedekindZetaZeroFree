module

public import DedekindZetaZeroFree.Adeles.Lattices.AdditiveFundamentalDomain
public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ChamberCosetBounds
public import DedekindZetaZeroFree.Theta.Periods.MeromorphicContinuationAndResidues

@[expose] public section

section

noncomputable section
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ResidualChamberConstruction.CommonExceptional

theorem negative_order_union_locally_discrete_of_cleared_germs
    {X : Type*} (e : ℂ → X → ℂ) (Ω U : Set ℂ)
    (hlocal : ∀ s ∈ Ω,
      ∃ (r : ℝ) (n : ℕ) (c : ℂ → X → ℂ),
        0 < r ∧ Metric.ball s r ⊆ Ω ∧
        (∀ x, AnalyticOnNhd ℂ (fun z => c z x) (Metric.ball s r)) ∧
        (∀ z ∈ Metric.ball s r \ {s}, ∀ x,
          e z x = (z - s) ^ (-(n : ℤ)) * c z x))
    (hregular : ∀ x, AnalyticOnNhd ℂ (fun z => e z x) U) :
    (∀ s ∈ Ω, ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ Metric.ball s r,
        z ∈ {w : ℂ | w ∈ Ω ∧ ∃ x, meromorphicOrderAt (fun v => e v x) w < 0} →
          z = s) ∧
    Disjoint {w : ℂ | w ∈ Ω ∧ ∃ x, meromorphicOrderAt (fun v => e v x) w < 0} U := by
  constructor
  ·
    intro s hs
    obtain ⟨r, n, c, hr, hsub, hc, heq⟩ := hlocal s hs
    refine ⟨r, hr, ?_⟩
    intro z hz hzN
    by_contra hzs
    obtain ⟨-, x, hx⟩ := hzN
    have hnb : Metric.ball s r \ {s} ∈ 𝓝 z := by
      rw [Set.sdiff_eq]
      exact Filter.inter_mem (Metric.isOpen_ball.mem_nhds hz)
        ((isClosed_singleton.isOpen_compl).mem_nhds (by simpa using hzs))
    have hev : (fun v => e v x) =ᶠ[𝓝[≠] z]
        (fun v => (v - s) ^ (-(n : ℤ)) * c v x) := by
      filter_upwards [nhdsWithin_le_nhds hnb] with v hv
      exact heq v hv x
    have hzpow : AnalyticAt ℂ (fun v => (v - s) ^ (-(n : ℤ))) z :=
      (analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hzs)
    have hcaz : AnalyticAt ℂ (fun v => c v x) z := hc x z hz
    have hmul : meromorphicOrderAt (fun v => (v - s) ^ (-(n : ℤ)) * c v x) z
        = meromorphicOrderAt (fun v => (v - s) ^ (-(n : ℤ))) z
          + meromorphicOrderAt (fun v => c v x) z := by
      simpa only [Pi.mul_def] using meromorphicOrderAt_mul (f := fun v => (v - s) ^ (-(n : ℤ)))
        (g := fun v => c v x) hzpow.meromorphicAt hcaz.meromorphicAt
    have hkey : 0 ≤ meromorphicOrderAt (fun v => e v x) z := by
      rw [meromorphicOrderAt_congr hev, hmul]
      exact add_nonneg hzpow.meromorphicOrderAt_nonneg hcaz.meromorphicOrderAt_nonneg
    exact absurd hx (not_lt.mpr hkey)
  ·
    rw [Set.disjoint_left]
    intro w hw hwU
    obtain ⟨-, x, hx⟩ := hw
    exact absurd hx (not_lt.mpr (hregular x w hwU).meromorphicOrderAt_nonneg)

end DedekindZetaZeroFree.KPGlobalResidualKernel.ResidualChamberConstruction.CommonExceptional

end

end
