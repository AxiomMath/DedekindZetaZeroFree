module

public import DedekindZetaZeroFree.Analysis.MellinVerticalIntegral

@[expose] public section

section

noncomputable section
open scoped Topology
open Filter Asymptotics

namespace DedekindZetaZeroFree.LargeSieve.CompactMellin

private lemma eventually_zero_atTop {h : ℝ → ℂ} {a b : ℝ}
    (hsupp : Function.support h ⊆ Set.Icc a b) : h =ᶠ[Filter.atTop] 0 := by
  filter_upwards [Filter.eventually_gt_atTop b] with x hx
  by_contra hne
  exact absurd (hsupp (Function.mem_support.mpr hne)).2 (not_le.mpr hx)

private lemma eventually_zero_nhdsGT {h : ℝ → ℂ} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support h ⊆ Set.Icc a b) : h =ᶠ[𝓝[>] 0] 0 := by
  filter_upwards [Ioo_mem_nhdsGT ha] with x hx
  by_contra hne
  exact absurd (hsupp (Function.mem_support.mpr hne)).1 (not_le.mpr hx.2)

theorem entire_of_positive_compact_support (h : ℝ → ℂ) (a b : ℝ)
    (hh : Continuous h) (hsupp : Function.support h ⊆ Set.Icc a b) (ha : 0 < a) :
    Differentiable ℂ (mellin h) := by
  intro s
  refine mellin_differentiableAt_of_isBigO_rpow (s := s) (a := s.re + 1) (b := s.re - 1)
    ((hh.locallyIntegrable).locallyIntegrableOn _) ?_ ?_ ?_ ?_
  · exact (eventually_zero_atTop hsupp).trans_isBigO (Asymptotics.isBigO_zero _ _)
  · linarith
  · exact (eventually_zero_nhdsGT ha hsupp).trans_isBigO (Asymptotics.isBigO_zero _ _)
  · linarith

end DedekindZetaZeroFree.LargeSieve.CompactMellin

end

end

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical ContDiff Topology FourierTransform
open MeasureTheory Filter
open Asymptotics

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem compact_mellin_differentiable (h : ℝ → ℂ) (a b : ℝ)
    (hh : ContDiff ℝ ∞ h) (hsupp : Function.support h ⊆ Set.Icc a b)
    (ha : 0 < a) (hab : a < b) :
    Differentiable ℂ (mellin h) := by
  exact CompactMellin.entire_of_positive_compact_support h a b hh.continuous hsupp ha

end DedekindZetaZeroFree.LargeSieve.Vendor

end

end
