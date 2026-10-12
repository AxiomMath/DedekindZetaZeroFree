module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
open scoped Topology
namespace DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.GlobalScalarPin

 theorem germ_eq_of_open_agreement (a b : ℂ → ℂ)
    (U V : Set ℂ) (hU : IsPreconnected U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U)
    (ha : MeromorphicOn a U) (hb : MeromorphicOn b U)
    (hag : Set.EqOn a b V) (z : ℂ) (hz : z ∈ U) :
    a =ᶠ[𝓝[≠] z] b := by
  obtain ⟨w, hw⟩ := hne
  have heq : a =ᶠ[𝓝[≠] w] b :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hV.mem_nhds hw)).mono
      (fun s hs => hag hs)
  have hwtop : meromorphicOrderAt (a - b) w = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [heq] with s hs
    exact sub_eq_zero.mpr hs
  have hztop := (ha.sub hb).meromorphicOrderAt_eq_top_of_isPreconnected
    hU (hVU hw) hz hwtop
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hztop] with s hs
  exact sub_eq_zero.mp hs

end DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.GlobalScalarPin

end
