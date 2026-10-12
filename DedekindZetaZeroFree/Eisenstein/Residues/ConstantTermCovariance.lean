module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
open Filter
open scoped Topology

namespace DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.ResidueCovariance

theorem cleared_limit_of_chamber_transformation
    (A B C D p q m : ℂ → ℂ) (U V : Set ℂ)
    (_hU : IsOpen U) (hc : IsConnected U) (hz : (0 : ℂ) ∈ U)
    (hV : IsOpen V) (hne : V.Nonempty) (hsub : V ⊆ U)
    (hA : MeromorphicOn A U) (hB : MeromorphicOn B U)
    (hp : MeromorphicOn p U) (hq : MeromorphicOn q U)
    (hm : MeromorphicOn m U)
    (heq : ∀ s ∈ V, A s - p s = m s * (B s - q s))
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0)
    (hp0 : ContinuousAt p 0) (hq0 : ContinuousAt q 0)
    (hm0 : ContinuousAt m 0)
    (hclearC : C =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => s * A s))
    (hclearD : D =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => s * B s)) :
    C 0 = m 0 * D 0 := by
  let L : ℂ → ℂ := fun s => A s - p s
  let R : ℂ → ℂ := fun s => m s * (B s - q s)
  have hL : MeromorphicOn L U := hA.sub hp
  have hR : MeromorphicOn R U := hm.mul (hB.sub hq)
  obtain ⟨z, hzV⟩ := hne
  have hlocal : L =ᶠ[𝓝[≠] z] R :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hV.mem_nhds hzV)).mono
      (fun s hs => heq s hs)
  have htop : meromorphicOrderAt (L - R) z = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hlocal] with s hs
    exact sub_eq_zero.mpr hs
  have htop0 := (hL.sub hR).meromorphicOrderAt_eq_top_of_isPreconnected
    hc.isPreconnected (hsub hzV) hz htop
  have hout : L =ᶠ[𝓝[≠] (0 : ℂ)] R := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop0] with s hs
    exact sub_eq_zero.mp hs
  have hcleared : (fun s => C s - s * p s) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => m s * (D s - s * q s)) := by
    filter_upwards [hout, hclearC, hclearD] with s hs hcs hds
    dsimp [L, R] at hs
    rw [hcs, hds]
    calc
      s * A s - s * p s = s * (A s - p s) := by ring
      _ = s * (m s * (B s - q s)) := by rw [hs]
      _ = m s * (s * B s - s * q s) := by ring
  have hlcont : ContinuousAt (fun s => C s - s * p s) 0 :=
    hC.sub (continuousAt_id.mul hp0)
  have hrcont : ContinuousAt (fun s => m s * (D s - s * q s)) 0 :=
    hm0.mul (hD.sub (continuousAt_id.mul hq0))
  have he := Filter.EventuallyEq.eq_of_nhds
    ((hlcont.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hrcont).mp hcleared)
  simpa using he

end DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.ResidueCovariance

end
