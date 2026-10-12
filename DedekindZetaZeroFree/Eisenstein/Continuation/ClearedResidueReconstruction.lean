module

public import DedekindZetaZeroFree.Analysis.MeromorphicGermUniqueness
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SpectralCoordinateAndPoleOrders

@[expose] public section

noncomputable section
open scoped Topology Classical
open Filter

namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualRaisingContinuationPin

theorem cleared_identity_on_open {f k a d : ℂ → ℂ} {O V C : Set ℂ}
    (hf : MeromorphicOn f O) (hk : MeromorphicOn k O)
    (hO : IsPreconnected O) (hV : IsOpen V) (hVO : V ⊆ O)
    (hVne : V.Nonempty) (hagree : Set.EqOn f k V)
    (hC : IsOpen C) (hCO : C ⊆ O)
    (ha : ContinuousOn a C) (hd : ContinuousOn d C)
    (hfa : ∀ z ∈ C, z ≠ 0 → a z = z * f z)
    (hkd : ∀ z ∈ C, z ≠ 0 → d z = z * k z) :
    Set.EqOn a d C := by
  intro s hs
  have heq := KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
    hf hk hO hV hVO hVne hagree (hCO hs)
  have hn : ∀ᶠ z in 𝓝[≠] s, z ≠ 0 := by
    by_cases h : s = 0
    · subst s
      exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (continuousAt_id.eventually_ne h)
  have had : a =ᶠ[𝓝[≠] s] d := by
    filter_upwards [heq, hn, nhdsWithin_le_nhds (hC.mem_nhds hs)] with z hz hn hc
    rw [hfa z hc hn, hkd z hc hn, hz]
  exact tendsto_nhds_unique
    (((ha.continuousAt (hC.mem_nhds hs)).tendsto.mono_left nhdsWithin_le_nhds).congr' had)
    ((hd.continuousAt (hC.mem_nhds hs)).tendsto.mono_left nhdsWithin_le_nhds)

end DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualRaisingContinuationPin

end
