module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Spherical.HilbertResolventGerms

@[expose] public section

noncomputable section
open Filter Topology
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

theorem closed_cleared_center_eigen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : E →ₗ.[ℂ] E) (hD : D.IsClosed)
    (a : ℂ → ℂ) (v h w : ℂ → E) (c : ℂ)
    (ha : ContinuousAt a c) (hh : ContinuousAt h c) (hw : ContinuousAt w c)
    (he : ∀ᶠ s in 𝓝[≠] c, ∃ hv : v s ∈ D.domain,
      D ⟨v s, hv⟩ - a s • v s = -(h s))
    (hclear : ∀ᶠ s in 𝓝[≠] c, w s = (s-c) • v s) :
    (w c, a c • w c) ∈ D.graph := by
  have hg : ∀ᶠ s in 𝓝[≠] c, (w s, a s • w s - (s-c) • h s) ∈ D.graph := by
    filter_upwards [he, hclear] with s hs hws
    obtain ⟨hv, heq⟩ := hs
    have hm := D.graph.smul_mem (s-c) (D.mem_graph ⟨v s, hv⟩)
    have hvEq : D ⟨v s, hv⟩ = -(h s) + a s • v s := sub_eq_iff_eq_add.mp heq
    simpa only [Prod.smul_mk, hws, hvEq, smul_add, smul_neg, smul_smul,
      mul_comm, sub_eq_add_neg, add_comm] using hm
  have ht : Tendsto (fun s => (w s, a s • w s - (s-c) • h s)) (𝓝[≠] c)
      (𝓝 (w c, a c • w c)) := by
    have hc : ContinuousAt (fun s => (w s, a s • w s - (s-c) • h s)) c := hw.prodMk ((ha.smul hw).sub ((continuousAt_id.sub continuousAt_const).smul hh))
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact hD.mem_of_tendsto ht hg

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
