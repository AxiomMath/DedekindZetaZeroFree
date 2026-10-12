module

public import DedekindZetaZeroFree.Analysis.SpectralTheory.Resolvents.BelowThresholdMeromorphy

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

theorem graph_eigen_projection_fixed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : E →ₗ.[ℂ] E) (B : E →L[ℂ] E)
    (hB : KPResolventPencil.GenuineInverse D (-1) B)
    (μ : ℝ) (hμ : 0 ≤ μ) (t : E) (ht : (t, (μ : ℂ) • t) ∈ D.graph) :
    KPBelowThresholdResolvent.poleProjection B μ t = t := by
  obtain ⟨td, htval, hteq⟩ := D.mem_graph_iff.mp ht
  obtain ⟨_, _, hleft⟩ := hB
  have hi := hleft td
  rw [htval, hteq] at hi
  have he : (1 + (μ : ℂ)) • B t = t := by
    simpa only [neg_smul, one_smul, sub_neg_eq_add, add_smul, map_add, map_smul,
      add_comm] using hi
  have hn : (1 + (μ : ℂ)) ≠ 0 := by
    have hp : (0 : ℝ) < 1 + μ := by linarith
    exact_mod_cast ne_of_gt hp
  have hbt : B t = (1 + (μ : ℂ))⁻¹ • t := by
    calc
      B t = (1 + (μ : ℂ))⁻¹ • ((1 + (μ : ℂ)) • B t) := by
        rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
      _ = _ := by rw [he]
  apply Submodule.starProjection_eq_self_iff.mpr
  change B t - (((1 + μ)⁻¹ : ℝ) : ℂ) • t = 0
  rw [hbt]
  simp

theorem projected_source_orthogonal_eigentest
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : E →ₗ.[ℂ] E) (B : E →L[ℂ] E)
    (hB : KPResolventPencil.GenuineInverse D (-1) B)
    (μ : ℝ) (hμ : 0 ≤ μ) (t h z : E) (a : ℂ)
    (ht : (t, (μ : ℂ) • t) ∈ D.graph)
    (hz : z = a • KPBelowThresholdResolvent.poleProjection B μ h)
    (hpair : inner ℂ t h = 0) : inner ℂ t z = 0 := by
  have hfix := graph_eigen_projection_fixed D B hB μ hμ t ht
  have hs := (isSelfAdjoint_starProjection (KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹))).isSymmetric t h
  change inner ℂ (KPBelowThresholdResolvent.poleProjection B μ t) h =
    inner ℂ t (KPBelowThresholdResolvent.poleProjection B μ h) at hs
  rw [hfix, hpair] at hs
  rw [hz, inner_smul_right, ← hs, mul_zero]

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
