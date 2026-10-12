module

public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalizedFormGraph

theorem dense_bounded_extension
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E V W H : Type*} [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (e : E →ₗ[𝕜] V) (he : DenseRange e)
    (S : E →ₗ[𝕜] W) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u, ‖S u‖ ≤ C * ‖e u‖)
    (J : W →L[𝕜] H) (T : V →L[𝕜] H)
    (hprojection : ∀ u, J (S u) = T (e u)) :
    ∃ L : V →L[𝕜] W, ‖L‖ ≤ C ∧ (∀ u, L (e u) = S u) ∧ J.comp L = T := by
  set L : V →L[𝕜] W := LinearMap.extendOfNorm (σ₁₂ := RingHom.id 𝕜) S e with hL
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [hL]
    exact LinearMap.opNorm_extendOfNorm_le he hC hbound
  · intro u
    rw [hL]
    exact LinearMap.extendOfNorm_eq he ⟨C, hbound⟩ u
  · apply DFunLike.coe_injective
    refine DenseRange.equalizer he (J.comp L).continuous T.continuous ?_
    ext u
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply, hL,
      LinearMap.extendOfNorm_eq he ⟨C, hbound⟩ u, hprojection u]

end DedekindZetaZeroFree.KPLocalizedFormGraph

end
