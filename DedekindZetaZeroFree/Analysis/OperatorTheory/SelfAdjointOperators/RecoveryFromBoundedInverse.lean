module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree
namespace ResolventOperator

def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H,
    (∀ f : H, ∃ hf : R f ∈ A.domain, A ⟨R f, hf⟩ - z • R f = f) ∧
    (∀ u : A.domain, R (A u - z • (u : H)) = (u : H))}

def fromBoundedInverse {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) (hB : Function.Injective B) : H →ₗ.[ℂ] H where
  domain := LinearMap.range B.toLinearMap
  toFun := (LinearEquiv.ofInjective B.toLinearMap hB).symm.toLinearMap -
    (LinearMap.range B.toLinearMap).subtype

theorem fromBoundedInverse_domain {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (B : H →L[ℂ] H) (hB : Function.Injective B) :
    (fromBoundedInverse B hB).domain = LinearMap.range B.toLinearMap := rfl

theorem fromBoundedInverse_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (B : H →L[ℂ] H) (hB : Function.Injective B) (f : H) :
    fromBoundedInverse B hB ⟨B f, ⟨f, rfl⟩⟩ = f - B f := by
  change (LinearEquiv.ofInjective B.toLinearMap hB).symm
    ((LinearEquiv.ofInjective B.toLinearMap hB) f) - B f = f - B f
  rw [LinearEquiv.symm_apply_apply]

end ResolventOperator

theorem kp_cont_resolvent_selfadjoint_operator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (hsa : IsSelfAdjoint B) (hinj : Function.Injective B)
    (hdense : DenseRange B) (hquad : ∀ f : H, ‖B f‖ ^ 2 ≤ (inner ℂ f (B f)).re) :
    let Δ := ResolventOperator.fromBoundedInverse B hinj
    IsSelfAdjoint Δ ∧ Δ.IsClosed ∧
      (∀ u : Δ.domain, 0 ≤ (inner ℂ (u : H) (Δ u)).re) ∧
      (∀ f : H, ∃ hf : B f ∈ Δ.domain, (B f : H) + Δ ⟨B f, hf⟩ = f) ∧
      (∀ u : Δ.domain, B ((u : H) + Δ u) = (u : H)) ∧
      (-1 : ℂ) ∈ ResolventOperator.resolventSet Δ := by
  let Δ := ResolventOperator.fromBoundedInverse B hinj
  change IsSelfAdjoint Δ ∧ _
  have hD : Dense (Δ.domain : Set H) := by
    change Dense (LinearMap.range B.toLinearMap : Set H)
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe, DenseRange] using hdense
  have hsym (f g : H) : inner ℂ (B f) g = inner ℂ f (B g) := hsa.isSymmetric f g
  have hform : Δ.IsFormalAdjoint Δ := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    rcases hu with ⟨f, rfl⟩
    rcases hv with ⟨g, rfl⟩
    dsimp only [Δ]
    erw [ResolventOperator.fromBoundedInverse_apply,
      ResolventOperator.fromBoundedInverse_apply, inner_sub_left, inner_sub_right]
    exact congrArg (fun t : ℂ => t - inner ℂ (B f) (B g)) (hsym f g).symm
  have hforward : Δ ≤ Δ.adjoint := hform.le_adjoint hD
  have hback : Δ.adjoint ≤ Δ := by
    have hrecover (z : Δ.adjoint.domain) : (z : H) = B ((z : H) + Δ.adjoint z) := by
      apply ext_inner_right ℂ
      intro f
      have hh := LinearPMap.adjoint_isFormalAdjoint hD z ⟨B f, ⟨f, rfl⟩⟩
      erw [ResolventOperator.fromBoundedInverse_apply, inner_sub_right] at hh
      calc
        inner ℂ (z : H) f = inner ℂ (z : H) (B f) + inner ℂ (Δ.adjoint z) (B f) := by
          rw [hh]
          abel
        _ = inner ℂ (B ((z : H) + Δ.adjoint z)) f := by
          rw [map_add, inner_add_left, hsym (z : H) f, hsym (Δ.adjoint z) f]
    refine ⟨?_, ?_⟩
    · intro z hz
      exact ⟨z + Δ.adjoint ⟨z, hz⟩, (hrecover ⟨z, hz⟩).symm⟩
    · intro z u hzu
      have hu : u = ⟨B ((z : H) + Δ.adjoint z), ⟨(z : H) + Δ.adjoint z, rfl⟩⟩ :=
        Subtype.ext (hzu.symm.trans (hrecover z))
      rw [hu, ResolventOperator.fromBoundedInverse_apply, ← hrecover z]
      abel
  have hself : IsSelfAdjoint Δ := by
    exact (LinearPMap.isSelfAdjoint_def).mpr (le_antisymm hback hforward)
  have hpositive : ∀ u : Δ.domain, 0 ≤ (inner ℂ (u : H) (Δ u)).re := by
    rintro ⟨u, hu⟩
    rcases hu with ⟨f, rfl⟩
    dsimp only [Δ]
    erw [ResolventOperator.fromBoundedInverse_apply, inner_sub_right, Complex.sub_re]
    change 0 ≤ (inner ℂ (B f) f).re - (inner ℂ (B f) (B f)).re
    rw [hsym f f, inner_self_eq_norm_sq_to_K]
    norm_cast
    exact sub_nonneg.mpr (hquad f)
  have hleft : ∀ f : H, ∃ hf : B f ∈ Δ.domain, (B f : H) + Δ ⟨B f, hf⟩ = f := by
    intro f
    refine ⟨⟨f, rfl⟩, ?_⟩
    erw [ResolventOperator.fromBoundedInverse_apply]
    abel
  have hright : ∀ u : Δ.domain, B ((u : H) + Δ u) = (u : H) := by
    rintro ⟨u, hu⟩
    rcases hu with ⟨f, rfl⟩
    erw [ResolventOperator.fromBoundedInverse_apply]
    change B (B f + (f - B f)) = B f
    congr 1
    abel
  refine ⟨hself, hself.isClosed, hpositive, hleft, hright, ?_⟩
  refine ⟨B, ?_, ?_⟩
  · intro f
    obtain ⟨hf, heq⟩ := hleft f
    refine ⟨hf, ?_⟩
    simpa only [neg_smul, one_smul, sub_neg_eq_add, add_comm] using heq
  · intro u
    simpa only [neg_smul, one_smul, sub_neg_eq_add, add_comm] using hright u

end DedekindZetaZeroFree

end
