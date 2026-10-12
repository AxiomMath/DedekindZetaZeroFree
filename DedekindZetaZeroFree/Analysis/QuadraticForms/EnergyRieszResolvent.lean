module

public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree

def energyRieszResolvent
    {W H : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (j : W →L[ℂ] H) : H →L[ℂ] H :=
  j.comp j.adjoint

theorem energyRieszResolvent_properties
    {W H : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (j : W →L[ℂ] H) (hinj : Function.Injective j) (hdense : DenseRange j)
    (hcontract : ‖j‖ ≤ 1) :
    IsSelfAdjoint (energyRieszResolvent j) ∧
      (energyRieszResolvent j).IsPositive ∧
      Function.Injective (energyRieszResolvent j) ∧
      DenseRange (energyRieszResolvent j) ∧ ‖energyRieszResolvent j‖ ≤ 1 := by

  have hBsa : IsSelfAdjoint (energyRieszResolvent j) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    simp [energyRieszResolvent]

  have hBpos : (energyRieszResolvent j).IsPositive := by
    simpa [energyRieszResolvent] using ContinuousLinearMap.isPositive_self_comp_adjoint j

  have hker_adj : j.adjoint.ker = ⊥ := by
    have hd : Dense (j.range : Set H) := hdense
    have hcl : j.range.topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp hd
    have horth : j.rangeᗮ = ⊥ := Submodule.topologicalClosure_eq_top_iff.mp hcl
    rw [← ContinuousLinearMap.orthogonal_range j]
    exact horth
  have hBker : (energyRieszResolvent j).ker = ⊥ := by
    rw [energyRieszResolvent, ContinuousLinearMap.ker_self_comp_adjoint, hker_adj]
  have hBinj : Function.Injective (energyRieszResolvent j) :=
    (LinearMap.ker_eq_bot (f := (energyRieszResolvent j : H →ₗ[ℂ] H))).mp hBker

  have hBdense : DenseRange (energyRieszResolvent j) := by
    have horth : (energyRieszResolvent j).rangeᗮ = ⊥ := by
      rw [ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.isSelfAdjoint_iff'.mp hBsa]
      exact hBker
    have hcl : (energyRieszResolvent j).range.topologicalClosure = ⊤ :=
      Submodule.topologicalClosure_eq_top_iff.mpr horth
    have hd : Dense (((energyRieszResolvent j).range : Submodule ℂ H) : Set H) :=
      Submodule.dense_iff_topologicalClosure_eq_top.mpr hcl
    exact hd

  have hnorm : ‖energyRieszResolvent j‖ ≤ 1 := by
    rw [energyRieszResolvent]
    calc ‖j ∘L j.adjoint‖ ≤ ‖j‖ * ‖j.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖j‖ * ‖j‖ := by rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint j]
      _ ≤ 1 := by nlinarith [norm_nonneg j, hcontract]
  exact ⟨hBsa, hBpos, hBinj, hBdense, hnorm⟩

theorem energyRieszResolvent_variational
    {W H : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (j : W →L[ℂ] H) (f : H) :
    (∀ z : W, inner ℂ (j.adjoint f) z = inner ℂ f (j z)) ∧
      (∀ w : W, (∀ z : W, inner ℂ w z = inner ℂ f (j z)) → w = j.adjoint f) ∧
      energyRieszResolvent j f = j (j.adjoint f) := by
  refine ⟨fun z => j.adjoint_inner_left z f, fun w hw => ?_, rfl⟩

  refine ext_inner_right ℂ fun z => ?_
  rw [hw z, ← j.adjoint_inner_left z f]

theorem energyRieszResolvent_estimates
    {W H : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (j : W →L[ℂ] H) (hcontract : ‖j‖ ≤ 1) (f : H) :
    ‖energyRieszResolvent j f‖ ^ 2 ≤ (inner ℂ f (energyRieszResolvent j f)).re ∧
      (inner ℂ f (energyRieszResolvent j f)).re = ‖j.adjoint f‖ ^ 2 ∧
      ‖j.adjoint f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hBf : energyRieszResolvent j f = j (j.adjoint f) := rfl

  have h1 : (inner ℂ f (energyRieszResolvent j f)).re = ‖j.adjoint f‖ ^ 2 := by
    rw [hBf, ← j.adjoint_inner_left (j.adjoint f) f]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (j.adjoint f)
  have h2 : ‖energyRieszResolvent j f‖ ≤ ‖j.adjoint f‖ := by
    rw [hBf]
    calc ‖j (j.adjoint f)‖ ≤ ‖j‖ * ‖j.adjoint f‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖j.adjoint f‖ := by gcongr
      _ = ‖j.adjoint f‖ := one_mul _
  have h3 : ‖j.adjoint f‖ ≤ ‖f‖ := by
    calc ‖j.adjoint f‖ ≤ ‖j.adjoint‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖j‖ * ‖f‖ := by rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint j]
      _ ≤ 1 * ‖f‖ := by gcongr
      _ = ‖f‖ := one_mul _
  exact ⟨by rw [h1]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2, h1,
    pow_le_pow_left₀ (norm_nonneg _) h3 2⟩

end DedekindZetaZeroFree

end
