module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.InverseTensorSlots

@[expose] public section

noncomputable section
open scoped Classical
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype

private theorem harmonic_preimage (ℓ : ℕ) (h : PrincipalSeries negativeParameter)
    (hh : h ∈ harmonicKType negativeParameter ℓ) :
    ∃ f : PrincipalSeries positiveParameter,
      f ∈ harmonicKType positiveParameter ℓ ∧ standardIntertwiner (1 : ℂˣ) f = h := by
  have hm : compactRestriction negativeParameter h ∈
      (harmonicKType positiveParameter ℓ).map (compactRestriction positiveParameter) := by
    rw [← (harmonicKType_compact_identification negativeParameter positiveParameter ℓ).2]
    exact ⟨h, hh, rfl⟩
  obtain ⟨u, hu, he⟩ := hm
  let a : ℂ := (eigenvalue (1 : ℂˣ) ℓ : ℂ)⁻¹
  have hn : (eigenvalue (1 : ℂˣ) ℓ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (eigenvalue_ne_zero (1 : ℂˣ) ℓ)
  refine ⟨a • u, (harmonicKType positiveParameter ℓ).smul_mem a hu, ?_⟩
  apply compactRestriction_injective negativeParameter
  rw [map_smul, map_smul, (standardIntertwiner_harmonic_eigenvalue (1 : ℂˣ) ℓ u hu).2,
    smul_smul]
  simp only [a, inv_mul_cancel₀ hn, one_smul]
  exact he

theorem harmonic_preimage_exists (v : complexCore) :
    ∃ f : KPLiteralTensor.harmonicPlus, standardIntertwiner (1 : ℂˣ) f.val = v.val := by
  have he : KPLiteralTensor.harmonicPlus.map (standardIntertwiner (1 : ℂˣ)).toLinearMap =
      ⨆ ℓ : ℕ, harmonicKType negativeParameter ℓ := by
    rw [KPLiteralTensor.harmonicPlus, Submodule.map_iSup]
    congr 1
    funext ℓ
    apply le_antisymm
    · rintro h ⟨f, hf, rfl⟩
      exact (standardIntertwiner_harmonic_eigenvalue (1 : ℂˣ) ℓ f hf).1
    · intro h hh
      obtain ⟨f, hf, hfe⟩ := harmonic_preimage ℓ h hh
      exact ⟨f, hf, hfe⟩
  have hv : v.val ∈ KPLiteralTensor.harmonicPlus.map (standardIntertwiner (1 : ℂˣ)).toLinearMap := by
    rw [he]
    exact v.property.2
  obtain ⟨f, hf, hfe⟩ := hv
  exact ⟨⟨f,hf⟩, hfe⟩

theorem inverse_harmonic_mem (v : complexCore) :
    NativeStageSlot.inverse v.val ∈ KPLiteralTensor.harmonicPlus := by
  obtain ⟨f, hf⟩ := harmonic_preimage_exists v
  rw [← hf, NativeStageSlot.inverse_integral]
  exact f.property

def harmonicInverse : complexCore →ₗ[ℂ] KPLiteralTensor.harmonicPlus :=
  (NativeStageSlot.inverse.toLinearMap.comp complexCore.subtype).codRestrict
    KPLiteralTensor.harmonicPlus inverse_harmonic_mem

@[simp] theorem harmonicInverse_val (v : complexCore) :
    (harmonicInverse v).val = NativeStageSlot.inverse v.val := rfl

@[simp] theorem harmonicInverse_pin (v : complexCore) :
    standardIntertwiner (1 : ℂˣ) (harmonicInverse v).val = v.val :=
  NativeStageSlot.integral_inverse v.val

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
