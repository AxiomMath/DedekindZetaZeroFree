module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.HarmonicCoreFiniteness

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct Classical
namespace DedekindZetaZeroFree.KPLiteralScalarArchTensor
open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

local instance {ι : Type} : AddCommGroup
    (PiTensorProduct ℂ (fun _ : ι => KPLiteralTensor.harmonicPlus)) :=
  Module.addCommMonoidToAddCommGroup ℂ

def compactAction (k : compactSubgroup) :
    KPLiteralTensor.harmonicPlus →ₗ[ℂ] KPLiteralTensor.harmonicPlus where
  toFun f := ⟨KPCplxPrincipalSeriesCharts.pi positiveParameter k f.val, by
    obtain ⟨U, _, hf, hinv, hle⟩ :=
      KPLiteralScalarArchHarmonicCore.finite_invariant_subspace
        positiveParameter f.val f.property
    exact hle (hinv k f.val hf)⟩
  map_add' f g := by
    apply Subtype.ext
    change KPCplxPrincipalSeriesCharts.pi positiveParameter k (f.val + g.val) =
      KPCplxPrincipalSeriesCharts.pi positiveParameter k f.val + KPCplxPrincipalSeriesCharts.pi positiveParameter k g.val
    induction k.val using Quotient.inductionOn with
    | h a => rfl
  map_smul' c f := by
    apply Subtype.ext
    change KPCplxPrincipalSeriesCharts.pi positiveParameter k (c • f.val) = c • KPCplxPrincipalSeriesCharts.pi positiveParameter k f.val
    induction k.val using Quotient.inductionOn with
    | h a => rfl

theorem finite_local_subspace (f : KPLiteralTensor.harmonicPlus) :
    ∃ U : Submodule ℂ KPLiteralTensor.harmonicPlus,
      Module.Finite ℂ U ∧ f ∈ U ∧
        ∀ k (v : KPLiteralTensor.harmonicPlus), v ∈ U → compactAction k v ∈ U := by
  obtain ⟨V, hV, hfV, hinv, hle⟩ :=
    KPLiteralScalarArchHarmonicCore.finite_invariant_subspace
      positiveParameter f.val f.property
  let : Module.Finite ℂ V := hV
  let inc : V →ₗ[ℂ] KPLiteralTensor.harmonicPlus :=
    V.inclusion hle
  refine ⟨inc.range, inferInstance, ?_, ?_⟩
  · exact ⟨⟨f.val, hfV⟩, Subtype.ext rfl⟩
  · intro k v hv
    obtain ⟨w, rfl⟩ := hv
    exact ⟨⟨KPCplxPrincipalSeriesCharts.pi positiveParameter k w.val, hinv k w.val w.property⟩, Subtype.ext rfl⟩

end DedekindZetaZeroFree.KPLiteralScalarArchTensor

end
