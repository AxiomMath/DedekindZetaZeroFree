/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import DedekindZetaZeroFree.RepresentationTheory.Compact.Convolution
public import DedekindZetaZeroFree.RepresentationTheory.Compact.RegularRepresentation
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.RepresentativeFunctions

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/Compact/EigenspaceRepresentation.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: retain only the generic compact-group density slice; adapt imports and visibility.
The selected declarations are adapted to the current module interface.
License: repository root LICENSE (Apache-2.0).
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem convolutionCLM_rightRegularLp (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (g : G) :
    convolutionCLM k (rightRegularLp 𝕜 G g f)
      = (convolutionCLM k f).comp (.mulRight g) := by
  rw [rightRegularLp_apply]
  exact ContinuousMap.ext fun x => convolutionCLM_compMeasurePreserving_mul_right k f g x

theorem rightRegularLp_mem_eigenspace_convolutionOperator (k : C(G, 𝕜)) (μ : 𝕜) (g : G)
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    rightRegularLp 𝕜 G g f ∈
      Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ := by
  rw [rightRegularLp_apply]
  exact compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator k μ g hf

noncomputable def convolutionEigenspaceRepresentation (k : C(G, 𝕜)) (μ : 𝕜) :
    ContRepresentation 𝕜 G
      (Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :=
  ContRepresentation.subrepresentation (rightRegularLp 𝕜 G) _
    fun g _ hf => rightRegularLp_mem_eigenspace_convolutionOperator k μ g hf

@[simp]
theorem coe_convolutionEigenspaceRepresentation_apply (k : C(G, 𝕜)) (μ : 𝕜) (g : G)
    (f : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    ((convolutionEigenspaceRepresentation k μ g f : _) : Lp 𝕜 2 (haarProb G))
      = rightRegularLp 𝕜 G g (f : Lp 𝕜 2 (haarProb G)) :=
  ContRepresentation.coe_subrepresentation_apply g f

theorem continuous_convolutionEigenspaceRepresentation (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0) :
    Continuous (convolutionEigenspaceRepresentation k μ) := by
  have := finiteDimensional_eigenspace_convolutionOperator k hμ
  rw [continuous_clm_apply]
  intro f
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  simpa only [Function.comp_def, coe_convolutionEigenspaceRepresentation_apply] using
    continuous_rightRegularLp_apply (f : Lp 𝕜 2 (haarProb G))

theorem exists_smul_convolutionCLM_eq_star_matrixCoeff (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0) :
    ∃ y : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ,
      ∀ f (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ),
        μ⁻¹ • convolutionCLM k f
          = star (ContRepresentation.matrixCoeff (convolutionEigenspaceRepresentation k μ)
              (continuous_convolutionEigenspaceRepresentation k hμ) ⟨f, hf⟩ y) := by
  have := finiteDimensional_eigenspace_convolutionOperator k hμ
  have hπ := continuous_convolutionEigenspaceRepresentation k hμ
  obtain ⟨y, hy⟩ :
      ∃ y : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ,
        ∀ h : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ,
          ⟪y, h⟫_𝕜 = μ⁻¹ * convolutionCLM k (h : Lp 𝕜 2 (haarProb G)) 1 := by
    refine ⟨(InnerProductSpace.toDual 𝕜 _).symm
      (μ⁻¹ • ((ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) (1 : G)).comp
        ((convolutionCLM k).comp
          (Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ).subtypeL))),
      fun h => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      Submodule.coe_subtypeL, Submodule.subtype_apply, ContinuousMap.evalCLM_apply, smul_eq_mul]
  refine ⟨y, fun f hf => ?_⟩
  ext g
  have hg : ⟪y, convolutionEigenspaceRepresentation k μ g ⟨f, hf⟩⟫_𝕜
      = μ⁻¹ * convolutionCLM k f g := by
    rw [hy, coe_convolutionEigenspaceRepresentation_apply, convolutionCLM_rightRegularLp]
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight, one_mul]
  rw [ContinuousMap.star_apply, ContinuousMap.smul_apply, smul_eq_mul,
    ContRepresentation.matrixCoeff_apply, RCLike.star_def, inner_conj_symm, hg]

theorem isRepresentative_smul_convolutionCLM_of_mem_eigenspace (k : C(G, 𝕜)) {μ : 𝕜}
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    IsRepresentative (μ⁻¹ • convolutionCLM k f) := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [inv_zero, zero_smul]
    exact isRepresentative_zero 𝕜 G
  have := finiteDimensional_eigenspace_convolutionOperator k hμ
  obtain ⟨y, hy⟩ := exists_smul_convolutionCLM_eq_star_matrixCoeff k hμ
  rw [hy f hf]
  exact (isRepresentative_matrixCoeff _ _ _ _).star

theorem convolutionCLM_mem_representativeSubmodule_of_mem_iSup_eigenspace (k : C(G, 𝕜))
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ ⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    convolutionCLM k f ∈ representativeSubmodule 𝕜 G := by
  refine Submodule.iSup_induction (motive := fun x => convolutionCLM k x ∈
    representativeSubmodule 𝕜 G) _ hf (fun μ x hx => ?_) (by rw [map_zero]; exact zero_mem _)
    fun x y hx hy => ?_
  · rcases eq_or_ne μ 0 with rfl | hμ
    · rw [convolutionCLM_eq_zero_of_mem_eigenspace_zero k hx]
      exact zero_mem _
    · have hsmul : convolutionCLM k x = μ • (μ⁻¹ • convolutionCLM k x) := by
        rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
      rw [hsmul]
      exact Submodule.smul_mem _ _ (mem_representativeSubmodule_of_isRepresentative
        (isRepresentative_smul_convolutionCLM_of_mem_eigenspace k hx))
  · rw [map_add]
    exact add_mem hx hy

theorem convolutionCLM_mem_closure_representativeSubmodule (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionCLM k f ∈ closure (representativeSubmodule 𝕜 G : Set C(G, 𝕜)) := by
  set S := ⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ
  have htop : S.topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2
      (orthogonalComplement_iSup_eigenspaces_convolutionOperator_eq_bot k hk)
  have hf : f ∈ closure (S : Set (Lp 𝕜 2 (haarProb G))) := by
    rw [← Submodule.topologicalClosure_coe, htop]
    exact Submodule.mem_top
  refine closure_mono ?_
    (image_closure_subset_closure_image (convolutionCLM (G := G) k).continuous ⟨f, hf, rfl⟩)
  rintro - ⟨h, hh, rfl⟩
  exact convolutionCLM_mem_representativeSubmodule_of_mem_iSup_eigenspace k hh

end CompactGroup

end DedekindZetaZeroFree.TauCeti
