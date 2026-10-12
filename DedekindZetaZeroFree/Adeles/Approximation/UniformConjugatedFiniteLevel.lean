module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLComplex.AdelicSlices
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.Metaplectic.Torus.PhaseTrivialFiniteLevels
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AdelicCovers.CofinalNormalLevels

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
open KPLiteralRaw
open KPGlobalTorusFiniteStagesCofinality
open KPSmoothCofinalNormalLevels

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance finiteStageApproximationTopologicalGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

private theorem finiteSubgroup_eq_finitePart :
    PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ =
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  unfold PGLComplex.AdelicSlices.finiteSubgroup KPGlobalTorusFunctionData.finitePart
  congr 1
  ext x
  simp [PGLComplex.AdelicSlices.finiteTuples, Subgroup.mem_iInf]

 theorem exists_archFiniteSplit :
    ∃ e : (KPSmoothActualFlowData.GInfinity F ×
        KPGlobalTorusFunctionData.finitePart F ζ hζ) ≃ₜ* G F ζ hζ,
      ∀ a c, e (a, c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlices.actual_product_splitting F ζ hζ
  have h : ∃ e : (PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) ≃ₜ*
      PGLComplex.AdelicSlices.ActualCover F ζ hζ,
      ∀ a c, e (a, c) = PGLComplex.AdelicSlices.archimedeanInsertion F ζ hζ a * c.val :=
    ⟨e, he⟩
  rw [finiteSubgroup_eq_finitePart F ζ hζ] at h
  exact h

theorem compact_uniform_conjugated_finite_level
    (C : Set (G F ζ hζ)) (hC : IsCompact C)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    ∃ V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ k ∈ C, ∀ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V,
        k⁻¹ * a * k ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U := by
  classical
  obtain ⟨e, he⟩ := exists_archFiniteSplit F ζ hζ
  have h1 : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (1 : KPSmoothActualFlowData.GInfinity F) = 1 :=
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1

  have hD : IsCompact (Prod.snd '' (e.symm '' C)) :=
    (hC.image e.symm.continuous).image continuous_snd

  obtain ⟨W, hW, hconj⟩ :=
    compact_conjugation_nhds (Prod.snd '' (e.symm '' C)) hD (U.toOpenSubgroup)

  obtain ⟨V, hV⟩ := finitePart_compactOpen_basis F ζ hζ W hW
  refine ⟨V, ?_⟩
  intro k hk a ha
  obtain ⟨v, hv, hvval⟩ := ha
  let x : KPSmoothActualFlowData.GInfinity F := (e.symm k).1
  let c : KPGlobalTorusFunctionData.finitePart F ζ hζ := (e.symm k).2
  have hcD : c ∈ Prod.snd '' (e.symm '' C) := ⟨e.symm k, ⟨k, hk, rfl⟩, rfl⟩
  have hconjv : c⁻¹ * v * c ∈
      (U.toOpenSubgroup : Subgroup (KPGlobalTorusFunctionData.finitePart F ζ hζ)) :=
    hconj c hcD v (hV hv)
  have hk_eq : k = e (x, c) := by
    rw [← e.apply_symm_apply k]
  have ha_eq : a = e (1, v) := by
    rw [he 1 v, h1, one_mul]
    exact hvval.symm

  have hconj_eq : k⁻¹ * a * k = e (1, c⁻¹ * v * c) := by
    rw [hk_eq, ha_eq]
    simp only [← map_inv, ← map_mul]
    congr 1
    ext <;> simp [mul_assoc]
  rw [hconj_eq, he 1 (c⁻¹ * v * c), h1, one_mul]
  exact ⟨_, hconjv, rfl⟩

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation

end
