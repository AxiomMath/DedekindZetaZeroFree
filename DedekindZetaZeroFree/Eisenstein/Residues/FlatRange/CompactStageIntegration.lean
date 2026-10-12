module

public import DedekindZetaZeroFree.Eisenstein.Residues.FlatRange.CompactApproximation
public import DedekindZetaZeroFree.Eisenstein.Residues.FlatRange.FiniteScalarEvaluation

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ResidualFlatRange
open KPLiteralRaw
open FiniteScalarEvaluation

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance compactStageIntegrationTopologicalGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance compactStageIntegrationMeasurableSpace (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance compactStageIntegrationBorelSpace (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

theorem compactConvolution_mem_typeStage
    (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ)))
    (μ : Measure K) [IsProbabilityMeasure μ]
    (T : KPGlobalEisensteinData.CompactTypeStage
      ((rightAction F ζ hζ).comp K.subtype))
    (u : Functions F ζ hζ) (hu : Continuous u) (huT : u ∈ T.space)
    (h : C(K, ℂ)) :
    compactConvolution F ζ hζ K μ h u ∈ T.space := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let := T.finiteDimensional
  obtain ⟨n, m, x, A, b, hb⟩ :=
    finite_evaluation_reconstruction T.space
  let d : Fin n → ℂ := fun j => ∫ k : K,
    h k * (∑ i, A j i * u (x i * k.val)) ∂μ
  have hcoef (j : Fin n) : Integrable
      (fun k : K => h k * (∑ i, A j i * u (x i * k.val))) μ := by
    have hc : Continuous (fun k : K => h k * (∑ i, A j i * u (x i * k.val))) := by
      apply h.continuous.mul
      apply continuous_finsetSum
      intro i _
      exact continuous_const.mul (hu.comp (continuous_const.mul continuous_subtype_val))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq : compactConvolution F ζ hζ K μ h u = ∑ j, d j • (b j).val := by
    funext g
    simp only [compactConvolution, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hpoint (k : K) : u (g * k.val) =
        ∑ j, (∑ i, A j i * u (x i * k.val)) * (b j).val g := by
      let t : T.space := ⟨rightAction F ζ hζ k.val u, T.invariant k u huT⟩
      exact hb t g
    simp_rw [hpoint, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      dsimp [d]
      simp_rw [← mul_assoc]
      rw [integral_mul_const]
    · intro j _
      simpa only [mul_assoc] using (hcoef j).mul_const ((b j).val g)
  rw [heq]
  exact Submodule.sum_mem _ (fun j _ => T.space.smul_mem _ (b j).property)

end DedekindZetaZeroFree.ResidualFlatRange

end
