module

public import DedekindZetaZeroFree.Metaplectic.Induction.LocalSectionProductEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPActualReflectionData.LiteralProductPointBound
open KPGlobalResidualConstruction KPLiteralTensor KPCplxPrincipalSeriesCharts
open LiteralProductEvaluator

local instance : AddCommGroup harmonicPlus := Submodule.addCommGroup harmonicPlus
local instance : Module ℂ harmonicPlus := Submodule.module harmonicPlus
local instance : TopologicalSpace harmonicPlus := instTopologicalSpaceSubtype

theorem principalSeries_matrix_evaluation_joint (a : ℝ) :
    Continuous (fun p : PrincipalSeries a × KPCplxCharacterHaar.ComplexGL2 => p.1 p.2) := by
  have h := (KPCplxHarmonicExtraction.principalSeries_evaluation_continuous a 1).comp
    ((pi_continuous a).comp
      (((QuotientGroup.continuous_mk).comp continuous_snd).prodMk continuous_fst))
  exact h.congr (fun p => by change p.1 (1 * p.2) = p.1 p.2; rw [one_mul])

def compactMatrixEvaluation (a : ℝ) (K : Set KPCplxCharacterHaar.ComplexGL2)
    (hK : IsCompact K) : PrincipalSeries a →ₗ[ℂ] C(K, ℂ) where
  toFun f := ⟨fun k => f k.val,
    ((principalSeries_matrix_evaluation_joint a).comp
      (continuous_const.prodMk continuous_subtype_val))⟩
  map_add' := by intros; ext k; rfl
  map_smul' := by intros; ext k; rfl

theorem compactMatrixEvaluation_continuous (a : ℝ)
    (K : Set KPCplxCharacterHaar.ComplexGL2) (hK : IsCompact K) :
    Continuous (compactMatrixEvaluation a K hK) := by
  exact ContinuousMap.continuous_of_continuous_uncurry _
    ((principalSeries_matrix_evaluation_joint a).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

end DedekindZetaZeroFree.KPActualReflectionData.LiteralProductPointBound

end
