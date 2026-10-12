module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.MovingCompactCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalChamberSpatialInsertion

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
 theorem basis_jet_norm_bound (n : ℕ) {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ E) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ L : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ,
      ‖L‖ ≤ A * ∑ t : Fin n → ι, ‖L (fun i => b (t i))‖ := by
  let ev : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ →ₗ[ℝ]
      ((Fin n → ι) → ℂ) :=
    { toFun := fun L t => L (fun i => b (t i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective ev := by
    intro L M h
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply Basis.ext_multilinear (fun _ : Fin n => b)
    intro t
    exact congrFun h t
  let : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
    FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  let ec := ev.toContinuousLinearMap
  have hc := ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hi)
  obtain ⟨A, hA⟩ := ec.antilipschitz_of_isEmbedding hc.isEmbedding
  refine ⟨A, A.coe_nonneg, fun L => ?_⟩
  calc
    ‖L‖ ≤ A * ‖ec L‖ := ec.bound_of_antilipschitz hA L
    _ ≤ A * ∑ t : Fin n → ι, ‖L (fun i => b (t i))‖ := by
      apply mul_le_mul_of_nonneg_left _ A.coe_nonneg
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
      intro t
      exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ t)

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPLiteralChamber
section PartialJet
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup H] [NormedSpace ℝ H]
open Filter Set

end PartialJet

open Filter Set
section LocalSeries
open Filter Set
variable {α E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {f : α → E → H} {v : ℕ → α → ℝ} {U : Set E}

end LocalSeries

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalChamberSpatialInsertion

end
