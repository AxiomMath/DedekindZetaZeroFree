module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactDerivatives.SumPairing
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorWords.SlotCombinatorics

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical BigOperators Topology
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts CurrentComplexBoundary
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming evaluation_point_eval_continuous → evaluation_point_eval_continuous
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : CompactSpace compactSubgroup := isCompact_iff_compactSpace.mp compactSubgroup_isCompact
local instance : SecondCountableTopology compactSubgroup := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : SecondCountableTopology ComplexGL2 := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology ComplexPGL2 :=
    inferInstanceAs (SecondCountableTopology (ComplexGL2 ⧸ Subgroup.center _))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

def pureCompact (s : ℝ) (f : ι → PrincipalSeries s) (k : ι → compactSubgroup) : ℂ :=
  ∏i, (KPCplxPrincipalSeriesCharts.pi s (k i).val (f i)) 1

theorem pureCompact_continuous (s : ℝ) (f : ι → PrincipalSeries s) :
    Continuous (pureCompact s f) := by
  apply continuous_finset_prod
  intro i hi
  exact (evaluation_point_eval_continuous s 1).comp
    ((KPCplxPrincipalSeriesCharts.pi_continuous s).comp (((continuous_subtype_val.comp (continuous_apply i))).prodMk continuous_const))

theorem pureCompact_pair (μ : Measure (ι → compactSubgroup)) (s : ℝ)
    (f : ι → PrincipalSeries s) (g : ι → PrincipalSeries (-s)) :
    (∫k,pureCompact s f k*star (pureCompact (-s) g k) ∂μ) = productBoundary μ (fun _=>s) f g := by
  unfold pureCompact productBoundary
  simp only [star_prod,←Finset.prod_mul_distrib]

theorem finiteCompact_word_adjoint
    (ρ : Measure ComplexSU2) [IsProbabilityMeasure ρ] [ρ.IsHaarMeasure]
    (μ : Measure (ι → compactSubgroup)) [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (ν : ι → Measure compactSubgroup) [∀i,IsProbabilityMeasure (ν i)] [∀i,(ν i).IsHaarMeasure]
    (s : ℝ) (w : List (MatrixLetter ι))
    {κ κ₂ : Type} [Fintype κ] [Fintype κ₂]
    (c : κ → ℂ) (d : κ₂ → ℂ)
    (f : κ → ι → PrincipalSeries s) (g : κ₂ → ι → PrincipalSeries (-s)) :
    (∫k,(∑j,c j*pureCompact s (fun i=>matrixWord s (slotWords i w) (f j i)) k)*
      star (∑j,d j*pureCompact (-s) (g j) k) ∂μ) =
    (-1 : ℂ)^w.length * (∫k,(∑j,c j*pureCompact s (f j) k)*
      star (∑j,d j*pureCompact (-s) (fun i=>matrixWord (-s) (slotWords i w.reverse) (g j i)) k) ∂μ) := by
  rw [compact_pairing_sum μ c d _ _ (fun j=>pureCompact_continuous _ _) (fun j=>pureCompact_continuous _ _)]
  rw [compact_pairing_sum μ c d _ _ (fun j=>pureCompact_continuous _ _) (fun j=>pureCompact_continuous _ _)]
  simp_rw [pureCompact_pair]
  simp_rw [productBoundary_word_adjoint ρ μ ν,slotWords_lengths,←slotWords_reverse]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
