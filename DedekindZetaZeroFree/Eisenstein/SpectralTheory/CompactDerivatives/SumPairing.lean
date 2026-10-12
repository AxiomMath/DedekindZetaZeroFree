module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ProductBoundary

@[expose] public section

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
set_option backward.isDefEq.respectTransparency false
variable {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
variable {κ κ₂ : Type*} [Fintype κ] [Fintype κ₂]
theorem compact_pairing_sum (μ : Measure α) [IsFiniteMeasure μ]
    (c : κ → ℂ) (d : κ₂ → ℂ) (f : κ → α → ℂ) (g : κ₂ → α → ℂ)
    (hf : ∀i,Continuous (f i)) (hg : ∀j,Continuous (g j)) :
    (∫x, (∑i,c i*f i x)*star (∑j,d j*g j x) ∂μ) =
      ∑i, ∑j, c i*star (d j)*(∫x,f i x*star (g j x) ∂μ) := by
  have hi (i : κ) (j : κ₂) : Integrable (fun x => c i*star (d j)*(f i x*star (g j x))) μ :=
    ((continuous_const.mul ((hf i).mul (hg j).star))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : α) : (∑i,c i*f i x)*star (∑j,d j*g j x) =
      ∑i,∑j,c i*star (d j)*(f i x*star (g j x)) := by
    simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hmem
    apply Finset.sum_congr rfl
    intro j hmemj
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i hmem
  rw [integral_finset_sum _ (fun j _ => hi i j)]
  simp only [integral_const_mul]
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
