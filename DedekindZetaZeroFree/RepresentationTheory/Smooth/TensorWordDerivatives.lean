module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryOperatorWords
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Residual.FiniteSliceRightDerivatives

@[expose] public section

noncomputable section
open scoped Classical Topology BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction NativeComplexHCOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem pure_flow_hasDerivAt (s : ℝ) (h : ι → PrincipalSeries s)
    (a : ι → ComplexGL2) (b : MatrixLetter ι) :
    HasDerivAt (fun t : ℝ => ∏j, h j (Function.update a b.1
      (a b.1 * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • b.2)) j))
      ((∏j ∈ Finset.univ.erase b.1, h j (a j)) * derivative s b.2 (h b.1) (a b.1)) 0 := by
  have hp (g : ComplexGL2) : (∏j, h j (Function.update a b.1 g j)) =
      (∏j ∈ Finset.univ.erase b.1, h j (a j)) * h b.1 g := by
    rw [←Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b.1),mul_comm]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  simp_rw [hp]
  exact (hasDerivAt_flow s b.2 (h b.1) (a b.1)).const_mul _

theorem tupleWord_sum_pure (s : ℝ) (w : List (MatrixLetter ι))
    {κ : Type} [Fintype κ] (c : κ → ℂ) (f : κ → ι → PrincipalSeries s)
    (a : ι → ComplexGL2) :
    tupleWord w (fun a => ∑j, c j * ∏i, f j i (a i)) a =
      ∑j, c j * ∏i, CurrentComplexBoundary.matrixWord s (slotWords i w) (f j i) (a i) := by
  induction w generalizing a with
  | nil => rfl
  | cons b w hw =>
    let h : κ → ι → PrincipalSeries s := fun j i =>
      CurrentComplexBoundary.matrixWord s (slotWords i w) (f j i)
    change deriv (fun t : ℝ => tupleWord w _ _) 0 = _
    simp_rw [hw]
    have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (pure_flow_hasDerivAt s (h j) a b).const_mul (c j))
    rw [hd.deriv]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [←Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b.1),mul_comm]
    congr 1
    · simp only [slotWords,ite_true,CurrentComplexBoundary.matrixWord]
      rfl
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [slotWords,if_neg (Ne.symm (Finset.mem_erase.mp hi).1)]
      rfl
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
