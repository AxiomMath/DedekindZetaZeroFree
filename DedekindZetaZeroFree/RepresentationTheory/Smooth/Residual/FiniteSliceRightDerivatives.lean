module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Residual.MatrixDifferentialWords

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge KPSmoothActualFlowData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
def finiteSlicePoint (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (a : InfinitePlace F → ComplexGL2) : G F ζ hζ :=
  archimedeanInsertion F ζ hζ (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val

theorem finiteSlicePoint_flow (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (a : InfinitePlace F → ComplexGL2) (b : B F) (t : ℝ) :
    finiteSlicePoint F ζ hζ c a * archimedeanInsertion F ζ hζ (flow F b t) =
      finiteSlicePoint F ζ hζ c (Function.update a b.1
        (a b.1 * matrixExponential ((t : ℂ) • basisMatrix b.2))) := by
  let d : InfinitePlace F → ComplexGL2 := Function.update (fun _ => 1) b.1
    (matrixExponential ((t : ℂ) • basisMatrix b.2))
  have hf : flow F b t = fun w => Matrix.ProjGenLinGroup.mk (d w) := flow_matrix_update F b t
  have hc := finite_section_commute F ζ hζ c d
  rw [finiteSlicePoint,hf,mul_assoc,←hc.eq,←mul_assoc]
  rw [←(archimedean_insertion_properties F ζ hζ).2.1]
  congr 1
  apply congrArg (archimedeanInsertion F ζ hζ)
  funext v
  by_cases hv : v=b.1
  · subst v
    simp only [d,Function.update_self,Pi.mul_apply]
    rfl
  · simp only [d,Function.update_of_ne hv,Pi.mul_apply]
    change Matrix.ProjGenLinGroup.mk (a v) * Matrix.ProjGenLinGroup.mk 1 = _
    simp

theorem actualRightWord_finiteSlice (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (f : G F ζ hζ → ℂ) (w : List (Fin (groupDimension F)))
    (a : InfinitePlace F → ComplexGL2) :
    actualRightWord F ζ hζ w f (finiteSlicePoint F ζ hζ c a) =
      tupleWord (w.map (matrixLetter F)) (fun a => f (finiteSlicePoint F ζ hζ c a)) a := by
  induction w generalizing a with
  | nil => rfl
  | cons b w hw =>
    change deriv (fun t : ℝ => actualRightWord F ζ hζ w f
      (finiteSlicePoint F ζ hζ c a * archimedeanInsertion F ζ hζ
        (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F b) 1)))) 0 = _
    simp only [matrixExp_eq_flow]
    change deriv (fun t : ℝ => actualRightWord F ζ hζ w f
      (finiteSlicePoint F ζ hζ c a * archimedeanInsertion F ζ hζ
        (flow F (wordIndexEquiv F b) t))) 0 = _
    simp_rw [finiteSlicePoint_flow,hw]
    rfl
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
