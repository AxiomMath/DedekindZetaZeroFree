module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorWords.MatrixWords
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.DifferentialWordInterchange

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPContActualSphericalRightFieldIdentification KPMsClearedTruncationL2.NativeWordBridge
open KPSmoothActualFlowData
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
def matrixLetter (b : Fin (groupDimension F)) : MatrixLetter (InfinitePlace F) :=
  ((wordIndexEquiv F b).1,KPSmoothActualFlowData.basisMatrix (wordIndexEquiv F b).2)

theorem finite_section_commute (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (a : InfinitePlace F → ComplexGL2) :
    Commute (archimedeanInsertion F ζ hζ (fun w => Matrix.ProjGenLinGroup.mk (a w))) c.val := by
  obtain ⟨r,hr,he⟩ := c.property
  rw [←he,←sectionTuple_insertion]
  have hc : Commute (sectionTuple F ζ hζ a) r := by
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w =>
      have hw : r (.inl w)=1 := (Subgroup.mem_iInf.mp hr) w
      change _ * r (.inl w) = r (.inl w) * _
      rw [hw,mul_one,one_mul]
    | inr q => change 1*r (.inr q)=r (.inr q)*1; simp
  exact hc.map ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ))

theorem flow_matrix_update (b : B F) (t : ℝ) :
    flow F b t = fun w => Matrix.ProjGenLinGroup.mk
      (Function.update (fun _ => (1 : ComplexGL2)) b.1
        (matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b.2)) w) := by
  funext v
  by_cases hv : v=b.1
  · subst v
    simp only [flow,exponential,Function.update_self]
    congr 2
    rcases b with ⟨v,j⟩
    fin_cases j <;> ext r c <;> fin_cases r <;> fin_cases c <;>
      simp [sl2Matrix,KPSmoothActualFlowData.basisMatrix,Matrix.smul_apply,smul_eq_mul,mul_comm]
  · rw [Function.update_of_ne hv]
    change Matrix.ProjGenLinGroup.mk (matrixExponential _) = Matrix.ProjGenLinGroup.mk 1
    congr 1
    have he : sl2Matrix (fun j => if (v,j)=b then t else 0)=0 := by
      ext r c
      fin_cases r <;> fin_cases c <;> simp [sl2Matrix,Prod.ext_iff,hv]
    rw [he]
    apply Units.ext
    exact NormedSpace.exp_zero
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
