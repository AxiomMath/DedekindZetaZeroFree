module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightInvariantDifferentialWords
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.NativeLieWordReindexing
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.UpperRootLieDerivatives

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Operator
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

 theorem exp_upper (z : ℂ) :
    NormedSpace.exp (!![(0 : ℂ),z;0,0]) = !![1,z;0,1] := by
  have hs : (!![(0 : ℂ),z;0,0]) ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two,Matrix.mul_apply,Fin.sum_univ_two]
  rw [NormedSpace.exp_eq_tsum ℚ]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range 2) (fun n hn => by
    have hn' : 2 ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
    rw [pow_eq_zero_of_le hn' hs,smul_zero])]
  simp [Finset.sum_range_succ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

 def upperIndex (w : InfinitePlace F) (b : Bool) : Fin (groupDimension F) :=
    (lieEnumeration F).symm (w,1,if b then 1 else 0)

 theorem upper_native_curve (w : InfinitePlace F) (b : Bool) (t : ℝ) :
    upperCurve R w b t = KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
      (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F (upperIndex w b)) 1)) := by
  rw [← upperCoordinates_chart, KPLiteralChamber.right_insertion]
  congr 1
  funext v
  unfold KPSmoothLocalQuotientCharts.matrixExp
  congr 1
  apply Units.ext
  simp only [IsUnit.unit_spec]
  have hm : KPSmoothLocalQuotientCharts.lieMatrix F
      (t • Pi.single (lieEnumeration F (upperIndex w b)) 1) v =
      !![(0 : ℂ), if v = w then (t : ℂ) * direction b else 0;0,0] := by
    ext i j
    cases b <;> fin_cases i <;> fin_cases j <;>
      simp [KPSmoothLocalQuotientCharts.lieMatrix,upperIndex,Pi.single_apply,
        direction,eq_comm, Complex.ext_iff] <;> split_ifs <;> simp_all
  rw [hm, exp_upper]
  rw [KPLiteralChamber.rightMatrix_val _ (by simp [upperCoordinates])]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperCoordinates]

 theorem upperLieDerivative_actualRight (w : InfinitePlace F) (b : Bool) (f : MomentSources.Functions R) :
    MomentSources.upperLieDerivative R w b f = actualRight F R.A.zeta12 R.A.primitive_zeta12 (upperIndex w b) f := by
  funext g
  change deriv (fun t => f (g * upperCurve R w b t)) 0 = _
  simp_rw [upper_native_curve]
  rfl

end DedekindZetaZeroFree.RootDerivatives

end
