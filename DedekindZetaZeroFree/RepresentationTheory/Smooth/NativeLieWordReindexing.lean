module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows
public import DedekindZetaZeroFree.Adeles.Quotients.SmoothLocalCharts

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
open scoped NumberField Classical Matrix.Norms.Operator
variable (F : Type) [Field F] [NumberField F]

def actualBasisReindex : (NumberField.InfinitePlace F × Fin 3 × Fin 2) ≃
    KPSmoothActualFlowData.B F :=
  Equiv.prodCongr (Equiv.refl _) finProdFinEquiv

private theorem reindex_apply (x : KPSmoothLocalQuotientCharts.Coordinates F)
    (w : NumberField.InfinitePlace F) (i : Fin 3) (j : Fin 2) :
    LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F x
      (w, finProdFinEquiv (i, j)) = x (w, i, j) := by
  change (Equiv.piCongrLeft (fun _ => ℝ)
    (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv)) x
      ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv) (w, i, j)) = _
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

theorem actual_exponential_coordinate_reindex
    (x : KPSmoothLocalQuotientCharts.Coordinates F) :
    KPSmoothActualFlowData.exponential F
      (LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F x) =
      KPSmoothLocalQuotientCharts.matrixExp F x := by
  funext w
  have hM : KPSmoothActualFlowData.sl2Matrix
      (fun j => LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F x (w, j)) =
      KPSmoothLocalQuotientCharts.lieMatrix F x w := by
    have h00 := reindex_apply F x w 0 0
    have h01 := reindex_apply F x w 0 1
    have h10 := reindex_apply F x w 1 0
    have h11 := reindex_apply F x w 1 1
    have h20 := reindex_apply F x w 2 0
    have h21 := reindex_apply F x w 2 1
    norm_num [finProdFinEquiv] at h00 h01 h10 h11 h20 h21
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPSmoothActualFlowData.sl2Matrix, KPSmoothLocalQuotientCharts.lieMatrix,
        h00, h01, h10, h11, h20, h21, Complex.ext_iff, mul_comm]
  simp only [KPSmoothActualFlowData.exponential, KPSmoothActualFlowData.matrixExponential,
    KPSmoothLocalQuotientCharts.matrixExp, hM]

theorem actual_frame_ray_eq_flow
    (b : NumberField.InfinitePlace F × Fin 3 × Fin 2) (t : ℝ) :
    KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single b 1) =
      KPSmoothActualFlowData.flow F (actualBasisReindex F b) t := by
  rw [← actual_exponential_coordinate_reindex]
  congr 1
  funext c
  obtain ⟨c, rfl⟩ := (actualBasisReindex F).surjective c
  have hr := reindex_apply F (t • Pi.single b 1) c.1 c.2.1 c.2.2
  change LocalQuotientCharts.ExponentialHaarFrame.coordinateReindex F
    (t • Pi.single b 1) (actualBasisReindex F c) = _ at hr
  rw [hr]
  change (t • Pi.single b 1) c = if actualBasisReindex F c = actualBasisReindex F b then t else 0
  simp [Pi.single_apply, Equiv.apply_eq_iff_eq, eq_comm]

end DedekindZetaZeroFree.KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource

end
