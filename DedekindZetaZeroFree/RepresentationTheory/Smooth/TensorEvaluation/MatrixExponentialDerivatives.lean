module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandraHeckeLieCovariance
public import DedekindZetaZeroFree.Metaplectic.Induction.LocalSectionProductEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3200000
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources KPCplxCharacterHaar
open KPAdelicCoverRestrictedProduct
open KPContActualSphericalRightFieldIdentification
open KPActualReflectionData.LiteralProductEvaluator
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def rawBasisExponential (w : InfinitePlace F) (b : Fin 6) (t : ℝ) :
    KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (.inl w) :=
  KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (.inl w)
    (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm.toRingHom
      (KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b)))

theorem rawBasisExponential_matrix (w : InfinitePlace F) (b : Fin 6) (t : ℝ) :
    complexMatrix R.A w (rawBasisExponential R w b t) =
      KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b) := by
  apply Units.ext
  ext i j
  simp [complexMatrix, rawBasisExponential, KPLocalCover.sectionMap,
    Matrix.GeneralLinearGroup.map]

theorem rawBasisExponential_local (w : InfinitePlace F) (b : Fin 6) (t : ℝ)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (.inl w)) :
    (g * rawBasisExponential R w b t).epsilon = g.epsilon ∧
    complexMatrix R.A w (g * rawBasisExponential R w b t) =
      complexMatrix R.A w g * KPSmoothActualFlowData.matrixExponential
        ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b) := by
  constructor
  · change g.epsilon * 1 * KPLocalCover.sigmaTwo F R.A.zeta12
      R.A.primitive_zeta12 (.inl w) _ _ = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one, mul_one]
  · unfold complexMatrix
    change Matrix.GeneralLinearGroup.map _ (g.g * (rawBasisExponential R w b t).g) = _
    rw [map_mul]
    exact congrArg (_ * ·) (rawBasisExponential_matrix R w b t)

theorem rawBasisExponential_flow (w : InfinitePlace F) (b : Fin 6) (t : ℝ) :
    KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
      (KPSmoothActualFlowData.flow F (w, b) t) =
    scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (localInjection F R.A.zeta12 R.A.primitive_zeta12 (.inl w)
        (rawBasisExponential R w b t)) := by
  have hM (v : InfinitePlace F) :
      KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = (w,b) then t else 0) =
        if v = w then (t : ℂ) • KPSmoothActualFlowData.basisMatrix b else 0 := by
    by_cases hv : v = w
    · subst v
      rw [if_pos rfl]
      ext i k
      fin_cases i <;> fin_cases k <;>
        simp [KPSmoothActualFlowData.sl2Matrix, KPSmoothActualFlowData.basisMatrix,
          Matrix.smul_apply] <;> split_ifs <;> simp <;> ring
    · have hj (j : Fin 6) : (v,j) ≠ (w,b) := fun h => hv (congrArg Prod.fst h)
      simp only [if_neg hv, hj, if_false, KPSmoothActualFlowData.sl2Matrix]
      ext i k
      fin_cases i <;> fin_cases k <;> simp
  change KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
    (fun v => Matrix.ProjGenLinGroup.mk (KPSmoothActualFlowData.matrixExponential
      (KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = (w,b) then t else 0)))) = _
  rw [(KPSmoothActualFlowData.archimedean_insertion_properties F R.A.zeta12
    R.A.primitive_zeta12).2.2.2.2]
  rw [List.prod_map_eq_pow_single w]
  · rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
    have hw : KPSmoothActualFlowData.sl2Matrix (fun j => if j = b then t else 0) =
        (t : ℂ) • KPSmoothActualFlowData.basisMatrix b := by
      simpa using hM w
    simp [rawBasisExponential, hw]
  · intro v hv
    have hz : KPSmoothActualFlowData.matrixExponential (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      apply Units.ext
      exact NormedSpace.exp_zero
    simp only [hM, if_neg hv, hz, map_one]
    have hs : KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (.inl v) 1 = 1 := rfl
    rw [hs, map_one, map_one]
    simp

theorem rawBasisExponential_actual_path (i : Fin (groupDimension F)) (t : ℝ) :
    KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12
      (KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single (lieEnumeration F i) 1)) =
    scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (localInjection F R.A.zeta12 R.A.primitive_zeta12
        (.inl (actualLieIndexEquiv (F := F) i).1)
        (rawBasisExponential R (actualLieIndexEquiv (F := F) i).1
          (actualLieIndexEquiv (F := F) i).2 t)) := by
  rw [KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actual_frame_ray_eq_flow]
  exact rawBasisExponential_flow R _ _ t

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
