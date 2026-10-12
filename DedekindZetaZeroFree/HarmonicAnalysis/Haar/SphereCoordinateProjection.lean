module

public import DedekindZetaZeroFree.MeasureTheory.Sphere.HeightDistribution

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.KernelMass
open MeasureTheory Set
open scoped ENNReal Pointwise

theorem normalized_area_coordinate_projection :
    Measure.map
      (fun y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =>
        (1 - (y : EuclideanSpace ℝ (Fin 3)) 0) / 2)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      (volume : Measure ℝ).restrict (Icc 0 1) := by
  exact RawSphereProjection.normalized_coordinate_projection

end DedekindZetaZeroFree.ComplexFractionalInverse.KernelMass
