module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.KernelMass
open MeasureTheory Set
open scoped RealInnerProductSpace Pointwise

theorem normalized_area_projection_rotation (n : ℕ) (i : Fin n)
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    Measure.map
      (fun y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) =>
        (1 - inner ℝ (x : EuclideanSpace ℝ (Fin n))
          (y : EuclideanSpace ℝ (Fin n))) / 2)
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)⁻¹ •
        (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) =
    Measure.map
      (fun y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) =>
        (1 - (y : EuclideanSpace ℝ (Fin n)) i) / 2)
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)⁻¹ •
        (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  classical
  let μ : Measure ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  let z : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨EuclideanSpace.single i (1 : ℝ), by
    simpa only [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩
  let g : (EuclideanSpace ℝ (Fin n)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin n)) := (ℝ ∙ ((z : (EuclideanSpace ℝ (Fin n))) - (x : (EuclideanSpace ℝ (Fin n)))))ᗮ.reflection
  have hg : g z = (x : (EuclideanSpace ℝ (Fin n))) := Submodule.reflection_sub (by
    rw [mem_sphere_zero_iff_norm.mp z.property,
      mem_sphere_zero_iff_norm.mp x.property])
  let R : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := g.toHomeomorph.subtype (fun y => by
    change ‖y - 0‖ = 1 ↔ ‖g y - 0‖ = 1
    simp only [sub_zero, g.norm_map])
  have hR : MeasurePreserving R μ μ := by
    refine ⟨R.measurable, Measure.ext fun s hs => ?_⟩
    rw [R.measurableEmbedding.map_apply,
      Measure.toSphere_apply' _ (R.measurable hs), Measure.toSphere_apply' _ hs]
    congr 1
    have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' (R ⁻¹' s)) =
        g ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
      ext w
      constructor
      · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨t, ht, g y, ⟨R y, hy, rfl⟩, by simp⟩
      · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, heq⟩
        refine ⟨t, ht, g.symm y, ⟨R.symm y, ?_, rfl⟩, ?_⟩
        · simpa using hy
        · have := congrArg g.symm heq
          simpa using this
    rw [hset]
    exact g.measurePreserving.measure_preimage_emb g.toHomeomorph.measurableEmbedding _
  have hRN := hR.smul_measure (μ Set.univ)⁻¹
  have hp : Measurable (fun y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) => (1 - inner ℝ (x : (EuclideanSpace ℝ (Fin n))) (y : (EuclideanSpace ℝ (Fin n)))) / 2) := by
    fun_prop
  change Measure.map (fun y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) => (1 - inner ℝ (x : (EuclideanSpace ℝ (Fin n))) (y : (EuclideanSpace ℝ (Fin n)))) / 2)
      ((μ Set.univ)⁻¹ • μ) =
    Measure.map (fun y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) => (1 - (y : (EuclideanSpace ℝ (Fin n))) i) / 2) ((μ Set.univ)⁻¹ • μ)
  conv_lhs => rw [← hRN.map_eq]
  rw [Measure.map_map hp R.measurable]
  congr 1
  ext y
  change (1 - inner ℝ (x : (EuclideanSpace ℝ (Fin n))) (g y)) / 2 = (1 - (y : (EuclideanSpace ℝ (Fin n))) i) / 2
  rw [← hg, g.inner_map_map]
  simp [z, EuclideanSpace.inner_single_left]

end DedekindZetaZeroFree.ComplexFractionalInverse.KernelMass
