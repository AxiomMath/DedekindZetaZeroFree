module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.NativeLieWordReindexing
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RightInvariantFieldCoordinates

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Classical NumberField Manifold ContDiff
namespace DedekindZetaZeroFree.KPSpatialExponentialPullback
open KPContActualSphericalRightFieldIdentification KPContSectorCoveredQuotientVocabulary
open LocalQuotientCharts.ExponentialHaarFrame
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

set_option backward.isDefEq.respectTransparency false in

theorem group_chart_fields_basis (D : GroupChart F ζ hζ U R P H)
    (x : KPContLocalNorm.Space (groupDimension F)) (hx : x ∈ D.T.carrier) :
    ∃ e : Module.Basis (Fin (groupDimension F)) ℝ (KPContLocalNorm.Space (groupDimension F)),
      ∀ i, e i = D.fields i x := by
  letI := actualLieChartedSpace F
  letI := actualLieGroup F
  obtain ⟨E, he, hi⟩ := D.inverse_smooth
  have hE : ContMDiffOn (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) E E.source := by
    apply ((contMDiff_const (c := D.groupCenter)).mul
      (actualLieData F).exponential_smooth).contMDiffOn.congr
    intro a ha
    have hh := D.exponential.exponential_formula a (he ▸ ha)
    rw [← he] at hh
    exact hh.trans (congrArg (D.groupCenter * ·) (congrFun (actualLieData_exponential F) a)).symm
  let Φ : PartialDiffeomorph (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (KPSmoothLocalQuotientCharts.Coordinates F) (KPSmoothLocalQuotientCharts.ArchGroup F)
      (⊤ : ℕ∞) :=
    { toPartialEquiv := E.toPartialEquiv
      open_source := E.open_source
      open_target := E.open_target
      contMDiffOn_toFun := hE
      contMDiffOn_invFun := hi }
  have hxs : groupCoordinates F x ∈ E.source := by
    rw [he]
    exact D.closure_source ⟨x, subset_closure hx, rfl⟩
  let left (g : KPSmoothLocalQuotientCharts.ArchGroup F) :
      Diffeomorph (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
        (KPSmoothLocalQuotientCharts.ArchGroup F) (KPSmoothLocalQuotientCharts.ArchGroup F)
        (⊤ : ℕ∞) :=
    { toEquiv := Equiv.mulLeft g
      contMDiff_toFun := contMDiff_const.mul contMDiff_id
      contMDiff_invFun := contMDiff_const.mul contMDiff_id }
  let f : KPSmoothLocalQuotientCharts.Coordinates F → KPSmoothLocalQuotientCharts.Coordinates F :=
    fun y => E.symm (E (groupCoordinates F x) * (actualLieData F).exponential y)
  have hd0 : IsLocalDiffeomorphAt (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
      (actualLieData F).exponential 0 :=
    ⟨(actualLieData F).exponentialChart, (actualLieData F).zero_mem_source,
      fun y hy => ((actualLieData F).chart_eq_exponential y hy).symm⟩
  have hd1 := (left (E (groupCoordinates F x))).isLocalDiffeomorph
    ((actualLieData F).exponential 0)
  have hd2 : IsLocalDiffeomorphAt (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞)
      E.symm (E (groupCoordinates F x) * (actualLieData F).exponential 0) := by
    rw [(actualLieData F).exponential_zero, mul_one]
    exact ⟨Φ.symm, E.map_source hxs, fun y hy => rfl⟩
  have hd : IsLocalDiffeomorphAt (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) (⊤ : ℕ∞) f 0 :=
    (hd0.comp (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) _ hd1).comp
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) _ hd2
  let A := hd.mfderivToContinuousLinearEquiv (by simp)
  let b := ((actualLieData F).basis.map A.toLinearEquiv).reindex (lieEnumeration F).symm
  refine ⟨b.map (groupCoordinates F).symm.toLinearEquiv, ?_⟩
  intro i
  have hd' : HasFDerivAt f (fderiv ℝ f 0) 0 :=
    (hd.contMDiffAt.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hr : HasDerivAt (fun t : ℝ => t • (actualLieData F).basis (lieEnumeration F i))
      ((actualLieData F).basis (lieEnumeration F i)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((actualLieData F).basis (lieEnumeration F i))
  have hd'' : HasFDerivAt f (fderiv ℝ f 0)
      ((0 : ℝ) • (actualLieData F).basis (lieEnumeration F i)) := by simpa using hd'
  have hA : A ((actualLieData F).basis (lieEnumeration F i)) =
      deriv (fun t : ℝ => f (t • (actualLieData F).basis (lieEnumeration F i))) 0 := by
    change mfderiv (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F))
      (𝓘(ℝ, KPSmoothLocalQuotientCharts.Coordinates F)) f 0 _ = _
    rw [mfderiv_eq_fderiv]
    exact (hd''.comp_hasDerivAt 0 hr).deriv.symm
  simp only [Module.Basis.map_apply, Module.Basis.reindex_apply, b, Equiv.symm_symm]
  change (groupCoordinates F).symm (A ((actualLieData F).basis (lieEnumeration F i))) = _
  rw [hA]
  simp only [f, actualLieData_exponential, actualLieData_basis, GroupChart.fields,
    KPSmoothLocalQuotientCharts.rightLieField, ← he]
  rfl

end DedekindZetaZeroFree.KPSpatialExponentialPullback

end
