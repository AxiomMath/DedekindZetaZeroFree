module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.ScalarRestrictionOperator

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorBallRestriction

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContSectorLineL2Isometry
open KPContActualSectorChartEquivariantInputs KPContLocalNorm
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap
open KPContActualSectorCoordinateNullEquivalence

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

abbrev BallInside (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F)) : Prop :=
  KPContActualSectorCoordinateNullEquivalence.BallInside a B

abbrev BallL2 {n : ℕ} (B : LocalBall n) := KPContLocalNorm.BallL2 B

theorem weight_positive_lower (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ closure B.carrier, c ≤ weight a x := by
  have hs : closure B.carrier ⊆ chart a := hB.2
  have hc : ContinuousOn (weight a) (closure B.carrier) :=
    (scalarData a).smooth_weight.continuousOn.mono hs
  have hn : (closure B.carrier).Nonempty :=
    ⟨B.center, subset_closure (Metric.mem_ball_self B.radius_pos)⟩
  obtain ⟨p, hp, hmin⟩ := hB.1.exists_isMinOn hn hc
  exact ⟨weight a p, (scalarData a).positive_weight p (hs hp), fun x hx => hmin hx⟩
theorem ball_measure_le_weighted (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) (c : ℝ) (hc : 0 < c)
    (hl : ∀ x ∈ closure B.carrier, c ≤ weight a x) :
    volume.restrict B.carrier ≤ (ENNReal.ofReal c)⁻¹ • measure a := by
  have hs : B.carrier ⊆ chart a := fun x hx => hB.2 (subset_closure hx)
  have hlow : ENNReal.ofReal c • volume.restrict B.carrier ≤ measure a := by
    rw [← withDensity_const]
    calc
      (volume.restrict B.carrier).withDensity (fun _ => ENNReal.ofReal c) ≤
          (volume.restrict B.carrier).withDensity (fun x => ENNReal.ofReal (weight a x)) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet)] with x hx
        exact ENNReal.ofReal_le_ofReal (hl x (subset_closure hx))
      _ ≤ measure a := by
        change (volume.restrict B.carrier).withDensity _ ≤
          (volume.restrict (chart a)).withDensity _
        apply Measure.le_iff.mpr
        intro E hE
        rw [withDensity_apply _ hE, withDensity_apply _ hE]
        exact lintegral_mono' (Measure.restrict_mono le_rfl (Measure.restrict_mono hs le_rfl)) le_rfl
  have hi : (ENNReal.ofReal c)⁻¹ • (ENNReal.ofReal c • volume.restrict B.carrier) ≤
      (ENNReal.ofReal c)⁻¹ • measure a := by gcongr
  simpa [smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top] using hi

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ENNReal}
def lpRestrictionOfMeasureLeSMul (hc : c ≠ ⊤) (h : μ ≤ c • ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ := by
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) hc h
  refine { toFun := L, map_add' := L.map_add, map_smul' := ?_, cont := L.continuous }
  intro z f
  apply Lp.ext
  have habs : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hc h (z • f),
    Lp.coeFn_LpToLpOfMeasureLeSMul hc h f,
    Lp.coeFn_smul z (L f), habs.ae_eq (Lp.coeFn_smul z f)] with x h1 h2 h3 h4
  change L (z • f) x = (z • L f) x
  change L f x = f x at h2
  change (z • L f) x = z • L f x at h3
  change (z • f) x = z • f x at h4
  rw [h1, h3, h2, h4]
theorem lpRestrictionOfMeasureLeSMul_ae (hc : c ≠ ⊤) (h : μ ≤ c • ν) (f : Lp ℂ 2 ν) :
    lpRestrictionOfMeasureLeSMul hc h f =ᵐ[μ] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hc h f

theorem ball_measure_domination (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : BallInside a B) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ volume.restrict B.carrier ≤ c • measure a := by
  obtain ⟨r, hr, hl⟩ := weight_positive_lower a B hB
  exact ⟨(ENNReal.ofReal r)⁻¹, ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne',
    ball_measure_le_weighted a B hB r hr hl⟩

def weightedBall (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) : Lp ℂ 2 (measure a) →L[ℂ] BallL2 B :=
  let h := ball_measure_domination a B hB
  lpRestrictionOfMeasureLeSMul h.choose_spec.1 h.choose_spec.2

theorem weightedBall_ae (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) (f : Lp ℂ 2 (measure a)) :
    weightedBall a B hB f =ᵐ[volume.restrict B.carrier] f :=
  lpRestrictionOfMeasureLeSMul_ae _ _ f

theorem ball_absolutelyContinuous_weighted (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : BallInside a B) :
    volume.restrict B.carrier ≪ measure a := by
  obtain ⟨c, _, hc⟩ := ball_measure_domination a B hB
  exact Measure.absolutelyContinuous_of_le_smul hc

theorem weightedBall_ae_of_ae (a : ActualChart (U := U) (H := H))
    (B : LocalBall (3 * d F)) (hB : BallInside a B)
    (f : Lp ℂ 2 (measure a)) (g : Space (3 * d F) → ℂ)
    (hfg : f =ᵐ[measure a] g) :
    weightedBall a B hB f =ᵐ[volume.restrict B.carrier] g :=
  (weightedBall_ae a B hB f).trans ((ball_absolutelyContinuous_weighted a B hB).ae_eq hfg)

def scalarProducer (a : ActualChart (U := U) (H := H)) :
    KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ] Lp ℂ 2 (measure a) :=
  (scalarProducer_exists a).choose

theorem scalarProducer_spec (a : ActualChart (U := U) (H := H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (s : BorelL2Sections F ζ hζ U R P H)
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s) :
    scalarProducer a u =ᵐ[measure a] fun x => scalar s a x :=
  (scalarProducer_exists a).choose_spec u s hs

def scalarBall (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) : KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ] BallL2 B :=
  (weightedBall a B hB).comp (scalarProducer a)

theorem scalarBall_ae (a : ActualChart (U := U) (H := H)) (B : LocalBall (3 * d F))
    (hB : BallInside a B) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (s : BorelL2Sections F ζ hζ U R P H)
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s) :
    (fun x => scalarBall a B hB u x) =ᵐ[volume.restrict B.carrier]
      (fun x => scalar s a x) := by
  rw [scalarBall, ContinuousLinearMap.comp_apply]
  exact weightedBall_ae_of_ae a B hB _ _ (scalarProducer_spec a u s hs)

end DedekindZetaZeroFree.KPContActualSectorBallRestriction

end
