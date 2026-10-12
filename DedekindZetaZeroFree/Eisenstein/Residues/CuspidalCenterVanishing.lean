module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspidalOrthogonality.CentralAveraging
public import DedekindZetaZeroFree.Eisenstein.Continuation.Resolvent.CutoffAndClearedGerms

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CommonSphericalDisk.CuspidalCancellation

open MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions

private theorem projection_center_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) (hQQ : Q * Q = Q)
    (h z : E) (a : ℂ) (hz : z = a • Q h)
    (hpair : inner ℂ z h = 0) : z = 0 := by
  have hQz : Q z = z := by
    rw [hz, map_smul]
    have hp := congrArg (fun A : E →L[ℂ] E => A h) hQQ
    simpa only [mul_apply_eq_comp] using congrArg (fun x : E => a • x) hp
  have h' : inner ℂ z (Q h) = 0 := by
    have hsym : inner ℂ (Q z) h = inner ℂ z (Q h) := hQ.isSymmetric z h
    rw [hQz, hpair] at hsym
    exact hsym.symm
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  calc
    inner ℂ z z = inner ℂ z (a • Q h) := congrArg (inner ℂ z) hz
    _ = a * inner ℂ z (Q h) := inner_smul_right _ _ _
    _ = 0 := by rw [h', mul_zero]

 theorem cleared_center_unique {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v w w' : ℂ → E) (c : ℂ) (r r' : ℝ)
    (hr : 0 < r) (hr' : 0 < r')
    (hw : DifferentiableOn ℂ w (Metric.ball c r))
    (hw' : DifferentiableOn ℂ w' (Metric.ball c r'))
    (he : ∀ s ∈ Metric.ball c r, s ≠ c → w s = (s - c) • v s)
    (he' : ∀ s ∈ Metric.ball c r', s ≠ c → w' s = (s - c) • v s) :
    w c = w' c := by
  have hwc := hw.continuousOn.continuousAt (Metric.ball_mem_nhds c hr)
  have hwc' := hw'.continuousOn.continuousAt (Metric.ball_mem_nhds c hr')
  have heq : w =ᶠ[𝓝[≠] c] w' := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c hr),
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c hr'),
      self_mem_nhdsWithin] with s hs hs' hne
    exact (he s hs (by simpa using hne)).trans (he' s hs' (by simpa using hne)).symm
  exact ((hwc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hwc').mp heq).eq_of_nhds

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

include realization hι hf buffer

theorem smooth_center_eq_zero
    (V : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
    (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain)
    (r : ℝ) (hr : 0 < r) (hb : Metric.ball c r ⊆ KPContinuation.spectralDomain)
    (hi : Metric.ball c r ∩ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U
      R.adelicHaar R.adelic_isHaar rfl realization KPContinuation.spectralDomain ⊆ {c})
    (w : ℂ → KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (hw : DifferentiableOn ℂ w (Metric.ball c r))
    (he : ∀ s ∈ Metric.ball c r, s ≠ c → w s = (s - c) •
      KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U
        R.adelicHaar R.adelic_isHaar rfl realization ι buffer
        KPContinuation.spectralDomain f χ source s)
    (N : KPContActualCutoffPlusClearedGerm.ClearedNumerator F ζ hζ C R P H U
      R.adelicHaar R.adelic_isHaar rfl ι KPContinuation.spectralDomain f χ
      realization buffer source V c r w)
    (hmean : IncomingFiberOrthogonality.AllCuspMeanZero F ζ hζ C R P H U (N.W c)) :
    N.W c = 0 := by
  let v := KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U
    R.adelicHaar R.adelic_isHaar rfl realization ι buffer
    KPContinuation.spectralDomain f χ source
  let a := KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)
  let B := KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ
    (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
    R.adelicHaar R.adelic_isHaar rfl realization
  have hg := kp_cont_actual_hilbert_simple_germs F ζ hζ C R P H U
    R.adelicHaar R.adelic_isHaar rfl realization ι hι
    (stageConclusions F ζ hζ C R P H U ι hι)
    KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen
    (fun _ hs => hs) f hf buffer χ source
  obtain ⟨r', hr', hb', hi', w', hw', he', hcenter', houtside'⟩ := hg.simple_germs c hc
  have hcentereq : w c = w' c :=
    cleared_center_unique v w w' c r r' hr hr' hw hw' he he'
  have hrep := N.represents c (Metric.mem_ball_self hr)
  have hae : ((w c).val : KPContActualAllCuspSource.Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[KPContActualAllCuspSource.measure F ζ hζ C R P H U]
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (N.W c) := by
    obtain ⟨hm, heq⟩ := hrep
    have hs : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (N.W c).val).val =
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (N.W c) := by
      rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
      rfl
    rw [← hs, ← heq]
    exact hm.coeFn_toLp
  have hpair : inner ℂ (w c) (source.h c) = 0 :=
    SourceCuspidalOrthogonality.source_inner_eq_zero F ζ hζ C R P H U
      ι buffer KPContinuation.spectralDomain f χ source (N.W c) (w c) hae hmean c hc
  have hzero : w c = 0 := by
    by_cases hp : c ∈ KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U
        R.adelicHaar R.adelic_isHaar rfl realization KPContinuation.spectralDomain
    · obtain ⟨μ, hμ, heig, hcoord⟩ := hp.2
      let Q := KPBelowThresholdResolvent.poleProjection B μ
      have hQ : IsSelfAdjoint Q :=
        isSelfAdjoint_starProjection (KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹))
      have hQQ : Q * Q = Q := by
        apply ContinuousLinearMap.ext
        intro x
        change (KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹)).starProjection
          ((KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹)).starProjection x) = _
        exact Submodule.starProjection_eq_self_iff.mpr
          (Submodule.starProjection_apply_mem _ _)
      exact projection_center_zero Q hQ hQQ (source.h c) (w c) ((deriv a c)⁻¹)
        (hcentereq.trans (hcenter' hp μ hcoord)) hpair
    · exact hcentereq.trans (houtside' hp)
  have hzrep : KPContActualSmoothLineGluing.Represents F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
      (0 : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U).val (w c) := by
    rw [hzero]
    have hs : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
        (0 : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U).val).val = 0 := by
      rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
      change ((KPContSectorScalarLineAlgebra.S F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm 0).val = 0
      exact congrArg Subtype.val (LinearEquiv.map_zero
        (KPContSectorScalarLineAlgebra.S F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm)
    refine ⟨hs ▸ (MemLp.zero : MemLp
      (0 : KPContActualAllCuspSource.Covered F ζ hζ C R P H U → ℂ)
      2 (KPContActualAllCuspSource.measure F ζ hζ C R P H U)), ?_⟩
    simp only [hs, MemLp.toLp_zero]
    rfl
  exact (N.unique c (Metric.mem_ball_self hr) 0 hzrep).symm

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CommonSphericalDisk.CuspidalCancellation

end
