module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGerms.JointNumeratorEvaluation
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.ChartL2Bounds
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.MatrixFlowDerivativeIdentification
public import DedekindZetaZeroFree.Analysis.Sobolev.InteriorPointEvaluation
public import DedekindZetaZeroFree.Analysis.LieGroups.RightWordSobolevBounds

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Classical NumberField ENNReal
namespace DedekindZetaZeroFree.FourierContinuation.ResidualOutputSobolev
open KPContActualSphericalRightFieldIdentification KPMsGreenFlux KPContLocalNorm
open KPContLocalCubeEmbedding KPMsClearedTruncationL2.NativeWordBridge
open KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
local notation "q" => KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
local notation "X" => KPSmoothLocalQuotientCharts.X F ζ hζ
def quotientWord (w : List (Fin (groupDimension F))) (f : X → ℂ) : X → ℂ :=
  KPSmoothActualFlowData.wordDerivative F ζ hζ (w.map (wordIndexEquiv F)) f

theorem quotientWord_lift (w : List (Fin (groupDimension F))) (f : X → ℂ)
    (g : Cover F ζ hζ) :
    quotientWord w f (q g) = actualRightWord F ζ hζ w (fun g => f (q g)) g :=
  (actualRightWord_eq_wordDerivative F ζ hζ w f g).symm

theorem quotientWord_level (f : X → ℂ)
    (hf : ∀ (v : U.toOpenSubgroup) (g : Cover F ζ hζ), f (q (g*v.val.val)) = f (q g))
    (w : List (Fin (groupDimension F))) :
    ∀ (v : U.toOpenSubgroup) (g : Cover F ζ hζ),
      quotientWord w f (q (g*v.val.val)) = quotientWord w f (q g) := by
  intro v g
  rw [quotientWord_lift,quotientWord_lift]
  exact ResidueContinuity.ScalarSourceJointContinuity.actual_word_right_level (fun g => f (q g))
    (fun g u => hf u g) w g v

theorem exists_original_ball_l2_bound
    (chart : GroupChart F ζ hζ U R P H) (A : LocalBall (groupDimension F))
    (hAT : closedCarrier A ⊆ chart.T.carrier) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : X → ℂ, MemLp f 2 R.quotientHaar →
      (∀ (v : U.toOpenSubgroup) (g : Cover F ζ hζ), f (q (g*v.val.val)) = f (q g)) →
      MemLp (fun x => f (q (chart.groupLift x))) 2 (volume.restrict A.carrier) ∧
      lpNorm (fun x => f (q (chart.groupLift x))) 2 (volume.restrict A.carrier) ≤
        C * lpNorm f 2 R.quotientHaar := by
  obtain ⟨C,hC,hb⟩ := exists_original_chart_l2_bound chart (closedCarrier A)
    (isCompact_closedBall _ _) hAT
  refine ⟨C,hC,?_⟩
  intro f hf hl
  obtain ⟨hLp,hn⟩ := hb f hf hl
  have hμ : volume.restrict A.carrier ≤ volume.restrict (closedCarrier A) :=
    Measure.restrict_mono Metric.ball_subset_closedBall le_rfl
  refine ⟨hLp.mono_measure hμ,?_⟩
  exact (ENNReal.toReal_mono hLp.eLpNorm_ne_top
    (eLpNorm_mono_measure (p := 2) _ hμ)).trans hn

theorem exists_original_compact_point_bound
    (chart : GroupChart F ζ hζ U R P H) (A : LocalBall (groupDimension F))
    (hAT : closedCarrier A ⊆ chart.T.carrier) :
    ∃ W : Finset (List (Fin (groupDimension F))),
      (∀ w ∈ W, w.length ≤ groupDimension F) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f : X → ℂ,
        ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (q (chart.groupLift x))) chart.T.carrier →
        (∀ (v : U.toOpenSubgroup) (g : Cover F ζ hζ), f (q (g*v.val.val)) = f (q g)) →
        (∀ w ∈ W, MemLp (quotientWord w f) 2 R.quotientHaar) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ w ∈ W, lpNorm (quotientWord w f) 2 R.quotientHaar ≤ M) →
          ∀ x ∈ closedCarrier A, ‖f (q (chart.groupLift x))‖ ≤ C*M := by
  obtain ⟨B,hBT,E,hE,hev⟩ := exists_outer_ball_sobolev_point_bound A chart.T hAT
  obtain ⟨W,hW,C,hC,hsob⟩ :=
    GroupChartSobolev.exists_actual_group_chart_word_sobolev_bound chart B hBT (groupDimension F)
  obtain ⟨D,hD,htube⟩ := exists_original_ball_l2_bound chart B hBT
  refine ⟨W,hW,E*C*D,by positivity,?_⟩
  intro f hs hl hp M hM hm
  have hlocal (w) (hw : w ∈ W) :=
    htube (quotientWord w f) (hp w hw) (quotientWord_level f hl w)
  have hLp (w) (hw : w ∈ W) :
      MemLp (fun x => actualRightWord F ζ hζ w (fun g => f (q g)) (chart.groupLift x))
        2 (volume.restrict B.carrier) := by
    simpa only [quotientWord_lift] using (hlocal w hw).1
  obtain ⟨u,hu,hn⟩ := hsob (fun g => f (q g)) hs hLp (D*M) (mul_nonneg hD.le hM) (by
    intro w hw
    rw [Lp.norm_toLp]
    have hb := (hlocal w hw).2.trans (mul_le_mul_of_nonneg_left (hm w hw) hD.le)
    simpa only [quotientWord_lift, lpNorm] using hb)
  intro x hx
  have hc : ContinuousOn (fun x => f (q (chart.groupLift x))) B.carrier :=
    hs.continuousOn.mono (fun y hy => hBT (Metric.ball_subset_closedBall hy))
  exact (hev _ hc u hu x hx).trans ((mul_le_mul_of_nonneg_left hn hE.le).trans_eq (by ring))

end DedekindZetaZeroFree.FourierContinuation.ResidualOutputSobolev

end
