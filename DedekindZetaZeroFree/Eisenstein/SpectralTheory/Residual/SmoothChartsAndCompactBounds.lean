module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DifferentialWords.KFiniteVectors
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.CompactPointwiseBounds
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteTranslationLieCommutation

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Classical NumberField ENNReal
namespace DedekindZetaZeroFree.FourierContinuation.ResidualOutputSobolev
open KPContActualSphericalRightFieldIdentification KPMsGreenFlux KPContLocalNorm
open KPContLocalCubeEmbedding KPGlobalResidualConstruction
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
open LocalQuotientCharts.ExponentialHaarFrame
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
local notation "q" => KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
local notation "X" => KPSmoothLocalQuotientCharts.X F ζ hζ
theorem smooth_group_chart (f : Cover F ζ hζ → ℂ) (hf : Smooth F ζ hζ f)
    (chart : GroupChart F ζ hζ U R P H) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (chart.groupLift x)) chart.T.carrier := by
  let g := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ chart.groupCenter *
    chart.finiteRepresentative
  have hsm := (hf.2 g).comp ((coordinateReindex F).contDiff.comp (groupCoordinates F).contDiff)
  apply hsm.contDiffOn.congr
  intro x hx
  unfold GroupChart.groupLift
  rw [chart.exponential.exponential_formula (groupCoordinates F x)
    (chart.closure_source ⟨x,subset_closure hx,rfl⟩)]
  rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1,
    ← actual_exponential_coordinate_reindex]
  have hc := ActualScalarCasimirTransport.insertion_commutes_finiteRepresentative F ζ hζ
    (KPSmoothActualFlowData.exponential F ((coordinateReindex F) (groupCoordinates F x)))
    chart.finiteRepresentative
  change _ = f (g * _)
  dsimp [g]
  rw [mul_assoc,hc.eq,← mul_assoc]

theorem exists_original_compact_bound (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K : Set (Cover F ζ hζ)) (hK : IsCompact K) :
    ∃ W : Finset (List (Fin (groupDimension F))),
      (∀ w ∈ W, w.length ≤ groupDimension F) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f : X → ℂ,
        Smooth F ζ hζ (fun g => f (q g)) →
        (∀ (v : U.toOpenSubgroup) (g : Cover F ζ hζ), f (q (g*v.val.val)) = f (q g)) →
        (∀ w ∈ W, MemLp (quotientWord w f) 2 R.quotientHaar) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ w ∈ W, lpNorm (quotientWord w f) 2 R.quotientHaar ≤ M) →
          ∀ g ∈ K, ‖f (q g)‖ ≤ C*M := by
  choose D hD using chart_at_point F ζ hζ U R P H
  have hb (g : Cover F ζ hζ) : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (0 : Space (groupDimension F)) r ⊆ (D g).T.carrier :=
    Metric.nhds_basis_closedBall.mem_iff.mp (Metric.isOpen_ball.mem_nhds (D g).zero_mem)
  choose r hr hsub using hb
  let A (g : Cover F ζ hζ) : LocalBall (groupDimension F) :=
    ⟨(D g).T.dimension_pos,0,r g,hr g⟩
  have hAT (g) : closedCarrier (A g) ⊆ (D g).T.carrier := hsub g
  have hnhds (g) : (D g).piece (closedCarrier (A g)) ∈ 𝓝 g := by
    simpa only [hD g, closedCarrier, A] using (D g).piece_nhds _ (Metric.closedBall_mem_nhds _ (hr g)) (hAT g)
  obtain ⟨S,_,hcover⟩ := hK.elim_nhds_subcover
    (fun g => (D g).piece (closedCarrier (A g))) (fun g _ => hnhds g)
  choose W hW C hC hbound using fun g => exists_original_compact_point_bound (D g) (A g) (hAT g)
  refine ⟨S.biUnion W,?_,(∑ g ∈ S,C g)+1,?_,?_⟩
  · intro w hw
    obtain ⟨g,hg,hwg⟩ := Finset.mem_biUnion.mp hw
    exact hW g w hwg
  · have : 0 ≤ ∑ g ∈ S,C g := Finset.sum_nonneg (fun g _ => (hC g).le)
    linarith
  intro f hf hl hp M hM hm g hg
  obtain ⟨a,ha,hga⟩ := Set.mem_iUnion₂.mp (hcover hg)
  obtain ⟨x,hx,u,hgu⟩ := hga
  have hmem (w) (hw : w ∈ W a) : w ∈ S.biUnion W := Finset.mem_biUnion.mpr ⟨a,ha,hw⟩
  have ht := hbound a f (smooth_group_chart _ hf _) hl
    (fun w hw => hp w (hmem w hw)) M hM (fun w hw => hm w (hmem w hw)) x hx
  have hCa : C a ≤ (∑ a ∈ S,C a)+1 := by
    have hs := Finset.single_le_sum (fun a _ => (hC a).le) ha
    linarith
  rw [hgu,hl u]
  exact ht.trans (mul_le_mul_of_nonneg_right hCa hM)
theorem raw_smooth_green (f : Cover F ζ hζ → ℂ)
    (hf : KPLiteralRaw.Smooth F ζ hζ f) : Smooth F ζ hζ f :=
  ⟨hf.1,fun g => RawWordKFinite.expLift_smooth f hf.2.1 g⟩

theorem exists_original_compact_bound_raw (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K : Set (Cover F ζ hζ)) (hK : IsCompact K) :
    ∃ W : Finset (List (Fin (groupDimension F))),
      (∀ w ∈ W, w.length ≤ groupDimension F) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f : X → ℂ,
        KPLiteralRaw.Smooth F ζ hζ (fun g => f (q g)) →
        (∀ (v : U.toOpenSubgroup) (g : Cover F ζ hζ), f (q (g*v.val.val)) = f (q g)) →
        (∀ w ∈ W, MemLp (quotientWord w f) 2 R.quotientHaar) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ w ∈ W, lpNorm (quotientWord w f) 2 R.quotientHaar ≤ M) →
          ∀ g ∈ K, ‖f (q g)‖ ≤ C*M := by
  obtain ⟨W,hW,C,hC,hb⟩ := exists_original_compact_bound U R P H K hK
  exact ⟨W,hW,C,hC,fun f hf => hb f (raw_smooth_green _ hf)⟩
end DedekindZetaZeroFree.FourierContinuation.ResidualOutputSobolev

end
