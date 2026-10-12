module

public import DedekindZetaZeroFree.Analysis.Complex.CompactMeromorphicFamilies
public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalHilbertOrthogonalCenters
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.ResidueFamiliesAndPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming cutoff → cutoff
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming lift_eq → lift_eq
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ

open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming compact_word_holomorphy → compact_word_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming singleton_combination → singleton_combination
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming scalar_eq_lift → scalar_eq_lift
open _root_.DedekindZetaZeroFree.KPContActualCommonDiskRightHolomorphy renaming continuous_of_pieces → continuous_of_pieces
open scoped BigOperators
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.FiniteCompactAssembly renaming finite_compact_numerator → finite_compact_numerator

theorem finite_owned_residue_hilbert_orthogonal_centers
    (K : Subgroup G) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (A : TensorActionSource.LiteralResidueFamily hK) :
    ∃ (n : ℕ) (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (m : Fin n → ℕ) (w : ∀ i, Fin (m i) → List (Fin (groupDimension F)))
      (B : ∀ i, Fin (m i) → ℂ → ℂ)
      (Z : ∀ i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H (U i))
      (z : ∀ i, Fin (m i) → KPContActualAllCuspSource.Sector F ζ hζ C R P H (U i)),
      (∀ i j, KPContActualSmoothLineGluing.Represents F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H (U i)) R P H (Z i j).val (z i j)) ∧
      (∀ i j, (z i j, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) 0 • z i j) ∈
        (sourceLaplacian F ζ hζ C R P H (U i)).graph) ∧
      (∀ i j, CuspEigentestOrthogonal F ζ hζ C R P H (U i) 0 (z i j)) ∧
      (∀ i j g, KPMsGreenFlux.casimir F ζ hζ
        (groupScalar F ζ hζ C R P H (U i) (Z i j)) g =
        KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
          groupScalar F ζ hζ C R P H (U i) (Z i j) g) ∧
      (∀ i j, KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
        F ζ hζ C R P H (U i) (Z i j) → Z i j = 0) ∧
      ∀ g, A.cleared f 0 g = ∑ i, ∑ j, B i j 0 * actualRightWord F ζ hζ (w i j)
        (groupScalar F ζ hζ C R P H (U i) (Z i j)) g := by
  obtain ⟨n, U, m, w, B, Z, z, hz, heig, horth, hnative, hcus, q, J, T, r, hq, hq0, hJ, hch,
    hr, hb, hT, hclear, hcenter⟩ := finite_literal_global_hilbert_orthogonal_centers F ζ hζ C R P H K hK f
  refine ⟨n, U, m, w, B, Z, z, hz, heig, horth, hnative, hcus, ?_⟩
  intro g
  obtain ⟨O, u, hO, hc, hOc, hu, hub, hE, hAc, han⟩ := A.germ.2 f
  have he : (fun s => J s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => q s * A.E f s g) := by
    apply CompactPeriodAnalyticity.UpperPeriodContinuation.chamber_identity_germ (hJ g)
      (hq.meromorphicOn.mul ((A.normal f g).meromorphicOn))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ?_ 0 ?_
    · intro s hs
      change J s g = q s * A.E f s g
      rw [hch s hs, A.germ.1 f s hs]
    · norm_num [KPContinuation.spectralDomain]
  have hnum : (fun s => T s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => q s * A.cleared f s g) := by
    filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hu), self_mem_nhdsWithin]
      with s hes hsr hsu hne
    rw [hclear s hsr hne]
    change s * J s g = q s * A.cleared f s g
    rw [hes, congrFun (hAc s hsu hne) g]
    change s * (q s * A.E f s g) = q s * (s * A.E f s g)
    ring
  have hqA : ContinuousAt (fun s => q s * A.cleared f s g) 0 :=
    (hq 0 (by norm_num [KPContinuation.spectralDomain])).continuousAt.mul
      ((han g) 0 (Metric.mem_ball_self hu)).continuousAt
  have he0 := (((hT g) 0 (Metric.mem_ball_self hr)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hqA).mp hnum |>.eq_of_nhds
  have hpin : T 0 g = A.cleared f 0 g := by simpa only [hq0, one_mul] using he0
  exact hpin.symm.trans (hcenter g)

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
