module

public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.CuspidalOrthogonalCenters
public import DedekindZetaZeroFree.Eisenstein.Continuation.Residual.CasimirAndEigenCenters

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming native_second_word → native_second_word
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming nativeIndex → nativeIndex
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U

theorem spherical_scalar_native_orthogonal_centers
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U) (hv : v ≠ 0) :
    ∃ Z : ℂ → Smooth,
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g : G,
        groupScalar F ζ hζ C R P H U (Z s) g =
          ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * g)) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → Smooth,
            SmoothTaylorData F ζ hζ C R P H U (Metric.ball c r) N ∧
            (∀ s ∈ Metric.ball c r, s ≠ c →
              groupScalar F ζ hζ C R P H U (N s) =
                (s - c) • groupScalar F ζ hζ C R P H U (Z s)) ∧
            (∃ z : KPContActualAllCuspSource.Sector F ζ hζ C R P H U,
              KPContActualSmoothLineGluing.Represents F ζ hζ level R P H (N c).val z ∧
              (z, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c • z) ∈
                (ResidualHilbertCenters.sourceLaplacian F ζ hζ C R P H U).graph ∧
              ResidualHilbertCenters.CuspEigentestOrthogonal F ζ hζ C R P H U c z) ∧
            (∀ g : G, KPMsGreenFlux.casimir F ζ hζ
              (groupScalar F ζ hζ C R P H U (N c)) g =
              KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) c *
                groupScalar F ζ hζ C R P H U (N c) g) ∧
            (KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
              F ζ hζ C R P H U (N c) → N c = 0) := by
  obtain ⟨Z, hch, hl⟩ := ResidualHilbertCenters.spherical_scalar_hilbert_orthogonal_centers
    F ζ hζ C R P H U v hv
  let A : ℂ → G → ℂ := fun s => groupScalar F ζ hζ C R P H U (Z s)
  have hm (w) (g) : MeromorphicOn (fun s => actualRightWord F ζ hζ w (A s) g)
      KPContinuation.spectralDomain := by
    apply actual_word_meromorphic F ζ hζ C R P H U A _ w g
    intro c hc
    obtain ⟨r, hr, hb, N, hN, he, hz, hcus⟩ := hl c hc
    exact ⟨r, hr, hb, fun s => groupScalar F ζ hζ C R P H U (N s),
      hN.right_holomorphic, he⟩
  refine ⟨Z, hch, ?_⟩
  intro c hc
  obtain ⟨r, hr, hb, N, hN, he, hz, hcus⟩ := hl c hc
  refine ⟨r, hr, hb, N, hN, he, hz, ?_, hcus⟩
  intro g
  apply spherical_numerator_casimir F ζ hζ U v A hm _ c hc r hr
    (fun s => groupScalar F ζ hζ C R P H U (N s)) _ he g
  · intro s hs
    exact funext (hch s hs)
  · intro w g
    exact actual_word_analytic F ζ hζ C R P H U Metric.isOpen_ball _
      hN.right_holomorphic w g

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry

end
