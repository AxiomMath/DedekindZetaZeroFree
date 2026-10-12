module

public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.HilbertBoundaryCenters

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
variable {F : Type} [Field F] [NumberField F]
variable {SS : SArithmeticData F} {η : RayClassCharacter F SS.modulus}
variable (AR : PrincipalMellin.ActualRecipe SS η)
variable (AP : KPGlobalTorusFiniteStages.CompatibleModelData F AR.A.zeta12 AR.A.primitive_zeta12)
variable (AC : KPGlobalTorusFiniteStages.LocalFiberData F AR.A.zeta12 AR.A.primitive_zeta12 AP)
local notation "G" => KPGlobalTorusFunctionData.G F AR.A.zeta12 AR.A.primitive_zeta12
variable (D : KPGlobalTorusInducingPlan.ModelData F AR.A.zeta12 AR.A.primitive_zeta12)
variable (Haar : KPSmoothLocalQuotientCharts.HaarRecipe F AR.A.zeta12 AR.A.primitive_zeta12)
variable (Transport : KPMsFixedHaarDisintegration.SphericalTransport F AR.A.zeta12 AR.A.primitive_zeta12)
variable (H : KPMsFixedHaarDisintegration.AllLevels F AR.A.zeta12 AR.A.primitive_zeta12 Haar Transport)
variable (U : KPMsRationalCompactCrossPairing.Level F AR.A.zeta12 AR.A.primitive_zeta12)
local notation "level" => KPContActualAllCuspSource.level F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U

theorem spherical_scalar_native_boundary_centers
    (v : KPContActualSphericalFlatStage.Stage F AR.A.zeta12 AR.A.primitive_zeta12 U) (hv : v ≠ 0) :
    ∃ Z : ℂ → Smooth,
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g : G,
        groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (Z s) g =
          ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F AR.A.zeta12 AR.A.primitive_zeta12 s v.val).val
              (KPLiteralRaw.rationalLift F AR.A.zeta12 AR.A.primitive_zeta12 (Quotient.out c) * g)) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → Smooth,
            SmoothTaylorData F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (Metric.ball c r) N ∧
            (∀ s ∈ Metric.ball c r, s ≠ c →
              groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (N s) =
                (s - c) • groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (Z s)) ∧
            (∃ z : KPContActualAllCuspSource.Sector F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U,
              KPContActualSmoothLineGluing.Represents F AR.A.zeta12 AR.A.primitive_zeta12 level Haar Transport H (N c).val z ∧
              (z, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c • z) ∈
                (ResidualHilbertCenters.sourceLaplacian F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U).graph ∧
              (c = 0 → LiteralSource.SphericalBoundaryProperty AR AP AC D Haar Transport H U v z)) ∧
            (∀ g : G, KPMsGreenFlux.casimir F AR.A.zeta12 AR.A.primitive_zeta12
              (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (N c)) g =
              KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) c *
                groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (N c) g) ∧
            (KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
              F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (N c) → N c = 0) := by
  obtain ⟨Z, hch, hl⟩ := LiteralSource.spherical_scalar_hilbert_boundary_centers
    AR AP AC D Haar Transport H U v hv
  let A : ℂ → G → ℂ := fun s => groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (Z s)
  have hm (w) (g) : MeromorphicOn (fun s => actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w (A s) g)
      KPContinuation.spectralDomain := by
    apply actual_word_meromorphic F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U A _ w g
    intro c hc
    obtain ⟨r, hr, hb, N, hN, he, hz, hcus⟩ := hl c hc
    exact ⟨r, hr, hb, fun s => groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (N s),
      hN.right_holomorphic, he⟩
  refine ⟨Z, hch, ?_⟩
  intro c hc
  obtain ⟨r, hr, hb, N, hN, he, hz, hcus⟩ := hl c hc
  refine ⟨r, hr, hb, N, hN, he, hz, ?_, hcus⟩
  intro g
  apply spherical_numerator_casimir F AR.A.zeta12 AR.A.primitive_zeta12 U v A hm _ c hc r hr
    (fun s => groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (N s)) _ he g
  · intro s hs
    exact funext (hch s hs)
  · intro w g
    exact actual_word_analytic F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Metric.isOpen_ball _
      hN.right_holomorphic w g

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry

end
