module

public import DedekindZetaZeroFree.Analysis.Elliptic.LocalizedHyperbolicGreenIdentity
public import DedekindZetaZeroFree.Analysis.Elliptic.PartitionPairingTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCutoffDistributionEquation

open KPContActualCutoffSmoothDescent KPContActualCutoffTestPairingHolomorphy

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)

structure Properties
    (D : Descent F ζ hζ C R P H U ι buffer Ω f χ) : Prop where

  pairings : KPContActualCutoffTestPairingHolomorphy.Conclusions
    F ζ hζ C R P H U ι buffer Ω f χ D

  covered_equation : ∀ s ∈ Ω, ∀ φ : Tests F ζ hζ C R P H U,
    (∫ x, coveredPair F ζ hζ C R P H U (D.cutoff s)
      (testLaplacian F ζ hζ C R P H U φ) x
      ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U)) -
    KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s *
      (∫ x, coveredPair F ζ hζ C R P H U (D.cutoff s)
        (testScalar F ζ hζ C R P H U φ) x
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
          (level F ζ hζ C R P H U)) =
    ∫ x, coveredPair F ζ hζ C R P H U (D.commutator s)
      (testScalar F ζ hζ C R P H U φ) x
      ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U)

  quotient_equation : ∀ s ∈ Ω, ∀ φ : Tests F ζ hζ C R P H U,
    (∫ x, quotientPair F ζ hζ C R P H U (D.cutoff s)
      (testLaplacian F ζ hζ C R P H U φ) x ∂ R.quotientHaar) -
    KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s *
      (∫ x, quotientPair F ζ hζ C R P H U (D.cutoff s)
        (testScalar F ζ hζ C R P H U φ) x ∂ R.quotientHaar) =
    ∫ x, quotientPair F ζ hζ C R P H U (D.commutator s)
      (testScalar F ζ hζ C R P H U φ) x ∂ R.quotientHaar

private lemma scalar_add (w₁ w₂ : SmoothSections F ζ hζ C R P H U) :
    scalar F ζ hζ C R P H U (w₁ + w₂) =
      scalar F ζ hζ C R P H U w₁ + scalar F ζ hζ C R P H U w₂ := by
  funext x; simp [scalar, map_add]

private lemma scalar_smul (a : ℂ) (w : SmoothSections F ζ hζ C R P H U) :
    scalar F ζ hζ C R P H U (a • w) = a • scalar F ζ hζ C R P H U w := by
  funext x; simp [scalar, map_smul]

theorem covered_green_pairing
    (w : SmoothSections F ζ hζ C R P H U)
    (φ : Tests F ζ hζ C R P H U) :
    (∫ x, coveredPair F ζ hζ C R P H U w
        (testLaplacian F ζ hζ C R P H U φ) x
      ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U)) =
    ∫ x, coveredPair F ζ hζ C R P H U
        (KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U w)
        (testScalar F ζ hζ C R P H U φ) x
      ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
        (level F ζ hζ C R P H U) := by
  obtain ⟨L, htransport⟩ := KPContCutoffPartitionTransport.finite_chart_pairing_transport
    F ζ hζ C R P H U φ
  rw [(htransport w).1, (htransport w).2]
  apply Finset.sum_congr rfl
  intro i _
  exact KPContCutoffLocalizedGreen.compact_interior_green
    F ζ hζ (level F ζ hζ C R P H U) R P H (L.chart i) w (L.test i)
    (L.test_compact i) (L.test_interior i)

end DedekindZetaZeroFree.KPContActualCutoffDistributionEquation

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cutoff_distribution_equation
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (_hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (_hΩ : Ω ⊆ KPContinuation.spectralDomain) (_hopen : IsOpen Ω)
    (f : ℂ → S) (_hf : DifferentiableOn ℂ f Ω)
    (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T)
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ) :
    KPContActualCutoffDistributionEquation.Properties F ζ hζ C R P H U
      ι buffer Ω f χ D := by
  have hpair := kp_cont_actual_cutoff_test_pairing_holomorphy
    F ζ hζ C R P H U _hR buffer ι _hι _hStage Ω _hΩ _hopen f _hf χ D
  have hloc := kp_cont_actual_cutoff_local_commutator
    F ζ hζ C R P H U _hR buffer ι _hι _hStage Ω _hΩ f _hf χ D
  have hcov : ∀ s ∈ Ω, ∀ φ : KPContActualCutoffTestPairingHolomorphy.Tests
        F ζ hζ C R P H U,
      (∫ x, KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
          (D.cutoff s)
          (KPContActualCutoffTestPairingHolomorphy.testLaplacian F ζ hζ C R P H U φ) x
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
          (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)) -
      KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s *
        (∫ x, KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
            (D.cutoff s)
            (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U φ) x
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
            (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)) =
      ∫ x, KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
          (D.commutator s)
          (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U φ) x
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
          (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) := by
    intro s hs φ
    have hcut := hpair.cutoff_tests φ
    have hcom := hpair.commutator_tests φ
    have hgreen := KPContActualCutoffDistributionEquation.covered_green_pairing
      F ζ hζ C R P H U (D.cutoff s) φ
    have hsec : KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U (D.cutoff s) =
        KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s •
            D.cutoff s + D.commutator s := by
      have h := hloc.equation s hs
      have h1 : KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U (D.cutoff s) =
          D.commutator s +
            KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s •
              D.cutoff s := by
        calc KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U (D.cutoff s)
            = KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U (D.cutoff s) -
                KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s •
                  D.cutoff s +
                KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s •
                  D.cutoff s := by abel
          _ = D.commutator s +
                KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s •
                  D.cutoff s := by rw [h]
      rwa [add_comm] at h1
    have hpt : KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
          (KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U (D.cutoff s))
          (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U φ)
        = fun x => KPContinuation.spectralCoordinate
              (KPContActualCutoffLocalCommutator.d F : ℤ) s *
            KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
              (D.cutoff s)
              (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U φ) x
          + KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
              (D.commutator s)
              (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U φ) x := by
      funext x
      simp only [KPContActualCutoffTestPairingHolomorphy.coveredPair]
      rw [hsec, KPContActualCutoffDistributionEquation.scalar_add,
        KPContActualCutoffDistributionEquation.scalar_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hInt1 := hcut.covered_integrable s hs
    have hInt2 := hcom.covered_integrable s hs
    have key : (∫ x, KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
          (D.cutoff s)
          (KPContActualCutoffTestPairingHolomorphy.testLaplacian F ζ hζ C R P H U φ) x
        ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
          (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)) =
        KPContinuation.spectralCoordinate (KPContActualCutoffLocalCommutator.d F : ℤ) s *
          (∫ x, KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
              (D.cutoff s)
              (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U φ) x
            ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
              (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)) +
        ∫ x, KPContActualCutoffTestPairingHolomorphy.coveredPair F ζ hζ C R P H U
            (D.commutator s)
            (KPContActualCutoffTestPairingHolomorphy.testScalar F ζ hζ C R P H U φ) x
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
            (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) := by
      rw [hgreen, hpt]
      rw [integral_add]
      · rw [integral_const_mul]
      · exact hInt1.const_mul _
      · exact hInt2
    rw [key]
    ring
  refine ⟨hpair, hcov, ?_⟩
  · intro s hs φ
    have hcut := hpair.cutoff_tests φ
    have hlap := hpair.cutoff_laplacian_tests φ
    have hcom := hpair.commutator_tests φ
    rw [hlap.integral_identification s hs, hcut.integral_identification s hs,
      hcom.integral_identification s hs]
    exact hcov s hs φ

end DedekindZetaZeroFree

end
