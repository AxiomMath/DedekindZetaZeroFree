module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.LocalCommutatorEquation
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.TestPairingHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContCutoffPartitionTransport

open KPContActualCutoffSmoothDescent KPContActualCutoffTestPairingHolomorphy
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentOverlapRationalBranches KPContActualCotangentPieceHilbertSum
open KPContActualCotangentCountableShrinking KPContActualSectorFiniteSupportPartition

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

structure Localization (φ : Tests F ζ hζ C R P H U) where
  compact : Set (KPFiniteCuspAtlas.rawXU F ζ hζ (level F ζ hζ C R P H U))
  compact_isCompact : IsCompact compact
  test_supported : ∀ i x,
    KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
      (H.atlas (level F ζ hζ C R P H U)) i x ∉ compact → (φ.val i).val x = 0
  n : ℕ
  chart : Fin n → ShrunkChart F ζ hζ (level F ζ hζ C R P H U) R P H
  partition : FinitePartition F ζ hζ (level F ζ hζ C R P H U) R P H chart compact Set.univ
  test : (i : Fin n) → localScalarTests (chart i)
  test_coefficient : ∀ i (x : omega (chart i)),
    (test i).val x = (partition.multiplier i (q (chart i) x.val) : ℂ) *
      sectionFields φ.val (chart i) x
  test_compact : ∀ i, HasCompactSupport (liftExtension (chart i) (test i).val)
  test_interior : ∀ i, tsupport (liftExtension (chart i) (test i).val) ⊆ omega (chart i)

private theorem testLaplacian_sum {n : ℕ} (ψ : Fin n → Tests F ζ hζ C R P H U) :
    testLaplacian F ζ hζ C R P H U (∑ i, ψ i) =
      fun x => ∑ i, testLaplacian F ζ hζ C R P H U (ψ i) x := by
  unfold testLaplacian
  simp only [← KPCuspCutoffGraph.divergence_differential_local]
  simp only [map_sum, Submodule.coe_sum]
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply]

private theorem testScalar_sum {n : ℕ} (ψ : Fin n → Tests F ζ hζ C R P H U) :
    testScalar F ζ hζ C R P H U (∑ i, ψ i) =
      fun x => ∑ i, testScalar F ζ hζ C R P H U (ψ i) x := by
  have he (φ : Tests F ζ hζ C R P H U) : testScalar F ζ hζ C R P H U φ =
      ((KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H).symm φ.val).val := rfl
  simp only [he, Submodule.coe_sum, map_sum]
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply]

theorem finite_chart_pairing_transport (φ : Tests F ζ hζ C R P H U) :
    ∃ L : Localization F ζ hζ C R P H U φ,
      ∀ w : SmoothSections F ζ hζ C R P H U,
        ((∫ x, coveredPair F ζ hζ C R P H U w
            (testLaplacian F ζ hζ C R P H U φ) x
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
            (level F ζ hζ C R P H U)) =
          ∑ i, ∫ y, sectionFields w.val (L.chart i) (coordinates (L.chart i) y) *
            star (HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
              (liftExtension (L.chart i) (L.test i).val)
              (coordinates (L.chart i) y).val) ∂(L.chart i).liftedMeasure) ∧
        ((∫ x, coveredPair F ζ hζ C R P H U
            (KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U w)
            (testScalar F ζ hζ C R P H U φ) x
          ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
            (level F ζ hζ C R P H U)) =
          ∑ i, ∫ y, HyperbolicChart.laplacian (KPContCotangentActualOverlap.d F)
              (liftExtension (L.chart i) (sectionFields w.val (L.chart i)))
              (coordinates (L.chart i) y).val *
            star ((L.test i).val (coordinates (L.chart i) y))
            ∂(L.chart i).liftedMeasure) := by
  obtain ⟨K,hK,hφK⟩ := φ.property.2
  obtain ⟨n,a,_,_,⟨Q⟩⟩ := kp_cont_actual_sector_finite_support_partition
    F ζ hζ (level F ζ hζ C R P H U) R P H K Set.univ hK isOpen_univ (Set.subset_univ K)
  have ht := fun i => KPContActualPartitionLocalTest.localize_test a Q φ i
  choose ψ τ hψ hτ hc hi using ht
  let L : Localization F ζ hζ C R P H U φ :=
    { compact := K, compact_isCompact := hK, test_supported := hφK,
      n := n, chart := a, partition := Q, test := τ, test_coefficient := hτ,
      test_compact := hc, test_interior := hi }
  have hrec : φ = ∑ i, ψ i := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    funext z
    simp only [Finset.sum_apply, Submodule.coe_sum]
    simp only [hψ, ← Finset.sum_mul]
    by_cases hz : KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
        (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j z ∈ K
    · have hh := Q.partition _ (Q.contains_compact hz)
      have hh' : (∑ i, (Q.multiplier i (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
          (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j z) : ℂ)) = 1 := by
        exact_mod_cast hh
      rw [hh', one_mul]
    · rw [hφK j z hz, mul_zero]
  have hsupport (i : Fin n) : ∃ B : Set (KPFiniteCuspAtlas.rawXU F ζ hζ (level F ζ hζ C R P H U)),
      IsCompact B ∧ B ⊆ (a i).baseDomain ∧ ∀ j z,
        KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
          (H.atlas (level F ζ hζ C R P H U)) j z ∉ B → ((ψ i).val j).val z = 0 := by
    refine ⟨tsupport (Q.multiplier i), Q.compact_support i, fun x hx => (Q.support_subset i hx).1, ?_⟩
    intro j z hz
    rw [hψ i j z, image_eq_zero_of_notMem_tsupport hz]
    simp
  have hfields (i : Fin n) : sectionFields (ψ i).val (a i) = (τ i).val := by
    funext x
    rw [hτ i x]
    simp only [sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      KPContCotangentActualOverlap.ChartKind.representative, one_smul]
    rw [hψ]
    simp only [map_one, Units.val_one, one_mul]
    rfl
  refine ⟨L,?_⟩
  intro w
  have hp (i : Fin n) := KPContActualPartitionPairing.single_chart_pairing
    (ψ i) (a i) (hsupport i) w
  have hpΔ (i : Fin n) := KPContActualPartitionPairing.single_chart_pairing
    (ψ i) (a i) (hsupport i) (KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U w)
  constructor
  · rw [congrArg (testLaplacian F ζ hζ C R P H U) hrec, testLaplacian_sum]
    have he : coveredPair F ζ hζ C R P H U w
        (fun x => ∑ i, testLaplacian F ζ hζ C R P H U (ψ i) x) =
        fun x => ∑ i, coveredPair F ζ hζ C R P H U w
          (testLaplacian F ζ hζ C R P H U (ψ i)) x := by
      funext x
      simp [coveredPair, map_sum, Finset.mul_sum]
    rw [he, integral_finset_sum _ (fun i _ => (hp i).2.1)]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [L, hfields] using (hp i).2.2.2
  · rw [congrArg (testScalar F ζ hζ C R P H U) hrec, testScalar_sum]
    have he : coveredPair F ζ hζ C R P H U
        (KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U w)
        (fun x => ∑ i, testScalar F ζ hζ C R P H U (ψ i) x) =
        fun x => ∑ i, coveredPair F ζ hζ C R P H U
          (KPContActualCutoffLocalCommutator.Δloc F ζ hζ C R P H U w)
          (testScalar F ζ hζ C R P H U (ψ i)) x := by
      funext x
      simp [coveredPair, map_sum, Finset.mul_sum]
    rw [he, integral_finset_sum _ (fun i _ => (hpΔ i).1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hpΔ i).2.2.1]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [KPContActualCutoffLocalCommutator.localLaplacian_chart, hfields]

end DedekindZetaZeroFree.KPContCutoffPartitionTransport

end
