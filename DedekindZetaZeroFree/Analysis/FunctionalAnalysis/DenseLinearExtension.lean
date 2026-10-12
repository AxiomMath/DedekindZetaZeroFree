module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.FriedrichsLaplacian

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentBoundedScalarMultiplier

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentIntrinsicHilbertIntegral

private theorem dense_linear_extension {S V : Type*} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (e f : S →ₗ[ℂ] V) (hd : DenseRange e) (B : ℝ) (hB : 0 ≤ B)
    (hn : ∀ x, ‖f x‖ ≤ B * ‖e x‖) :
    ∃ N : V →L[ℂ] V, ‖N‖ ≤ B ∧ ∀ x, N (e x) = f x := by
  refine ⟨f.extendOfNorm e, ?_, ?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le hd hB hn
  · exact LinearMap.extendOfNorm_eq hd ⟨B, hn⟩

theorem exists_multiplier
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (η : RealSmoothCutoff F ζ hζ U R P H)
    (B : ℝ) (hB : 0 ≤ B) (hη : ∀ x, |η.val x| ≤ B) :
    ∃ N : KPContActualSectorCotangentL2.V F ζ hζ U R P H →L[ℂ]
        KPContActualSectorCotangentL2.V F ζ hζ U R P H,
      ‖N‖ ≤ B ∧ ∀ W : T_U F ζ hζ U R P H,
        N (j W) = j (cotangentMultiply η W) := by
  classical
  have hdense : DenseRange (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) :=
    KPContActualSectorFriedrichsSynthesis.cotangentDense F ζ hζ U R P H μG hμG hR realization
  let f : T_U F ζ hζ U R P H →ₗ[ℂ] KPContActualSectorCotangentL2.V F ζ hζ U R P H :=
    (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)).comp (cotangentMultiply η)
  have hnorm : ∀ W : T_U F ζ hζ U R P H,
      ‖f W‖ ≤ B * ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W‖ := by
    intro W
    have hns : ∀ x : KPFiniteCuspAtlas.rawXU F ζ hζ U,
        (normSquare (cotangentMultiply η W).val x : ℝ)
          = (η.val x)^2 * (normSquare W.val x : ℝ) := by
      intro x
      obtain ⟨a, y, hy⟩ := KPContActualGlobalGreen.base_covered (F := F) (ζ := ζ)
        (hζ := hζ) (U := U) (R := R) (P := P) (H := H) x
      rw [← hy, normSquare_chart, normSquare_chart]
      simp only [NNReal.coe_pow, coe_nnnorm]
      rw [show (coefficient (cotangentMultiply η W) a y)
          = (η.val (KPContCotangentOverlapRationalBranches.q a y.val) : ℂ)
              • coefficient W.val a y from rfl]
      rw [norm_smul, mul_pow,
        show ‖((η.val (KPContCotangentOverlapRationalBranches.q a y.val) : ℝ) : ℂ)‖
            = |η.val (KPContCotangentOverlapRationalBranches.q a y.val)| from by simp,
        sq_abs]
    have hr1 : toAeQuotient (cotangentSquareFamily (cotangentMultiply η W))
        = intrinsicClass (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H)
            (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
              (cotangentMultiply η W)) := by
      rw [show j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
            (cotangentMultiply η W)
          = KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H
              (cotangentSquareFamily (cotangentMultiply η W)) from rfl]
      rfl
    have hr2 : toAeQuotient (cotangentSquareFamily W)
        = intrinsicClass (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H)
            (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W) := by
      rw [show j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W
          = KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H
              (cotangentSquareFamily W) from rfl]
      rfl
    have h1 := norm_sq_eq_integral (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H)
      (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) (cotangentMultiply η W))
      (cotangentSquareFamily (cotangentMultiply η W)) hr1
    have h2 := norm_sq_eq_integral (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H)
      (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W)
      (cotangentSquareFamily W) hr2
    have h1' : ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
          (cotangentMultiply η W)‖^2
        = ∫ x, (η.val x)^2 * (normSquare W.val x : ℝ)
            ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
      rw [h1]
      apply integral_congr_ae
      filter_upwards with x
      exact hns x
    have h2' : ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W‖^2
        = ∫ x, (normSquare W.val x : ℝ)
            ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
      rw [h2]
      apply integral_congr_ae
      filter_upwards with x
      rfl
    have hle : (∫ x, (η.val x)^2 * (normSquare W.val x : ℝ)
          ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P))
        ≤ ∫ x, B^2 * (normSquare W.val x : ℝ)
            ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P) := by
      apply integral_mono_of_nonneg
      · filter_upwards with x
        positivity
      · exact (integrable_normSquare (cotangentSquareFamily W)).const_mul (B^2)
      · filter_upwards with x
        have habs := abs_le.mp (hη x)
        have hx : (η.val x)^2 ≤ B^2 := by nlinarith [habs.1, habs.2, hB]
        have hns0 : (0:ℝ) ≤ (normSquare W.val x : ℝ) := by positivity
        nlinarith [hx, hns0]
    have hkey : ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
          (cotangentMultiply η W)‖^2
        ≤ B^2 * ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W‖^2 := by
      rw [h1', h2']
      calc (∫ x, (η.val x)^2 * (normSquare W.val x : ℝ)
            ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P))
          ≤ ∫ x, B^2 * (normSquare W.val x : ℝ)
              ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P) := hle
        _ = B^2 * ∫ x, (normSquare W.val x : ℝ)
              ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P) := integral_const_mul _ _
    have hbound : ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
          (cotangentMultiply η W)‖
        ≤ B * ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W‖ := by
      calc ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
            (cotangentMultiply η W)‖
          = Real.sqrt (‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
              (cotangentMultiply η W)‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt ((B * ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W‖)^2) :=
            Real.sqrt_le_sqrt (by rw [mul_pow]; exact hkey)
        _ = B * ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W‖ :=
            Real.sqrt_sq (by positivity)
    show ‖f W‖ ≤ B * ‖j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) W‖
    rw [show f W = j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
        (cotangentMultiply η W) from rfl]
    exact hbound
  let e : T_U F ζ hζ U R P H →ₗ[ℂ] KPContActualSectorCotangentL2.V F ζ hζ U R P H :=
    j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  exact @dense_linear_extension (T_U F ζ hζ U R P H)
    (KPContActualSectorCotangentL2.V F ζ hζ U R P H)
    (inferInstance : AddCommGroup (T_U F ζ hζ U R P H))
    (inferInstance : Module ℂ (T_U F ζ hζ U R P H))
    (intrinsicNormedAddCommGroup cover) (intrinsicNormedSpace cover)
    (intrinsicCompleteSpace cover) e f hdense B hB hnorm

end DedekindZetaZeroFree.KPContActualCotangentBoundedScalarMultiplier

end
