module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.FrequencyDetector
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.FrequencySubpowerBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyRightBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawReciprocal31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem minus_mask_correspondence (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hgL : ∀ s : ℂ, 1 < s.re →
      g s = Detector.idealLSeries F (FixedData.primMinus D u).character s) :
    ∀ ξ : ℂ, 0 < ξ.re →
      (FixedData.pkg D).minus u ξ =
        Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet ((FixedData.pkg D).U u))
          (fun v => (FixedData.primMinus D u).character v.asIdeal) ξ * g ξ := by
  intro ξ hξ
  have hnp := ((FixedData.pkg D).nonprincipal u hu).2
  rw [RawHeckeIdentification31.minus_eq_hecke_mul_mask D u hu ξ hξ, mul_comm]
  congr 1
  have hA := RowHeckeBridge.hecke_analyticOn D.recipe.A (FixedData.primMinus D u) hnp
  have hgA : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re} := fun z _ => hg.analyticAt z
  have hconn : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hev : g =ᶠ[nhds (2 : ℂ)]
      (RowHeckeBridge.hecke D.recipe.A (FixedData.primMinus D u) hnp).L := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    rw [hgL z hz, RowHeckeBridge.hecke_eq_idealLSeries D.recipe.A (FixedData.primMinus D u) hnp z hz]
  have key := hgA.eqOn_of_preconnected_of_eventuallyEq hA hconn
    (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) hev
  exact (key hξ).symm

theorem raw_reciprocal :
    ∃ A ρ : ℝ, 0 ≤ A ∧ RawConvexityExponent D A ∧ HeightSpec D A ρ ∧
      (∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        (FixedData.rawExceptionalSet D ρ U).Finite ∧
          ((FixedData.rawExceptionalSet D ρ U).ncard : ℝ) ≤ C * U ^ DetectorDef.α) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ Uε : ℝ, 2 ≤ Uε ∧ ∀ U : ℝ, Uε ≤ U →
        ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
          U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
          u ∉ FixedData.rawExceptionalSet D ρ U →
          ∀ ξ : ℂ, Scales.goodLine ≤ ξ.re → ξ.re ≤ Scales.rightLine → |ξ.im| ≤ 2 * U ^ ρ →
            (FixedData.pkg D).minus u ξ ≠ 0 ∧
              ‖((FixedData.pkg D).minus u ξ)⁻¹‖ ≤ C * U ^ ε := by
  obtain ⟨A, ρ, hA, hc, hρ, hcount⟩ := RawDetector31.detector_exists D
  refine ⟨A, ρ, hA, hc, hρ, hcount, fun ε hε => ?_⟩
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨Cp, hCp, Up, hUp, hprim⟩ :=
    RawReciprocalPrimitive31.raw_reciprocal_primitive D A ρ hA hc hρ (ε / 2) hε2
  obtain ⟨Cm, hCm, hmask⟩ := RawDeletionMask31.minus_mask_subpower D (8801 / 10000 : ℝ) (ε / 2)
    (by norm_num) hε2
  refine ⟨Cp * Cm * 2 ^ (ε / 2), mul_pos (mul_pos hCp hCm) (by positivity), max Up 2, le_max_right _ _,
    fun U hU u hu hq1 hq2 hqe ξ hξ1 hξ2 hξ3 => ?_⟩
  have hUp' : Up ≤ U := le_trans (le_max_left _ _) hU
  have hU2 : 2 ≤ U := le_trans (le_max_right _ _) hU
  have hUpos : 0 < U := by linarith
  have hxg : (8801 / 10000 : ℝ) ≤ ξ.re := hξ1
  have hpos : 0 < ξ.re := by linarith
  have hnp := ((FixedData.pkg D).nonprincipal u hu).2
  obtain ⟨g, hgd, hgξ⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A
    (FixedData.primMinus D u) hnp
  have hgL : ∀ s : ℂ, 1 < s.re →
      g s = Detector.idealLSeries F (FixedData.primMinus D u).character s := fun s hs => by
    rw [hgξ s (by linarith), RowHeckeBridge.hecke_eq_idealLSeries D.recipe.A
      (FixedData.primMinus D u) hnp s hs]
  obtain ⟨hgne, hginv⟩ := (hprim U hUp' u hu hq1 hq2 hqe g hgd hgL ξ hxg hξ3)
  obtain ⟨hmne, -, hminv⟩ := hmask u ξ hxg
  have hcorr := minus_mask_correspondence D u hu g hgd hgL ξ hpos
  have hq0 : 0 ≤ frequencyNorm D.recipe u := by
    unfold frequencyNorm; positivity
  have hqU : frequencyNorm D.recipe u ^ (ε / 2) ≤ (2 * U) ^ (ε / 2) :=
    Real.rpow_le_rpow hq0 hq2.le hε2.le
  have h2U : (2 * U) ^ (ε / 2) = 2 ^ (ε / 2) * U ^ (ε / 2) :=
    Real.mul_rpow (by norm_num) hUpos.le
  have hUe : U ^ (ε / 2) * U ^ (ε / 2) = U ^ ε := by
    rw [← Real.rpow_add hUpos]; congr 1; ring
  rw [hcorr]
  refine ⟨mul_ne_zero hmne hgne, ?_⟩
  rw [mul_inv, norm_mul]
  have hA1 : ‖(g ξ)⁻¹‖ ≤ Cp * U ^ (ε / 2) := hginv
  have hA2 : ‖(Detector.finiteEulerDeletionMask F
      (RawHeckeRows.rawDeletionSet ((FixedData.pkg D).U u))
      (fun v => (FixedData.primMinus D u).character v.asIdeal) ξ)⁻¹‖
        ≤ Cm * (2 ^ (ε / 2) * U ^ (ε / 2)) := by
    refine hminv.trans ?_
    rw [← h2U]
    exact mul_le_mul_of_nonneg_left hqU hCm.le
  calc ‖(Detector.finiteEulerDeletionMask F
      (RawHeckeRows.rawDeletionSet ((FixedData.pkg D).U u))
      (fun v => (FixedData.primMinus D u).character v.asIdeal) ξ)⁻¹‖ * ‖(g ξ)⁻¹‖
      ≤ (Cm * (2 ^ (ε / 2) * U ^ (ε / 2))) * (Cp * U ^ (ε / 2)) :=
        mul_le_mul hA2 hA1 (norm_nonneg _)
          (mul_nonneg hCm.le (mul_nonneg (by positivity) (Real.rpow_nonneg hUpos.le _)))
    _ = Cp * Cm * 2 ^ (ε / 2) * U ^ ε := by rw [← hUe]; ring

theorem raw_reciprocal_right :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
      ∀ ξ : ℂ, Scales.rightLine ≤ ξ.re →
        (FixedData.pkg D).minus u ξ ≠ 0 ∧ ‖((FixedData.pkg D).minus u ξ)⁻¹‖ ≤ C := by
  have hx1 : (1 : ℝ) < Scales.rightLine := by rw [Scales.rightLine_eq]; norm_num
  obtain ⟨C, hC, h⟩ := RawRightHecke31.minus_right D Scales.rightLine hx1
  exact ⟨C, hC, fun u _ ξ hξ => ⟨(h u ξ hξ).1, (h u ξ hξ).2.2⟩⟩

end

end DedekindZetaZeroFree.Quantitative.RawReciprocal31
