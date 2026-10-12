module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspCutoffs.GlobalRegularity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
open scoped Classical NumberField Topology ENNReal
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.NativeCutoffExhaustion
open KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming admissible_mono → admissible_mono
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming modulus_gt_of_not_core → modulus_gt_of_not_core
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.CutoffApproximation renaming cutoff_bound → cutoff_bound
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (D : KPMsFixedHaarDisintegration.Disintegration A R P)

 def cutoff (Y : ℝ) (n : ℕ) (x : X F ζ hζ) : ℂ :=
  (ActualSharpStokes.CutoffApproximation.coreCutoff A R P D (Y + n) (Y + n) x : ℂ)

 theorem cutoff_regular (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (n : ℕ) :
    Continuous (cutoff A R P D Y n) ∧ HasCompactSupport (cutoff A R P D Y n) ∧
      (∀ x, ‖cutoff A R P D Y n x‖ ≤ 1) ∧
      ∀ (w : NumberField.InfinitePlace F) (i : Fin 6) (x : X F ζ hζ),
        LipschitzWith 8 (fun t : ℝ => cutoff A R P D Y n
          (KPSmoothActualFlowData.rightTranslate F ζ hζ
            (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
              (KPSmoothActualFlowData.flow F (w,i) t)) x)) := by
  have hYn : 0 < Y + (n : ℝ) := add_pos_of_pos_of_nonneg hY.1 (Nat.cast_nonneg _)
  obtain ⟨hc, hs, hl⟩ := ActualSharpStokes.WeakCutoffSources.global_coreCutoff_native_regular
    A R P D (Y+n) (admissible_mono A hY (le_add_of_nonneg_right (Nat.cast_nonneg _))) (Y+n) hYn
  refine ⟨hc, hs, ?_, ?_⟩
  · intro x
    simpa only [cutoff, Complex.norm_real, Real.norm_eq_abs] using
      cutoff_bound A R P D (Y+n) (Y+n) x
  · intro w i x
    have he : Real.nnabs (4 * (Y + (n : ℝ) + (Y + (n : ℝ))) / (Y + (n : ℝ))) = 8 := by
      apply Subtype.ext
      change |4 * (Y + (n : ℝ) + (Y + (n : ℝ))) / (Y + (n : ℝ))| = 8
      rw [show 4 * (Y + (n : ℝ) + (Y + (n : ℝ))) / (Y + (n : ℝ)) = 8 by
        field_simp; ring]
      norm_num
    simpa only [cutoff, he] using hl w i x

private theorem cutoff_eventually_one (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (x : X F ζ hζ) :
    ∀ᶠ n : ℕ in atTop, cutoff A R P D Y n x = 1 := by
  have ht : Tendsto (fun n : ℕ => Y + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ Y tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (D.modulus (P.projection U x)))] with n hn
  have hx : x ∈ quotientCore A P (Y + (n : ℝ)) := by
    by_contra hxn
    have hm := modulus_gt_of_not_core A R P D (Y+n)
      (admissible_mono A hY (le_add_of_nonneg_right (Nat.cast_nonneg _))) x hxn
    exact (not_lt_of_ge hn) hm
  simp only [cutoff, ActualSharpStokes.CutoffApproximation.coreCutoff, ite_eq_left hx, Complex.ofReal_one]

 theorem cutoff_tendsto_one (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) (x : X F ζ hζ) :
    Tendsto (fun n : ℕ => cutoff A R P D Y n x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [cutoff_eventually_one A R P D Y hY x] with n hn
    exact hn.symm)
end DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.NativeCutoffExhaustion

end
