module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.WeakEnergyCutoffExhaustion

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
open KPMsClearedTruncationL2
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem first_derivative_memLp_of_energy
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    {U : Level F ζ hζ} (f : smoothSpace F ζ hζ U)
    (c : KPSmoothActualFlowData.B F → ℝ) (hc : ∀ b, 0 < c b)
    (hJ : (∫⁻ x, ENNReal.ofReal (∑ b, c b *
      ‖KPSmoothActualFlowData.flowDerivative F ζ hζ b f.val x‖ ^ 2)
      ∂ R.quotientHaar) < ⊤) (b : KPSmoothActualFlowData.B F) :
    MemLp (KPSmoothActualFlowData.flowDerivative F ζ hζ b f.val) 2 R.quotientHaar := by
  letI : BorelSpace (KPSmoothActualFlowData.X F ζ hζ) := ⟨rfl⟩
  have hd : Continuous (KPSmoothActualFlowData.flowDerivative F ζ hζ b f.val) :=
    (smoothDerivatives F ζ hζ U [b] f).continuous
  apply (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mpr
  refine ⟨(hd.norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  have hp (x : X F ζ hζ) : ‖KPSmoothActualFlowData.flowDerivative F ζ hζ b f.val x‖ ^ 2 ≤
      (c b)⁻¹ * ∑ d, c d * ‖KPSmoothActualFlowData.flowDerivative F ζ hζ d f.val x‖ ^ 2 := by
    have hs := Finset.single_le_sum
      (fun d (_ : d ∈ Finset.univ) => mul_nonneg (hc d).le (sq_nonneg
        ‖KPSmoothActualFlowData.flowDerivative F ζ hζ d f.val x‖))
      (Finset.mem_univ b)
    have hh : ‖KPSmoothActualFlowData.flowDerivative F ζ hζ b f.val x‖ ^ 2 ≤
        (∑ d, c d * ‖KPSmoothActualFlowData.flowDerivative F ζ hζ d f.val x‖ ^ 2) / c b :=
      (le_div_iff₀ (hc b)).mpr (by simpa [mul_comm] using hs)
    simpa [div_eq_mul_inv, mul_comm] using hh
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((c b)⁻¹ * ∑ d, c d *
        ‖KPSmoothActualFlowData.flowDerivative F ζ hζ d f.val x‖ ^ 2) ∂ R.quotientHaar :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal (c b)⁻¹ * (∫⁻ x, ENNReal.ofReal (∑ d, c d *
        ‖KPSmoothActualFlowData.flowDerivative F ζ hζ d f.val x‖ ^ 2) ∂ R.quotientHaar) := by
      simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr (hc b).le)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ

theorem original_first_derivative_memLp
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    {U₀ : Level F ζ hζ} (f : smoothSpace F ζ hζ U₀)
    (c : KPSmoothActualFlowData.B F → ℝ) (hc : ∀ b, 0 < c b)
    (hf2 : MemLp f.val 2 R.quotientHaar)
    (hv2 : MemLp (fun x => ∑ b, (c b : ℂ) *
      KPSmoothActualFlowData.wordDerivative F ζ hζ [b,b] f.val x) 2 R.quotientHaar)
    (b : KPSmoothActualFlowData.B F) :
    MemLp (KPSmoothActualFlowData.flowDerivative F ζ hζ b f.val) 2 R.quotientHaar := by
  exact first_derivative_memLp_of_energy R f c hc
    (original_diagonal_energy_finite A R P D Y hY f c (fun b => (hc b).le) hf2 hv2) b

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
