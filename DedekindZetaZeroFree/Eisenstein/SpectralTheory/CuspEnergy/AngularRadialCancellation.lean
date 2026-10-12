module

public import DedekindZetaZeroFree.Eisenstein.Residues.AngularRadialCancellation
public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.KernelMean

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsFixedHaarDisintegration
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : SphericalTransport F ζ hζ)
variable (H : AllLevels F ζ hζ R P)
variable (U : Level F ζ hζ)
theorem actual_angular_radial_cancellation {T : ℝ}
    (χ : CuspIndex (H.atlas U) → KPCutoffSource.SmoothCuspCutoff T)
    (τ : ℝ) (hτ : τ < T) (c : CuspIndex (H.atlas U) → ℂ) :
    (((H.disintegration U).beta Set.univ).toReal : ℂ) *
      (∫ r : ℝ in Set.Ioi (Real.exp (2*(Module.finrank ℚ F / 2:ℕ)*τ)),
        ∫ω : Omega (H.atlas U), c ω.1 * ((r:ℂ) *
          KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
            (χ ω.1).toFun 0 (Real.log r/(2*(Module.finrank ℚ F / 2:ℕ))))
          ∂probability (H.atlas U) (H.disintegration U).beta ∂radialMeasure) =
    (-(4:ℂ)*(Module.finrank ℚ F / 2:ℕ)/3) *
      ((((H.disintegration U).beta Set.univ).toReal : ℂ) *
        ∫ω : Omega (H.atlas U), c ω.1 ∂probability (H.atlas U) (H.disintegration U).beta) := by
  let : MeasurableSpace (CuspIndex (H.atlas U)) := borel _
  let : BorelSpace (CuspIndex (H.atlas U)) := ⟨rfl⟩
  let := (H.disintegration U).probability_mass
  have hp : Measurable (fun ω : Omega (H.atlas U) => ω.1) :=
    (continuous_def.mpr (fun s _ => isOpen_sigma_fst_preimage s)).measurable
  have hd : 0 < Module.finrank ℚ F / 2 := by
    rw [← (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1]
    exact (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2
  rw [KPCutoffSource.angular_radial_cancellation _ _ hp _ hd χ τ hτ c]
  ring

end DedekindZetaZeroFree.KPMsFixedHaarDisintegration

end
