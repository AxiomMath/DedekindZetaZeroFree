module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.RadialIntegrabilityAndCuspCancellation

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DedekindZetaZeroFree.KPCutoffSource
theorem finite_angular_integral {Ω J : Type*}
    [MeasurableSpace Ω] [Fintype J] [TopologicalSpace J] [DiscreteTopology J]
    [MeasurableSpace J] [BorelSpace J] (ν : Measure Ω) [IsFiniteMeasure ν]
    (p : Ω → J) (hp : Measurable p) (f : J → ℂ) :
    (∫ ω, f (p ω) ∂ν) = ∑j,(Measure.map p ν).real {j} • f j := by
  have hc : Continuous f := continuous_of_discreteTopology
  rw [← integral_map hp.aemeasurable hc.aestronglyMeasurable]
  exact integral_fintype (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
theorem angular_radial_cancellation {Ω J : Type*}
    [MeasurableSpace Ω] [Fintype J] [TopologicalSpace J] [DiscreteTopology J]
    [MeasurableSpace J] [BorelSpace J] (ν : Measure Ω) [IsFiniteMeasure ν]
    (p : Ω → J) (hp : Measurable p) (d : ℕ) (hd : 0 < d)
    {T : ℝ} (χ : J → SmoothCuspCutoff T) (τ : ℝ) (hτ : τ < T) (c : J → ℂ) :
    (∫ r : ℝ in Set.Ioi (Real.exp (2*d*τ)),
      ∫ω, c (p ω) * ((r:ℂ)*incomingCommutatorMultiplier d (χ (p ω)).toFun 0
        (Real.log r/(2*d))) ∂ν ∂KPMsFixedHaarDisintegration.radialMeasure) =
      (-(4:ℂ)*(d:ℂ)/3) * ∫ω,c (p ω) ∂ν := by
  have hi (r : ℝ) :
      (∫ω, c (p ω) * ((r:ℂ)*incomingCommutatorMultiplier d (χ (p ω)).toFun 0
        (Real.log r/(2*d))) ∂ν) =
      ∑j, ((Measure.map p ν).real {j}:ℂ) *
        (c j * ((r:ℂ)*incomingCommutatorMultiplier d (χ j).toFun 0 (Real.log r/(2*d)))) := by
    simpa only [Complex.real_smul] using finite_angular_integral ν p hp
      (fun j => c j * ((r:ℂ)*incomingCommutatorMultiplier d (χ j).toFun 0 (Real.log r/(2*d))))
  simp_rw [hi]
  rw [finite_angular_integral ν p hp c]
  simp only [Complex.real_smul, ← mul_assoc]
  simpa only [← mul_assoc] using finite_cusp_radial_cancellation d hd χ τ hτ (fun j => ((Measure.map p ν).real {j}:ℂ)*c j)

end DedekindZetaZeroFree.KPCutoffSource

end
