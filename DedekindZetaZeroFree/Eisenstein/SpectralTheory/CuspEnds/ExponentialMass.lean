module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.OutgoingZeroModeTails

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

theorem end_exponential_mass_finite
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (a : KPContActualChamberOutgoingAdapter.Cusps F ζ hζ C R P H U)
    (κ : ℝ) (hκ : κ < 2 * (KPCuspLogShape.dimension F : ℝ)) (T : ℝ) :
    (∫⁻ p in {p : KPCuspCharts.Coordinates F | T < p.2},
      ENNReal.ofReal (Real.exp (κ * p.2))
      ∂KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a) < ∞ := by
  let G := KPContActualChamberOutgoingAdapter.geometry F ζ hζ C R P H U a
  let μ : Measure (KPCuspCharts.Cross F) :=
    (volume : Measure (KPCuspCharts.Horizontal F)).prod G.shapeMeasure
  let A := G.fundamentalDomain
  let ν := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)
  let w := (H.disintegration (KPContActualChamberOutgoingAdapter.level F ζ hζ C R P H U)).componentWeight a.1
  have hrad : (∫⁻ t in Set.Ioi T, ENNReal.ofReal (Real.exp (κ*t)) ∂ν) < ∞ := by
    dsimp [ν, KPCuspCharts.radialMeasure]
    rw [restrict_withDensity measurableSet_Ioi]
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    have he : (fun t : ℝ => ENNReal.ofReal (Real.exp (-2 * (KPCuspLogShape.dimension F : ℝ) * t)) *
        ENNReal.ofReal (Real.exp (κ*t))) =
        (fun t => ENNReal.ofReal (Real.exp ((κ-2*(KPCuspLogShape.dimension F : ℝ))*t))) := by
      funext t
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    simp only [Pi.mul_apply]
    rw [he, ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_exp_mul_Ioi (by linarith : κ-2*(KPCuspLogShape.dimension F : ℝ) < 0) T)
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_lt_top
  letI := KPCompactGreen.fundamentalDomain_finiteMeasure G
  have hμ : μ A < ∞ := by
    change (volume.prod G.shapeMeasure) G.fundamentalDomain < ∞
    rw [← Measure.restrict_apply_univ G.fundamentalDomain]
    exact measure_lt_top _ _
  letI := G.haar_shapeMeasure
  letI : SFinite μ := by dsimp [μ]; infer_instance
  letI : SFinite ν := by dsimp [ν, KPCuspCharts.radialMeasure]; infer_instance
  have hm : ((μ.prod ν).restrict {p : KPCuspCharts.Coordinates F | p.1 ∈ A}).restrict
      {p | T < p.2} = (μ.restrict A).prod (ν.restrict (Set.Ioi T)) := by
    have ht : MeasurableSet {p : KPCuspCharts.Coordinates F | T < p.2} :=
      measurableSet_Ioi.preimage measurable_snd
    rw [Measure.restrict_restrict ht, Measure.prod_restrict]
    congr 1
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioi]
    exact and_comm
  change (∫⁻ p in {p : KPCuspCharts.Coordinates F | T < p.2},
    ENNReal.ofReal (Real.exp (κ*p.2)) ∂w • ((μ.prod ν).restrict {p | p.1 ∈ A})) < ∞
  rw [Measure.restrict_smul, lintegral_smul_measure]
  rw [hm, lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top ((H.disintegration _).finite_componentWeight a.1)
    (ENNReal.mul_lt_top hrad hμ)

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
