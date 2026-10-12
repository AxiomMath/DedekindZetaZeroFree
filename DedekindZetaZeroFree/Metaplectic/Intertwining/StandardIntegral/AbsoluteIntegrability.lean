module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Bruhat.OpenCellSummand
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicTraceQuotientCompatibility

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal DedekindZetaZeroFree.KPAdditiveFundamentalDomain
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

theorem actual_standard_integrable
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    KPGlobalEisensteinData.IntertwinerIntegrable (KPAdditiveHaar.adelicMeasure F)
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ))
      (KPGlobalTorusFunctionData.N F ζ hζ)
      (KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)) g := by
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let D := KPAdditiveFundamentalDomain.domain F
  let K : Set (Adeles F) := closure (KPAdditiveFundamentalDomain.archParallelepiped F) ×ˢ
    (KPAdelicTopology.integralAdeles F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  have hK : IsCompact K := KPAdditiveFundamentalDomain.compact_closed_cover F
  have hDK : D ⊆ K := by
    intro x hx
    exact ⟨subset_closure hx.1, hx.2⟩
  let A := (fun x : Adeles F => KPGlobalTorusFunctionData.N F ζ hζ x * g) '' K
  have hN := KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ
  have hA : IsCompact A := hK.image (hN.mul continuous_const)
  obtain ⟨b, hb, hbound⟩ := KPContActualChamberNormalSeries.normal_majorant F ζ hζ U ι f
    hι hf 0 [] {s} isCompact_singleton (by rintro z rfl; exact hs) A hA
  let h : Adeles F → ℂ := fun x => KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
    (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
  have hh : Measurable h := standard_measurable F ζ hζ U ι s (f s) g
  have hsum_bound : ∀ x ∈ D,
      (∑' t : F, ENNReal.ofReal ‖h (algebraMap F (Adeles F) t + x)‖) ≤
        ENNReal.ofReal (∑' q, (b q : ℝ)) := by
    intro x hx
    let e : F → KPChamberBruhatTwoCells.RationalQuotient F :=
      fun t => KPChamberBruhatTwoCells.cellIndex F (some t)
    have he : Function.Injective e :=
      (KPChamberBruhatTwoCells.cellIndex_bijective F).1.comp (Option.some_injective F)
    have ht : ∀ t, ‖h (algebraMap F (Adeles F) t + x)‖ ≤ (b (e t) : ℝ) := by
      intro t
      have hq := hbound (e t) s rfl (KPGlobalTorusFunctionData.N F ζ hζ x * g)
        ⟨x, hDK hx, rfl⟩
      simpa only [KPContActualChamberNormalSeries.mixedJet,
        KPContActualChamberNormalSeries.rightWord, List.foldr_nil, iteratedDerivWithin_zero,
        KPContActualChamberNormalSeries.term, e, open_cell_term, h] using hq
    calc
      _ ≤ ∑' t : F, ENNReal.ofReal (b (e t) : ℝ) := ENNReal.tsum_le_tsum (fun t => ENNReal.ofReal_le_ofReal (ht t))
      _ ≤ ∑' q, ENNReal.ofReal (b q : ℝ) := ENNReal.tsum_comp_le_tsum_of_injective he (fun q => ENNReal.ofReal (b q : ℝ))
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun q => (b q).coe_nonneg) hb).symm
  letI : MeasurableConstVAdd F (Adeles F) := ⟨fun t =>
    (measurable_const.add measurable_id : Measurable
      (fun x : Adeles F => algebraMap F (Adeles F) t + x))⟩
  letI : VAddInvariantMeasure F (Adeles F) (KPAdditiveHaar.adelicMeasure F) := ⟨fun t s hs => by
    have hp := measurePreserving_add_left (KPAdditiveHaar.adelicMeasure F)
      (algebraMap F (Adeles F) t)
    exact hp.measure_preimage hs.nullMeasurableSet⟩
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hfd := KPAdditiveFundamentalDomain.isAddFundamentalDomain F
    (KPAdditiveHaar.adelicMeasure F)
  have hfinite : (∫⁻ x : Adeles F, ENNReal.ofReal ‖h x‖ ∂KPAdditiveHaar.adelicMeasure F) < ⊤ := by
    rw [hfd.lintegral_eq_tsum'']
    rw [← lintegral_tsum]
    · have hle : (∫⁻ x in D, ∑' t : F, ENNReal.ofReal ‖h (algebraMap F (Adeles F) t + x)‖
          ∂KPAdditiveHaar.adelicMeasure F) ≤
          ∫⁻ x in D, ENNReal.ofReal (∑' q, (b q : ℝ)) ∂KPAdditiveHaar.adelicMeasure F := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (KPAdditiveFundamentalDomain.domain_measurableSet F)] with x hx
        exact hsum_bound x hx
      apply lt_of_le_of_lt hle
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top
        (KPAdditiveFundamentalDomain.domain_mass F (KPAdditiveHaar.adelicMeasure F)).2
    · intro t
      exact (hh.comp (measurable_const.add measurable_id)).norm.ennreal_ofReal.aemeasurable
  exact ⟨hh.aestronglyMeasurable, by simpa only [HasFiniteIntegral, ofReal_norm_eq_enorm] using hfinite⟩

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
