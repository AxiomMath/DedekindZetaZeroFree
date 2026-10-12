module

public import DedekindZetaZeroFree.Adeles.Quotients.SmoothLocalCharts
public import DedekindZetaZeroFree.Adeles.Quotients.LocalCharts.CompactLiftL2Bounds

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped ENNReal Classical Pointwise
namespace DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

theorem pushforward_le_of_orbit_multiplicity {G X Q : Type*}
    [Group G] [MulAction G X] [MeasurableSpace X] [MeasurableSpace Q]
    [Countable G] [MeasurableConstSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (D : Set X) (hD : IsFundamentalDomain G D μ)
    (q : X → Q) (hq : Measurable q) (hqin : ∀ γ : G, ∀ x, q (γ • x) = q x)
    (C : Set X) (hC : MeasurableSet C) (N : ℕ)
    (hN : ∀ x, (∑' γ : G, C.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) ≤ N) :
    Measure.map q (μ.restrict C) ≤ (N : ℝ≥0∞) • Measure.map q (μ.restrict D) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply hq hS, Measure.restrict_apply (hq hS),
    Measure.smul_apply, smul_eq_mul, Measure.map_apply hq hS,
    Measure.restrict_apply (hq hS)]
  let f : X → ℝ≥0∞ := (q ⁻¹' S ∩ C).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator ((hq hS).inter hC)
  rw [← lintegral_indicator_one ((hq hS).inter hC)]
  change (∫⁻ x, f x ∂μ) ≤ _
  rw [hD.lintegral_eq_tsum'' f]
  have hft : ∀ γ : G, AEMeasurable (fun x => f (γ • x)) (μ.restrict D) :=
    fun γ => (hf.comp (measurable_const_smul γ)).aemeasurable
  rw [← lintegral_tsum hft]
  calc
    (∫⁻ x in D, ∑' γ : G, f (γ • x) ∂μ) ≤
        ∫⁻ x in D, (q ⁻¹' S).indicator (fun _ => (N : ℝ≥0∞)) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : q x ∈ S
      · rw [Set.indicator_of_mem (show x ∈ q ⁻¹' S from hx)]
        exact (ENNReal.tsum_le_tsum (fun γ => by
          by_cases hc : γ • x ∈ C
          · simp [f, Set.indicator_apply, hc, hqin, hx]
          · simp [f, Set.indicator_apply, hc])).trans (hN x)
      · have hz : ∀ γ : G, f (γ • x) = 0 := by
          intro γ
          exact Set.indicator_of_notMem (by
            intro h; exact hx (hqin γ x ▸ h.1)) _
        simp only [hz, tsum_zero]
        exact bot_le
    _ = (N : ℝ≥0∞) * μ (q ⁻¹' S ∩ D) := by
      rw [lintegral_indicator (hq hS), lintegral_const,
        Measure.restrict_restrict (hq hS), Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]

theorem compact_haar_recipe_pushforward_bound (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (C : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ)) (hC : IsCompact C) :
    ∃ N : ℕ, Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
      (R.adelicHaar.restrict C) ≤ (N : ℝ≥0∞) • R.quotientHaar := by
  letI : IsTopologicalGroup (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI : LocallyCompactSpace (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI : T2Space (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI : SecondCountableTopology (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : BorelSpace (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) := ⟨rfl⟩
  letI : BorelSpace (KPSmoothLocalQuotientCharts.X F ζ hζ) := ⟨rfl⟩
  letI : R.adelicHaar.IsHaarMeasure := R.adelic_isHaar
  let Γ := KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ
  haveI : Countable Γ := by
    have hd := (ActualQuotient.actual_rational_closed_discrete F ζ hζ).2
    exact (IsLindelof.countable_of_isDiscrete
      (ActualQuotient.actual_rational_closed_discrete F ζ hζ).1.isLindelof hd).to_subtype
  obtain ⟨N, hN⟩ :=
    KPSmoothAutomorphicEvaluation.OrbitTubeComparison.compact_orbit_indicator_bound Γ
      (ActualQuotient.actual_rational_closed_discrete F ζ hζ).1
      (ActualQuotient.actual_rational_closed_discrete F ζ hζ).2 C hC
  refine ⟨N, ?_⟩
  rw [← R.quotient_normalization]
  apply pushforward_le_of_orbit_multiplicity R.adelicHaar R.domain R.domain_fundamental
    (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) continuous_quotient_mk'.measurable
    _ C hC.isClosed.measurableSet N
  · exact hN
  · intro γ g
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    change g * ((γ : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * g)⁻¹ ∈ Γ
    simpa only [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] using Γ.inv_mem γ.property

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
