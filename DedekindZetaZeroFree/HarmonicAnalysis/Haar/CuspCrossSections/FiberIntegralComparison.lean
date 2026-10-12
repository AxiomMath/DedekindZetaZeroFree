module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialTests
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.HorizontalAveraging
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.MeanZeroIntegration

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

variable {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}

theorem continuous_invariant_cross_integrable
    (G : KPCuspCharts.ChartOutput F hF S D)
    (f : KPCuspCharts.Cross F → ℝ) (hf : Continuous f)
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F), f (G.crossAction s x) = f x) :
    Integrable f ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
  have hrel : ∀ x y : KPCuspCharts.Cross F,
      KPCuspCharts.crossRelation F S x y → f x = f y := by
    intro x y hxy
    change MulAction.orbitRel S _ (KPCuspCharts.toArch F (x, 0))
      (KPCuspCharts.toArch F (y, 0)) at hxy
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp ((MulAction.orbitRel_apply).mp hxy)
    obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
    change KPCuspSiegel.action F s.val (KPCuspCharts.toArch F (y, 0)) =
      KPCuspCharts.toArch F (x, 0) at hs
    rw [G.actual_action s A hA hc] at hs
    have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective hs
    have hx : G.crossAction s y = x := by
      rw [G.crossAction_formula s A hA hc]
      exact congrArg Prod.fst hp
    rw [← hx]
    exact hinv s y
  let d : KPCuspCharts.CrossQuotient F S → ℝ := Quotient.lift f hrel
  have hd : Continuous d := hf.quotient_lift _
  letI := G.compact_cross
  letI := G.finite_sectionMeasure
  have hfinite : IsFiniteMeasure
      ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
    constructor
    have h := measure_lt_top G.sectionMeasure Set.univ
    rw [G.sectionMeasure_formula,
      Measure.map_apply measurable_quotient_mk'' MeasurableSet.univ] at h
    simpa using h
  letI := hfinite
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hd.continuousOn
  refine ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
  exact Filter.Eventually.of_forall fun x => hC (Quotient.mk _ x) (Set.mem_univ _)

theorem invariant_cross_section_bounded (G : KPCuspCharts.ChartOutput F hF S D)
    (f : KPCuspCharts.Cross F → ℝ) (hf : Continuous f)
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F), f (G.crossAction s x) = f x) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  have hrel : ∀ x y, KPCuspCharts.crossRelation F S x y → f x = f y := by
    intro x y hxy
    change MulAction.orbitRel S _ (KPCuspCharts.toArch F (x, 0))
      (KPCuspCharts.toArch F (y, 0)) at hxy
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp ((MulAction.orbitRel_apply).mp hxy)
    obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
    change KPCuspSiegel.action F s.val (KPCuspCharts.toArch F (y, 0)) =
      KPCuspCharts.toArch F (x, 0) at hs
    rw [G.actual_action s A hA hc] at hs
    have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective hs
    have hx : G.crossAction s y = x := by
      rw [G.crossAction_formula s A hA hc]
      exact congrArg Prod.fst hp
    rw [← hx]
    exact hinv s y
  let q : KPCuspCharts.CrossQuotient F S → ℝ := Quotient.lift f hrel
  have hq : Continuous q := hf.quotient_lift _
  letI := G.compact_cross
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hq.continuousOn
  refine ⟨C, fun x => ?_⟩
  exact
    hC (Quotient.mk (KPCuspCharts.crossRelation F S) x) (Set.mem_univ _)

theorem invariant_torus_slice_integrable
    {ρ : S →* rootsOfUnity 3 F}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ)) [IsFiniteMeasure μ]
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ)
    (hf : Continuous (fun x : KPCuspCharts.Cross F => f (QuotientAddGroup.mk x.1) x.2))
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      f (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        f (QuotientAddGroup.mk x.1) x.2)
    (b : KPCuspCharts.Shape F) : Integrable (fun z => f z b) μ := by
  have hm : Measurable (fun z => f z b) := by
    apply measurable_from_quotient.mpr
    exact (hf.comp (continuous_id.prodMk continuous_const)).measurable
  obtain ⟨C, hC⟩ := invariant_cross_section_bounded G _ hf hinv
  refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  exact hC (x, b)

theorem invariant_fiber_integral_comparison_of_horizontal_averaging
    {ρ : S →* rootsOfUnity 3 F}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ)) [IsFiniteMeasure μ]
    (haverage : ∀ (f : KPCuspGenuineMonodromy.KernelTorus S D ρ →
        KPCuspCharts.Shape F → ℝ),
      Continuous (fun x : KPCuspCharts.Cross F => f (QuotientAddGroup.mk x.1) x.2) →
      (∀ (s : S) (x : KPCuspCharts.Cross F),
        f (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
          f (QuotientAddGroup.mk x.1) x.2) →
      (∫ x : KPCuspCharts.Cross F, f (QuotientAddGroup.mk x.1) x.2
        ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) =
      ∫ x : KPCuspCharts.Cross F, (∫ z, f z x.2 ∂μ)
        ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain)
    (mass energy : KPCuspGenuineMonodromy.KernelTorus S D ρ →
      KPCuspCharts.Shape F → ℝ)
    (hmass : Continuous (fun x : KPCuspCharts.Cross F =>
      mass (QuotientAddGroup.mk x.1) x.2))
    (henergy : Continuous (fun x : KPCuspCharts.Cross F =>
      energy (QuotientAddGroup.mk x.1) x.2))
    (hmass_inv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      mass (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        mass (QuotientAddGroup.mk x.1) x.2)
    (henergy_inv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      energy (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        energy (QuotientAddGroup.mk x.1) x.2)
    (a : ℝ)
    (hfiber : ∀ b : KPCuspCharts.Shape F,
      a * (∫ z, mass z b ∂μ) ≤ ∫ z, energy z b ∂μ) :
    a * (∫ x : KPCuspCharts.Cross F, mass (QuotientAddGroup.mk x.1) x.2
      ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) ≤
    ∫ x : KPCuspCharts.Cross F, energy (QuotientAddGroup.mk x.1) x.2
      ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain := by
  let f := fun z b => energy z b - a * mass z b
  have hf : Continuous (fun x : KPCuspCharts.Cross F =>
      f (QuotientAddGroup.mk x.1) x.2) := henergy.sub (hmass.const_mul a)
  have hinv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      f (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        f (QuotientAddGroup.mk x.1) x.2 := by
    intro s x
    dsimp [f]
    rw [henergy_inv, hmass_inv]
  have havg := haverage f hf hinv
  have hnonneg : 0 ≤ ∫ x : KPCuspCharts.Cross F, (∫ z, f z x.2 ∂μ)
      ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain := by
    apply integral_nonneg
    intro x
    dsimp [f]
    rw [integral_sub (invariant_torus_slice_integrable G μ energy henergy henergy_inv x.2)
      ((invariant_torus_slice_integrable G μ mass hmass hmass_inv x.2).const_mul a),
      integral_const_mul]
    exact sub_nonneg.mpr (hfiber x.2)
  rw [← havg] at hnonneg
  dsimp [f] at hnonneg
  rw [integral_sub (continuous_invariant_cross_integrable G _ henergy henergy_inv)
    ((continuous_invariant_cross_integrable G _ hmass hmass_inv).const_mul a),
    integral_const_mul] at hnonneg
  exact sub_nonneg.mp hnonneg

theorem invariant_fiber_integral_comparison
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (mass energy : KPCuspGenuineMonodromy.KernelTorus S D ρ →
      KPCuspCharts.Shape F → ℝ)
    (hmass : Continuous (fun x : KPCuspCharts.Cross F =>
      mass (QuotientAddGroup.mk x.1) x.2))
    (henergy : Continuous (fun x : KPCuspCharts.Cross F =>
      energy (QuotientAddGroup.mk x.1) x.2))
    (hmass_inv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      mass (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        mass (QuotientAddGroup.mk x.1) x.2)
    (henergy_inv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      energy (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        energy (QuotientAddGroup.mk x.1) x.2)
    (a : ℝ)
    (hfiber : ∀ b : KPCuspCharts.Shape F,
      a * (∫ z, mass z b ∂μ) ≤ ∫ z, energy z b ∂μ) :
    a * (∫ x : KPCuspCharts.Cross F, mass (QuotientAddGroup.mk x.1) x.2
      ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) ≤
      ∫ x : KPCuspCharts.Cross F, energy (QuotientAddGroup.mk x.1) x.2
        ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain := by
  letI := hprob
  apply invariant_fiber_integral_comparison_of_horizontal_averaging G μ
    (mass := mass) (energy := energy) (a := a) _ hmass henergy hmass_inv henergy_inv hfiber
  intro f hf hinv
  obtain ⟨havg_cont, havg_inv⟩ :=
    horizontal_average_continuous_invariant G μ hμ hprob f hf hinv
  let avg : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ :=
    fun _ b => ∫ z, f z b ∂μ
  let residual := fun z b => f z b - avg z b
  have hres_cont : Continuous (fun x : KPCuspCharts.Cross F =>
      residual (QuotientAddGroup.mk x.1) x.2) := hf.sub havg_cont
  have havg_invariant : ∀ (s : S) (x : KPCuspCharts.Cross F),
      avg (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        avg (QuotientAddGroup.mk x.1) x.2 := havg_inv
  have hres_inv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      residual (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        residual (QuotientAddGroup.mk x.1) x.2 := by
    intro s x
    dsimp [residual]
    rw [hinv, havg_invariant]
  have hres_mean : ∀ b : KPCuspCharts.Shape F, (∫ z, residual z b ∂μ) = 0 := by
    intro b
    have hfint := invariant_torus_slice_integrable G μ f hf hinv b
    change (∫ z, f z b - (∫ w, f w b ∂μ) ∂μ) = 0
    rw [integral_sub hfint (integrable_const _)]
    simp
  have hvanish := invariant_zero_mean_fiber_integral G μ hμ hprob residual
    hres_cont hres_inv hres_mean
  have hfint := continuous_invariant_cross_integrable G _ hf hinv
  have havgint := continuous_invariant_cross_integrable G _ havg_cont havg_invariant
  change (∫ x : KPCuspCharts.Cross F,
    f (QuotientAddGroup.mk x.1) x.2 - avg (QuotientAddGroup.mk x.1) x.2
    ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) = 0 at hvanish
  rw [integral_sub hfint havgint] at hvanish
  exact sub_eq_zero.mp hvanish

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end
