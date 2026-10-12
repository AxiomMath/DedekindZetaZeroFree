module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicTraceQuotientCompatibility
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.BruhatTwoCellIntegral

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal DedekindZetaZeroFree.KPAdditiveFundamentalDomain
open MeasureTheory NumberField
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
namespace DedekindZetaZeroFree.KPLiteralChamberWeight
open KPLiteralRaw KPLiteralChamber
open KPGlobalResidualKernel.RawStageL2.Outgoing
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem standard_measurable (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (g : G F ζ hζ) :
    Measurable (fun x : KPAdeles F => f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)) := by
  exact ((f.property.1 s).1.1.comp
    ((continuous_const.mul (KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F ζ hζ)).mul continuous_const)).measurable

private theorem open_cell_term (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (t : F) (x : KPAdeles F) (g : G F ζ hζ) :
    f.val s (rationalLift F ζ hζ
      (Quotient.out (KPChamberBruhatTwoCells.cellIndex F (some t))) *
        (KPGlobalTorusFunctionData.N F ζ hζ x * g)) =
    f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
      KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F (KPAdeles F) t + x) * g) := by
  change f.val s (rationalLift F ζ hζ
    (Quotient.out (KPChamberBruhatTwoCells.rationalCoset F
      (KPChamberBruhatTwoCells.rationalWeyl F * KPChamberBruhatTwoCells.rationalUnipotent F t))) * _) = _
  rw [KPLiteralExceptionalResidue.val_rationalCoset_out_eq, KPLiteralExceptionalResidue.rationalLift_eq_constructed]
  have h := KPChamberBruhatTwoCells.open_cell_translate F (ActualBruhat.rational F ζ hζ)
    (KPGlobalTorusFunctionData.Nhom F ζ hζ) (ActualBruhat.compatible_unipotent F ζ hζ)
    (f.val s) t x g
  have hw := ActualBruhat.section_signed_weyl F ζ hζ s
    (literalSource F ζ hζ K f s)
    (KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F (KPAdeles F) t + x) * g)
  change f.val s (ActualBruhat.rational F ζ hζ
    (KPChamberBruhatTwoCells.rationalWeyl F * KPChamberBruhatTwoCells.rationalUnipotent F t) *
    (KPGlobalTorusFunctionData.N F ζ hζ x * g)) = _
  dsimp only [KPGlobalTorusFunctionData.Nhom, MonoidHom.coe_mk, OneHom.coe_mk] at h
  simp only [toAdd_ofAdd] at h
  rw [← mul_assoc, h]
  simpa only [literalSource, KPRationalAdelicSplitting.pglW, mul_assoc] using hw

theorem standard_integrable (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    Integrable (fun x : KPAdeles F => f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g))
      (KPAdditiveHaar.adelicMeasure F) := by
  letI := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let D := KPAdditiveFundamentalDomain.domain F
  let C : Set (KPAdeles F) := closure (KPAdditiveFundamentalDomain.archParallelepiped F) ×ˢ
    (KPAdelicTopology.integralAdeles F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  have hC : IsCompact C := KPAdditiveFundamentalDomain.compact_closed_cover F
  have hDC : D ⊆ C := fun x hx => ⟨subset_closure hx.1, hx.2⟩
  let A := (fun x : KPAdeles F => KPGlobalTorusFunctionData.N F ζ hζ x * g) '' C
  have hA : IsCompact A := hC.image
    ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ).mul
      continuous_const)
  obtain ⟨b, hb, hbound⟩ := chamber_scalar_compact_majorants F ζ hζ K hK f {s}
    isCompact_singleton (by rintro z rfl; exact hs) A hA
  let h : KPAdeles F → ℂ := fun x => f.val s
    (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
  have hh : Measurable h := standard_measurable F ζ hζ K f s g
  have hsum_bound : ∀ x ∈ D,
      (∑' t : F, ENNReal.ofReal ‖h (algebraMap F (KPAdeles F) t + x)‖) ≤
        ENNReal.ofReal (∑' q, |b q|) := by
    intro x hx
    let e : F → KPChamberBruhatTwoCells.RationalQuotient F :=
      fun t => KPChamberBruhatTwoCells.cellIndex F (some t)
    have he : Function.Injective e :=
      (KPChamberBruhatTwoCells.cellIndex_bijective F).1.comp (Option.some_injective F)
    have ht : ∀ t, ‖h (algebraMap F (KPAdeles F) t + x)‖ ≤ |b (e t)| := by
      intro t
      have hq := hbound (e t) s rfl (KPGlobalTorusFunctionData.N F ζ hζ x * g)
        ⟨x, hDC hx, rfl⟩
      rw [open_cell_term] at hq
      exact hq.trans (le_abs_self _)
    calc
      _ ≤ ∑' t : F, ENNReal.ofReal |b (e t)| :=
        ENNReal.tsum_le_tsum (fun t => ENNReal.ofReal_le_ofReal (ht t))
      _ ≤ ∑' q, ENNReal.ofReal |b q| := ENNReal.tsum_comp_le_tsum_of_injective he (fun q => ENNReal.ofReal |b q|)
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun q => abs_nonneg _) hb.abs).symm
  letI : MeasurableConstVAdd F (KPAdeles F) := ⟨fun t =>
    (measurable_const.add measurable_id : Measurable
      (fun x : KPAdeles F => algebraMap F (KPAdeles F) t + x))⟩
  letI : VAddInvariantMeasure F (KPAdeles F) (KPAdditiveHaar.adelicMeasure F) := ⟨fun t a ha => by
    have hp := measurePreserving_add_left (KPAdditiveHaar.adelicMeasure F)
      (algebraMap F (KPAdeles F) t)
    exact hp.measure_preimage ha.nullMeasurableSet⟩
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hfd := KPAdditiveFundamentalDomain.isAddFundamentalDomain F (KPAdditiveHaar.adelicMeasure F)
  have hfinite : (∫⁻ x : KPAdeles F, ENNReal.ofReal ‖h x‖ ∂KPAdditiveHaar.adelicMeasure F) < ⊤ := by
    rw [hfd.lintegral_eq_tsum'']
    rw [← lintegral_tsum]
    · have hle : (∫⁻ x in D, ∑' t : F, ENNReal.ofReal ‖h (algebraMap F (KPAdeles F) t + x)‖
          ∂KPAdditiveHaar.adelicMeasure F) ≤
          ∫⁻ x in D, ENNReal.ofReal (∑' q, |b q|) ∂KPAdditiveHaar.adelicMeasure F := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (KPAdditiveFundamentalDomain.domain_measurableSet F)] with x hx
        exact hsum_bound x hx
      apply lt_of_le_of_lt hle
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top
        (KPAdditiveFundamentalDomain.domain_mass F (KPAdditiveHaar.adelicMeasure F)).2
    · intro t
      exact (hh.comp (measurable_const.add measurable_id)).norm.ennreal_ofReal.aemeasurable
  exact ⟨hh.aestronglyMeasurable,
    by simpa only [HasFiniteIntegral, ofReal_norm] using hfinite⟩

private theorem literal_two_cells_probability (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    (∫ q : KPAdditiveQuotient F,
      eisenstein F ζ hζ K f s
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)
      ∂KPWildKernelUpperBound.quotientHaar F) =
    f.val s g + ∫ x : KPAdeles F, f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
      ∂KPAdditiveHaar.adelicMeasure F := by
  letI := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  have hsum : ∀ q : KPAdditiveQuotient F,
      KPGlobalEisensteinData.EisensteinSummable
        (fun c : KPChamberBruhatTwoCells.RationalQuotient F => ActualBruhat.rational F ζ hζ (Quotient.out c))
        (f.val s) (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) := by
    intro q
    obtain ⟨b, hb, hbound⟩ := chamber_scalar_compact_majorants F ζ hζ K hK f {s}
      isCompact_singleton (by rintro z rfl; exact hs)
      {KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g} isCompact_singleton
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hb
    intro c
    simpa only [KPLiteralExceptionalResidue.rationalLift_eq_constructed] using hbound c s rfl _ rfl
  have h := ActualBruhat.integral_two_cells F ζ hζ s (literalSource F ζ hζ K f s)
    (KPAdditiveHaar.adelicMeasure F) (KPWildKernelUpperBound.quotientHaar F)
    (KPContinuation.ChamberOutgoingSource.actual_quotientHaar_compatible F) g hsum
    (standard_measurable F ζ hζ K f s g) (standard_integrable F ζ hζ K hK f s hs g)
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with q
    unfold eisenstein KPGlobalEisensteinData.eisenstein
    apply tsum_congr
    intro c
    rw [KPLiteralExceptionalResidue.rationalLift_eq_constructed]
    rfl
  · rfl

theorem literal_two_cells (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (μ : Measure (KPAdditiveQuotient F))
    (hμ : μ.IsAddHaarMeasure) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    (∫ q : KPAdditiveQuotient F,
      eisenstein F ζ hζ K f s
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂μ) =
    (μ.real Set.univ : ℂ) * (f.val s g + ∫ x : KPAdeles F, f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
      ∂KPAdditiveHaar.adelicMeasure F) := by
  letI := hμ
  letI : CompactSpace (KPAdditiveQuotient F) :=
    (additiveAdeleQuotient_compactHausdorff F).1
  let dq := KPWildKernelUpperBound.quotientHaar F
  have hscale := Measure.isAddInvariant_eq_smul_of_compactSpace μ dq
  have hm : μ.real Set.univ = (μ.addHaarScalarFactor dq : ℝ) := by
    conv_lhs => rw [hscale]
    simp [Measure.real, dq]
  rw [hm]
  conv_lhs => rw [hscale]
  rw [integral_smul_nnreal_measure]
  rw [literal_two_cells_probability F ζ hζ K hK f s hs g]
  rfl

end DedekindZetaZeroFree.KPLiteralChamberWeight

end
