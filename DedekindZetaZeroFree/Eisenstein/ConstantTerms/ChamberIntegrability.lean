module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberWeightUnfolding

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory NumberField
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.Chamber
open KPLiteralRaw KPLiteralChamber
open KPGlobalResidualKernel.RawStageL2.Outgoing
open _root_.DedekindZetaZeroFree.KPLiteralChamberWeight renaming standard_measurable → standard_measurable
open _root_.DedekindZetaZeroFree.KPLiteralChamberWeight renaming standard_integrable → standard_integrable

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem upper_integrable_probability (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : G F ζ hζ) :
    Integrable (fun q : KPAdditiveQuotient F => eisenstein F ζ hζ K f s
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g))
      (KPWildKernelUpperBound.quotientHaar F) := by
  letI := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let dq := KPWildKernelUpperBound.quotientHaar F
  let h : KPAdeles F → ℂ := fun x => f.val s
    (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
  have hp := (BruhatIntegral.integral_period_of_integrable F
    (KPAdditiveHaar.adelicMeasure F) dq
    (KPContinuation.ChamberOutgoingSource.actual_quotientHaar_compatible F) h
    (standard_measurable F ζ hζ K f s g)
    (standard_integrable F ζ hζ K hK f s hs g)).1
  have hsum (q : KPAdditiveQuotient F) :
      KPGlobalEisensteinData.EisensteinSummable
        (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
          ActualBruhat.rational F ζ hζ (Quotient.out c))
        (f.val s) (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) := by
    obtain ⟨b, hb, hbound⟩ := chamber_scalar_compact_majorants F ζ hζ K hK f {s}
      isCompact_singleton (by rintro z rfl; exact hs)
      {KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g} isCompact_singleton
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hb
    intro c
    simpa only [KPLiteralExceptionalResidue.rationalLift_eq_constructed] using hbound c s rfl _ rfl
  have hformula (q : KPAdditiveQuotient F) :
      eisenstein F ζ hζ K f s (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) =
        f.val s g + KPChamberAdditivePeriodization.complexPeriod F h q := by
    have he : eisenstein F ζ hζ K f s
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) =
        KPGlobalEisensteinData.eisenstein
          (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
            ActualBruhat.rational F ζ hζ (Quotient.out c)) (f.val s)
          (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) (hsum q) := by
      unfold eisenstein KPGlobalEisensteinData.eisenstein
      apply tsum_congr
      intro c
      rw [KPLiteralExceptionalResidue.rationalLift_eq_constructed]
    rw [he, KPChamberBruhatTwoCells.eisenstein_two_cells F
      (ActualBruhat.rational F ζ hζ) (f.val s)
      (KPLiteralExceptionalResidue.literal_scalar_rational_borel_invariant F ζ hζ K f s)]
    rw [KPLiteralExceptionalResidue.val_N_invariant]
    congr 1
    apply tsum_congr
    intro t
    have ht := KPChamberBruhatTwoCells.open_cell_translate F (ActualBruhat.rational F ζ hζ)
      (KPGlobalTorusFunctionData.Nhom F ζ hζ) (ActualBruhat.compatible_unipotent F ζ hζ)
      (f.val s) t (Quotient.out q) g
    dsimp only [KPGlobalTorusFunctionData.Nhom, MonoidHom.coe_mk, OneHom.coe_mk] at ht
    simp only [toAdd_ofAdd] at ht
    rw [← mul_assoc, ht]
    have hw := ActualBruhat.section_signed_weyl F ζ hζ s
      (literalSource F ζ hζ K f s)
      (KPGlobalTorusFunctionData.N F ζ hζ
        (algebraMap F (KPAdeles F) t + Quotient.out q) * g)
    simpa only [h, literalSource, KPRationalAdelicSplitting.pglW, mul_assoc] using hw
  exact ((integrable_const (f.val s g)).add hp).congr
    (Filter.Eventually.of_forall fun q => (hformula q).symm)

theorem upper_integrable (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : G F ζ hζ) :
    Integrable (fun q : KPAdditiveQuotient F => eisenstein F ζ hζ K f s
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g)) μ := by
  letI := hμ
  letI : CompactSpace (KPAdditiveQuotient F) :=
    (additiveAdeleQuotient_compactHausdorff F).1
  let dq := KPWildKernelUpperBound.quotientHaar F
  rw [Measure.isAddInvariant_eq_smul_of_compactSpace μ dq]
  exact (upper_integrable_probability F ζ hζ K hK f s hs g).smul_measure
    ENNReal.coe_ne_top

end DedekindZetaZeroFree.CompactPeriodAnalyticity.Chamber

end
