module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberWeightUnfolding
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAbsoluteConvergence

@[expose] public section

noncomputable section
open MeasureTheory NumberField
open scoped NumberField ENNReal
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPLiteralResidueKernelTests.FiniteFactorSplit.FourierChamber
open KPCompactFourier (char_integral_zero)
variable (F : Type) [Field F] [NumberField F]
 abbrev A := NumberField.AdeleRing (𝓞 F) F
 abbrev Q := A F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F

private theorem weighted_period (dx : Measure (A F)) (dq : Measure (Q F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [IsProbabilityMeasure dq]
    (hcompat : KPChamberAdditivePeriodization.CompatibleHaar F dx dq)
    (h : A F → ℂ) (hmeas : Measurable h) (hint : Integrable h dx)
    (χ : AddChar (Q F) Circle) (hχ : Continuous χ) :
    Integrable (fun q : Q F => KPChamberAdditivePeriodization.complexPeriod F h q *
      star (χ q : ℂ)) dq ∧
    (∫ q : Q F, KPChamberAdditivePeriodization.complexPeriod F h q * star (χ q : ℂ) ∂dq) =
      ∫ x : A F, h x * star (χ (QuotientAddGroup.mk x) : ℂ) ∂dx := by
  let w : A F → ℂ := fun x => h x * star (χ (QuotientAddGroup.mk x) : ℂ)
  have hc : Continuous (fun x : A F => star (χ (QuotientAddGroup.mk x) : ℂ)) :=
    (continuous_subtype_val.comp hχ).comp QuotientAddGroup.continuous_mk |>.star
  have hwmeas : Measurable w := hmeas.mul hc.measurable
  have hwint : Integrable w dx :=
    hint.mul_bdd hc.aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall (by
      intro x
      simp [Circle.norm_coe]))
  have htw := (KPChamberAdditivePeriodization.lintegral_nonnegativePeriod F dx dq hcompat
      (fun x => ENNReal.ofReal ‖w x‖) hwmeas.norm.ennreal_ofReal)
  have hfinite : ∫⁻ q : Q F, KPChamberAdditivePeriodization.normPeriod F w q ∂dq < ⊤ := by
    rw [show (fun q : Q F => KPChamberAdditivePeriodization.normPeriod F w q) =
        (fun q : Q F => KPChamberAdditivePeriodization.nonnegativePeriod F
          (fun x => ENNReal.ofReal ‖w x‖) q) from rfl, htw]
    simpa only [ofReal_norm, HasFiniteIntegral] using hwint.hasFiniteIntegral
  have hi := (KPChamberAdditivePeriodization.integral_complexPeriod F dx dq hcompat
    w hwmeas hfinite).2.2
  have hweq (q : Q F) : KPChamberAdditivePeriodization.complexPeriod F w q =
      KPChamberAdditivePeriodization.complexPeriod F h q * star (χ q : ℂ) := by
    have hmk : (QuotientAddGroup.mk (Quotient.out q : A F) : Q F) = q := Quotient.out_eq _
    unfold KPChamberAdditivePeriodization.complexPeriod
    simp only [w]
    have hs (t : F) :
        (χ (QuotientAddGroup.mk ((algebraMap F (A F)) t + (Quotient.out q : A F))) : ℂ) = (χ q : ℂ) := by
      have hz : (QuotientAddGroup.mk ((algebraMap F (A F)) t) : Q F) = 0 := by
        exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨t, rfl⟩
      rw [QuotientAddGroup.mk_add, hz, zero_add, hmk]
    simp_rw [hs]
    exact tsum_mul_right
  have heq : KPChamberAdditivePeriodization.complexPeriod F w =
      (fun q => KPChamberAdditivePeriodization.complexPeriod F h q * star (χ q : ℂ)) := funext hweq
  rw [heq] at hi
  exact hi
private theorem two_cells_weighted
    {G : Type*} [Group G]
    (r : Matrix.ProjGenLinGroup (Fin 2) F →* G)
    (n : Multiplicative (A F) →* G) (f : G → ℂ)
    (hB : KPChamberBruhatTwoCells.ScalarRationalBorelInvariant F r f)
    (hN : KPChamberBruhatTwoCells.ScalarUnipotentInvariant F n f)
    (hlift : KPChamberBruhatTwoCells.CompatibleUnipotentLift F r n)
    (dx : Measure (A F)) (dq : Measure (Q F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [IsProbabilityMeasure dq]
    (hcompat : KPChamberAdditivePeriodization.CompatibleHaar F dx dq)
    (g : G)
    (hsum : ∀ q : Q F, KPGlobalEisensteinData.EisensteinSummable
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => r (Quotient.out c))
      f (n (Multiplicative.ofAdd (Quotient.out q)) * g))
    (hmeas : Measurable (fun x : A F => f (r (KPChamberBruhatTwoCells.rationalWeyl F) *
      n (Multiplicative.ofAdd x) * g)))
    (hint : Integrable (fun x : A F => f (r (KPChamberBruhatTwoCells.rationalWeyl F) *
      n (Multiplicative.ofAdd x) * g)) dx)
    (χ : AddChar (Q F) Circle) (hχ : Continuous χ) (hne : χ ≠ 1) :
    (∫ q : Q F, KPGlobalEisensteinData.eisenstein
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => r (Quotient.out c))
      f (n (Multiplicative.ofAdd (Quotient.out q)) * g) (hsum q) * star (χ q : ℂ) ∂dq) =
    ∫ x : A F, f (r (KPChamberBruhatTwoCells.rationalWeyl F) *
      n (Multiplicative.ofAdd x) * g) * star (χ (QuotientAddGroup.mk x) : ℂ) ∂dx := by
  let h : A F → ℂ := fun x => f (r (KPChamberBruhatTwoCells.rationalWeyl F) *
    n (Multiplicative.ofAdd x) * g)
  have hp := weighted_period F dx dq hcompat h hmeas hint χ hχ
  have hformula (q : Q F) : KPGlobalEisensteinData.eisenstein
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => r (Quotient.out c))
      f (n (Multiplicative.ofAdd (Quotient.out q)) * g) (hsum q) =
      f g + KPChamberAdditivePeriodization.complexPeriod F h q := by
    rw [KPChamberBruhatTwoCells.eisenstein_two_cells F r f hB, hN]
    congr 1
    apply tsum_congr
    intro t
    simpa only [h, mul_assoc] using
      KPChamberBruhatTwoCells.open_cell_translate F r n hlift f t (Quotient.out q) g
  have hi : Integrable (fun q : Q F => f g * star (χ q : ℂ)) dq := by
    apply Integrable.const_mul
    exact (((continuous_subtype_val.comp hχ).star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hz : (∫ q : Q F, star (χ q : ℂ) ∂dq) = 0 := by
    change (∫ q : Q F, (starRingEnd ℂ) (χ q : ℂ) ∂dq) = 0
    rw [integral_conj, KPCompactFourier.char_integral_zero dq χ hne, map_zero]
  simp_rw [hformula, add_mul]
  rw [integral_add hi hp.1, integral_const_mul, hz, mul_zero, zero_add, hp.2]

open KPLiteralRaw KPLiteralChamber
open KPGlobalResidualKernel.RawStageL2.Outgoing
open KPLiteralChamberWeight (standard_measurable standard_integrable)

theorem literal_nontrivial_fourier_unfolding
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (z : ℂ) (hz : (1 : ℝ) / 3 < z.re)
    (χ : AddChar (KPAdditiveQuotient F) Circle) (hχ : Continuous χ) (hne : χ ≠ 1)
    (g : G F ζ hζ) :
    (∫ y : KPAdditiveQuotient F, eisenstein F ζ hζ K f z
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out y) * g) * star (χ y : ℂ)
        ∂KPWildKernelUpperBound.quotientHaar F) =
      ∫ x : KPAdeles F, f.val z (KPRationalAdelicSplitting.pglW F ζ hζ *
        KPGlobalTorusFunctionData.N F ζ hζ x * g) * star (χ (QuotientAddGroup.mk x) : ℂ)
        ∂KPAdditiveHaar.adelicMeasure F := by
  letI : CompactSpace (KPAdditiveQuotient F) :=
    (additiveAdeleQuotient_compactHausdorff F).1
  letI : T2Space (KPAdditiveQuotient F) :=
    (additiveAdeleQuotient_compactHausdorff F).2
  letI := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let r := ActualBruhat.rational F ζ hζ
  let n := KPGlobalTorusFunctionData.Nhom F ζ hζ
  let v := literalSource F ζ hζ K f z
  have hsum (y : KPAdditiveQuotient F) :
      KPGlobalEisensteinData.EisensteinSummable
        (fun c : KPChamberBruhatTwoCells.RationalQuotient F => r (Quotient.out c))
        (f.val z) (n (Multiplicative.ofAdd (Quotient.out y)) * g) := by
    simpa only [KPGlobalEisensteinData.EisensteinSummable, r,
      ← KPLiteralExceptionalResidue.rationalLift_eq_constructed] using
      (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK f z hz
        (n (Multiplicative.ofAdd (Quotient.out y)) * g)).norm
  have heq : (fun x : KPAdeles F => f.val z
      (r (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd x) * g)) =
      (fun x : KPAdeles F => f.val z (KPRationalAdelicSplitting.pglW F ζ hζ *
        KPGlobalTorusFunctionData.N F ζ hζ x * g)) := by
    funext x
    simpa only [r, n, v, literalSource, mul_assoc, KPRationalAdelicSplitting.pglW,
      KPCubicCoverConstruction.adelicW, KPGlobalTorusFunctionData.Nhom,
      MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] using
      ActualBruhat.section_signed_weyl F ζ hζ z v
        (KPGlobalTorusFunctionData.N F ζ hζ x * g)
  have hm := standard_measurable F ζ hζ K f z g
  have hi := standard_integrable F ζ hζ K hK f z hz g
  have h := two_cells_weighted F r n (f.val z)
    (ActualBruhat.scalar_rational_borel_invariant F ζ hζ z v)
    (ActualBruhat.scalar_unipotent_invariant F ζ hζ z v)
    (ActualBruhat.compatible_unipotent F ζ hζ)
    (KPAdditiveHaar.adelicMeasure F) (KPWildKernelUpperBound.quotientHaar F)
    (KPContinuation.ChamberOutgoingSource.actual_quotientHaar_compatible F) g hsum
    (heq.symm ▸ hm) (heq.symm ▸ hi) χ hχ hne
  calc
    _ = ∫ y : Q F, KPGlobalEisensteinData.eisenstein
        (fun c : KPChamberBruhatTwoCells.RationalQuotient F => r (Quotient.out c))
        (f.val z) (n (Multiplicative.ofAdd (Quotient.out y)) * g) (hsum y) *
          star (χ y : ℂ) ∂KPWildKernelUpperBound.quotientHaar F := by
      apply integral_congr_ae
      filter_upwards [] with y
      congr 1
      unfold eisenstein KPGlobalEisensteinData.eisenstein
      apply tsum_congr
      intro c
      rw [KPLiteralExceptionalResidue.rationalLift_eq_constructed]
      rfl
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg (fun c : ℂ => c * star (χ (QuotientAddGroup.mk x) : ℂ)) (congrFun heq x)

end DedekindZetaZeroFree.KPLiteralResidueKernelTests.FiniteFactorSplit.FourierChamber

end
