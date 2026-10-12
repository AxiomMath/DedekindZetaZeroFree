module

public import DedekindZetaZeroFree.Eisenstein.Residues.AdelicChamberContinuationData
public import DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped NumberField ENNReal

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing

namespace BruhatIntegral

variable (F : Type) [Field F] [NumberField F]

 abbrev A := NumberField.AdeleRing (𝓞 F) F
 abbrev Q := A F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F

theorem integral_period_of_integrable
    (dx : Measure (A F)) (dq : Measure (Q F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [IsProbabilityMeasure dq]
    (hcompat : KPChamberAdditivePeriodization.CompatibleHaar F dx dq)
    (h : A F → ℂ) (hmeas : Measurable h) (hint : Integrable h dx) :
    Integrable (KPChamberAdditivePeriodization.complexPeriod F h) dq ∧
      (∫ q, KPChamberAdditivePeriodization.complexPeriod F h q ∂dq) =
        ∫ a, h a ∂dx := by
  have hnorm := KPChamberAdditivePeriodization.lintegral_nonnegativePeriod
    F dx dq hcompat (fun a => ENNReal.ofReal ‖h a‖) hmeas.norm.ennreal_ofReal
  have hfinite : ∫⁻ q, KPChamberAdditivePeriodization.normPeriod F h q ∂dq < ⊤ := by
    change (∫⁻ q, KPChamberAdditivePeriodization.nonnegativePeriod F
      (fun a => ENNReal.ofReal ‖h a‖) q ∂dq) < ⊤
    rw [hnorm]
    simpa only [ofReal_norm_eq_enorm, HasFiniteIntegral] using hint.hasFiniteIntegral
  exact (KPChamberAdditivePeriodization.integral_complexPeriod
    F dx dq hcompat h hmeas hfinite).2.2

theorem constantTerm_two_cells
    {G : Type*} [Group G]
    (s : Matrix.ProjGenLinGroup (Fin 2) F →* G)
    (n : Multiplicative (A F) →* G) (fR : G → ℂ)
    (hB : KPChamberBruhatTwoCells.ScalarRationalBorelInvariant F s fR)
    (hN : KPChamberBruhatTwoCells.ScalarUnipotentInvariant F n fR)
    (hlift : KPChamberBruhatTwoCells.CompatibleUnipotentLift F s n)
    (dx : Measure (A F)) (dq : Measure (Q F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [IsProbabilityMeasure dq]
    (hcompat : KPChamberAdditivePeriodization.CompatibleHaar F dx dq)
    (g : G)
    (hsum : ∀ q : Q F, KPGlobalEisensteinData.EisensteinSummable
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => s (Quotient.out c))
      fR (n (Multiplicative.ofAdd (Quotient.out q)) * g))
    (hmeas : Measurable (fun a : A F =>
      fR (s (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd a) * g)))
    (hint : Integrable (fun a : A F =>
      fR (s (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd a) * g)) dx) :
    (∫ q : Q F, KPGlobalEisensteinData.eisenstein
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => s (Quotient.out c))
      fR (n (Multiplicative.ofAdd (Quotient.out q)) * g) (hsum q) ∂dq) =
      fR g + ∫ a : A F,
        fR (s (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd a) * g) ∂dx := by
  let h : A F → ℂ := fun a =>
    fR (s (KPChamberBruhatTwoCells.rationalWeyl F) * n (Multiplicative.ofAdd a) * g)
  have hperiod := integral_period_of_integrable F dx dq hcompat h hmeas hint
  have hformula : ∀ q : Q F, KPGlobalEisensteinData.eisenstein
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => s (Quotient.out c))
      fR (n (Multiplicative.ofAdd (Quotient.out q)) * g) (hsum q) =
        fR g + KPChamberAdditivePeriodization.complexPeriod F h q := by
    intro q
    rw [KPChamberBruhatTwoCells.eisenstein_two_cells F s fR hB]
    rw [hN]
    congr 1
    apply tsum_congr
    intro t
    simpa only [h, mul_assoc] using
      KPChamberBruhatTwoCells.open_cell_translate F s n hlift fR t (Quotient.out q) g
  simp_rw [hformula]
  rw [integral_add (integrable_const _) hperiod.1, integral_const, hperiod.2]
  simp [h]

end BruhatIntegral
end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing

end

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing
namespace ActualBruhat

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev rational :=
  (KPGlobalResidualConstruction.ElementaryOutputs.rationalSplitting F ζ hζ).lift

theorem section_unipotent_invariant (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (a : KPGlobalTorusFunctionData.Adeles F)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    v.val (KPGlobalTorusFunctionData.N F ζ hζ a * g) = v.val g := by
  have h := v.property 1 a g
  simpa [KPGlobalTorusFunctionData.deltaHalf] using h

theorem rational_unipotent (t : F) :
    rational F ζ hζ (KPChamberBruhatTwoCells.rationalUnipotent F t) =
      KPGlobalTorusFunctionData.Nhom F ζ hζ
        (Multiplicative.ofAdd (algebraMap F (KPGlobalTorusFunctionData.Adeles F) t)) := by
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ (KubotaRankTwo.n F t)) = _
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ _ =
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPRationalAdelicSplitting.N F ζ hζ _)
  exact congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
    (KPRationalAdelicSplitting.N_rational F ζ hζ t).symm

theorem compatible_unipotent :
    KPChamberBruhatTwoCells.CompatibleUnipotentLift F (rational F ζ hζ)
      (KPGlobalTorusFunctionData.Nhom F ζ hζ) := rational_unipotent F ζ hζ

theorem unsigned_weyl :
    rational F ζ hζ (Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap F)) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) := by
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ _) = _
  exact congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
    (KPRationalAdelicSplitting.W_rational F ζ hζ).symm

theorem section_rational_diagonal_invariant (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (y : Fˣ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    v.val ((KPGlobalTorusFunctionData.s F ζ hζ y).val * g) = v.val g := by
  let t : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H :=
    KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y
  have h := v.property t 0 g
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hchar : ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character t : ℂ) = 1 := by
    change ((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ
      (KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y) *
      KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
        (KPGlobalTorusFunctionData.s F ζ hζ y)) : ℂ) = 1
    rw [(KPGlobalTorusPeriodizationInverse.rational_representative_character F ζ hζ y).1,
      KPGlobalTorusBorelTwistCompatibility.normCharacter_rational]
    simp
  rw [hchar] at h
  simpa only [t, KPGlobalTorusPeriodizationInverse.rationalLift, hN, mul_one,
    KPGlobalTorusFunctionData.deltaHalf,
    KPGlobalTorusBorelTwistCompatibility.delta_rational, Units.val_one,
    NNReal.coe_one, Real.sqrt_one, Complex.ofReal_one, hchar, one_mul] using h

theorem section_signed_weyl (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    v.val (rational F ζ hζ (KPChamberBruhatTwoCells.rationalWeyl F) * g) =
      v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) * g) := by
  have hmatrix : KPChamberBruhatTwoCells.rationalWeyl F =
      Matrix.ProjGenLinGroup.mk (KPGlobalTorusFunctionData.rationalDiagonal F (-1)) *
        Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap F) := by
    rw [← map_mul]
    unfold KPChamberBruhatTwoCells.rationalWeyl
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [KPChamberBruhatTwoCells.rationalWeyl,
        KPGlobalTorusFunctionData.rationalDiagonal, KPStandardLocalRootLifts.weylSwap,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmatrix, map_mul, unsigned_weyl, mul_assoc]
  change v.val ((KPGlobalTorusFunctionData.s F ζ hζ (-1)).val * _) = _
  exact section_rational_diagonal_invariant F ζ hζ s v (-1) _

theorem scalar_unipotent_invariant (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s) :
    KPChamberBruhatTwoCells.ScalarUnipotentInvariant F
      (KPGlobalTorusFunctionData.Nhom F ζ hζ) v.val :=
  section_unipotent_invariant F ζ hζ s v

private theorem upper_matrix_factorization
    (b : KPRationalFlag.borel F) :
    ∃ (y : Fˣ) (t : F), Matrix.ProjGenLinGroup.mk b.val =
      Matrix.ProjGenLinGroup.mk (KPGlobalTorusFunctionData.rationalDiagonal F y) *
        KPChamberBruhatTwoCells.rationalUnipotent F t := by
  have hb : b.val 1 0 = 0 := b.property
  have hdet : b.val 0 0 * b.val 1 1 ≠ 0 := by
    have h := Units.ne_zero (Matrix.GeneralLinearGroup.det b.val)
    simpa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hb] using h
  have ha := (mul_ne_zero_iff.mp hdet).1
  have hd := (mul_ne_zero_iff.mp hdet).2
  let y : Fˣ := Units.mk0 (b.val 0 0 / b.val 1 1) (div_ne_zero ha hd)
  refine ⟨y, b.val 0 1 / b.val 0 0, ?_⟩
  unfold KPChamberBruhatTwoCells.rationalUnipotent
  rw [← map_mul]
  apply Eq.symm
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (b.val 1 1) hd, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPGlobalTorusFunctionData.rationalDiagonal, y,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_two, hb] <;> field_simp <;> ring

theorem scalar_rational_borel_invariant (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s) :
    KPChamberBruhatTwoCells.ScalarRationalBorelInvariant F (rational F ζ hζ) v.val := by
  intro b g
  obtain ⟨B, hB, he⟩ := b.property
  obtain ⟨y, t, ht⟩ := upper_matrix_factorization F ⟨B, hB⟩
  rw [← he, ht, map_mul, rational_unipotent, mul_assoc]
  change v.val ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
    (KPGlobalTorusFunctionData.N F ζ hζ _ * g)) = _
  rw [section_rational_diagonal_invariant, section_unipotent_invariant]

theorem integral_two_cells (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (dx : MeasureTheory.Measure (KPGlobalTorusFunctionData.Adeles F))
    (dq : MeasureTheory.Measure (RawAdditiveQuotient F))
    [dx.IsAddHaarMeasure] [dq.IsAddHaarMeasure] [MeasureTheory.IsProbabilityMeasure dq]
    (hcompat : KPChamberAdditivePeriodization.CompatibleHaar F dx dq)
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (hsum : ∀ q : RawAdditiveQuotient F,
      KPGlobalEisensteinData.EisensteinSummable
        (fun c : KPChamberBruhatTwoCells.RationalQuotient F => rational F ζ hζ (Quotient.out c))
        v.val (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g))
    (hmeas : Measurable (fun a : KPGlobalTorusFunctionData.Adeles F =>
      v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) * KPGlobalTorusFunctionData.N F ζ hζ a * g)))
    (hint : MeasureTheory.Integrable (fun a : KPGlobalTorusFunctionData.Adeles F =>
      v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) * KPGlobalTorusFunctionData.N F ζ hζ a * g)) dx) :
    (∫ q : RawAdditiveQuotient F, KPGlobalEisensteinData.eisenstein
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F => rational F ζ hζ (Quotient.out c))
      v.val (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) (hsum q) ∂dq) =
      v.val g + ∫ a : KPGlobalTorusFunctionData.Adeles F,
        v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPCubicCoverConstruction.adelicW F ζ hζ) * KPGlobalTorusFunctionData.N F ζ hζ a * g) ∂dx := by
  have heq : (fun a : KPGlobalTorusFunctionData.Adeles F =>
      v.val (rational F ζ hζ (KPChamberBruhatTwoCells.rationalWeyl F) *
        KPGlobalTorusFunctionData.Nhom F ζ hζ (Multiplicative.ofAdd a) * g)) =
      (fun a : KPGlobalTorusFunctionData.Adeles F =>
      v.val (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPCubicCoverConstruction.adelicW F ζ hζ) * KPGlobalTorusFunctionData.N F ζ hζ a * g)) := by
    funext a
    change v.val (rational F ζ hζ (KPChamberBruhatTwoCells.rationalWeyl F) *
      KPGlobalTorusFunctionData.N F ζ hζ a * g) = _
    simpa only [mul_assoc] using section_signed_weyl F ζ hζ s v
      (KPGlobalTorusFunctionData.N F ζ hζ a * g)
  have h := BruhatIntegral.constantTerm_two_cells F (rational F ζ hζ)
    (KPGlobalTorusFunctionData.Nhom F ζ hζ) v.val
    (scalar_rational_borel_invariant F ζ hζ s v)
    (scalar_unipotent_invariant F ζ hζ s v) (compatible_unipotent F ζ hζ)
    dx dq hcompat g hsum (heq.symm ▸ hmeas) (heq.symm ▸ hint)
  rw [heq] at h
  exact h

end ActualBruhat
end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Outgoing

end

end
