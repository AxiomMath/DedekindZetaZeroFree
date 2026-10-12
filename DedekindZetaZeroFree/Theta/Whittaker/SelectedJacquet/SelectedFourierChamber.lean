module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberIntegrability
public import DedekindZetaZeroFree.Eisenstein.Whittaker.ChamberUnfolding
public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (Q : AdmissibleFlatSources R)
open KPLiteralChamberWeight

theorem selected_quotientHaar_eq :
    Q.dq = KPWildKernelUpperBound.quotientHaar F := by
  letI := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  exact MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem selected_chamber_fourier_integrable (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    Integrable (fun q => KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
      Q.K (Q.flat v) s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  have hi := CompactPeriodAnalyticity.Chamber.upper_integrable F R.A.zeta12 R.A.primitive_zeta12
    Q.K Q.iwasawa (Q.flat v) Q.dq Q.quotientHaar s hs g
  exact hi.mul_bdd
    ((continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)).star).aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall (fun q => by simp))

theorem selected_open_cell_fourier_integrable (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    Integrable (fun x : KPAdeles F => (Q.flat v).val s
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) *
      star (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ))
      (KPAdditiveHaar.adelicMeasure F) := by
  have hi := standard_integrable F R.A.zeta12 R.A.primitive_zeta12
    Q.K Q.iwasawa (Q.flat v) s hs g
  exact hi.mul_bdd
    (((continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)).comp
      QuotientAddGroup.continuous_mk).star).aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall (fun x => by simp))

theorem selected_chamber_fourier_unfolding (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    fourier R Q.dq
      (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s) g =
    ∫ x : KPAdeles F, (Q.flat v).val s
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) *
      star (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ)
      ∂KPAdditiveHaar.adelicMeasure F := by
  have hi := selected_chamber_fourier_integrable R Q v s hs g
  have hu := selected_open_cell_fourier_integrable R Q v s hs g
  unfold MomentSources.fourier
  rw [selected_quotientHaar_eq R Q]
  exact KPLiteralResidueKernelTests.FiniteFactorSplit.FourierChamber.literal_nontrivial_fourier_unfolding
    F R.A.zeta12 R.A.primitive_zeta12 Q.K Q.iwasawa (Q.flat v) s hs
    (adelicTraceQuotientCharacter F) (continuous_adelicTraceQuotientCharacter F)
    (adelicTraceQuotientCharacter_ne_one F) g

end DedekindZetaZeroFree.SheetRescaling

end
