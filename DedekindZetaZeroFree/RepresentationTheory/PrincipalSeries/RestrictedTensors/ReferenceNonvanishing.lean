module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorProducts.IntegralQuotientActions
public import DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.LocalCompactsAndScalarSlots

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.DetectedDictionary
open MomentSources TensorActionSource
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (M : ∀ q, LocalImageData R q)

theorem finite_preimage_nonzero (q : KPFinitePlace F) :
    ∃ f : plusLocal R M (Sum.inr q),
      finiteSourceQuotient R M q f ≠ 0 := by
  have hA := (KPRankOneShellRepair.actual_zero_maps_nonzero F R.A.zeta12
    R.A.primitive_zeta12 q (M q).inducing (M q).inducing.polarization
    (M q).haar (M q).haar_integer).1
  by_contra hn
  push_neg at hn
  apply hA
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  exact congrArg Subtype.val (hn f)

def finiteReferenceSource (q : KPFinitePlace F) : plusLocal R M (Sum.inr q) :=
  (finite_preimage_nonzero R M q).choose

def finiteReference (q : KPFinitePlace F) : actualLocal R M (Sum.inr q) :=
  finiteSourceQuotient R M q (finiteReferenceSource R M q)

theorem finiteReference_ne_zero (q : KPFinitePlace F) :
    finiteReference R M q ≠ 0 :=
  (finite_preimage_nonzero R M q).choose_spec

def complexReferenceSource : KPLiteralTensor.harmonicPlus :=
  ⟨KPCplxPrincipalSeriesCharts.sphericalSection
      KPCplxPrincipalSeriesCharts.positiveParameter, by
    apply Submodule.mem_iSup_of_mem 0
    rw [KPCplxIntertwinerEigenvalues.harmonicKType_zero_eq_span]
    exact Submodule.mem_span_singleton_self _⟩

def complexReference : KPGlobalResidualConstruction.complexCore :=
  KPLiteralTensor.harmonicQuotient complexReferenceSource

theorem complexReference_ne_zero : complexReference ≠ 0 := by
  intro h
  have he := congrArg (fun f : KPGlobalResidualConstruction.complexCore => f.val 1) h
  change KPCplxIntertwinerEigenvalues.standardIntertwiner (1 : ℂˣ)
    (KPCplxPrincipalSeriesCharts.sphericalSection
      KPCplxPrincipalSeriesCharts.positiveParameter) 1 = 0 at he
  rw [KPCplxIntertwinerEigenvalues.standardIntertwiner_spherical] at he
  change (3 * KPCplxCharacterHaar.characterScale (1 : ℂˣ) / 2 : ℂ) *
    KPCplxPrincipalSeriesCharts.sphericalSection
      KPCplxPrincipalSeriesCharts.negativeParameter 1 = 0 at he
  rw [KPCplxPrincipalSeriesCharts.sphericalSection_one, mul_one] at he
  have hp := KPCplxCharacterHaar.characterScale_pos (1 : ℂˣ)
  have hr := congrArg Complex.re he
  norm_num at hr
  linarith

def referenceSource (p : KPHilbert.Place F) : plusLocal R M p := by
  cases p with
  | inl w => exact complexReferenceSource
  | inr q => exact finiteReferenceSource R M q

def reference (p : KPHilbert.Place F) : actualLocal R M p :=
  sourceQuotient R M p (referenceSource R M p)

theorem reference_ne_zero (p : KPHilbert.Place F) : reference R M p ≠ 0 := by
  cases p with
  | inl w => exact complexReference_ne_zero
  | inr q => exact finiteReference_ne_zero R M q

end DedekindZetaZeroFree.FourierContinuation.DetectedDictionary

end
