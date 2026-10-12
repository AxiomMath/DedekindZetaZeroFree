module

public import DedekindZetaZeroFree.Metaplectic.Kubota.ArchimedeanFlowBasis
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LieDerivatives.MatrixFlows
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DifferentialWordCyclicSpan

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open KPActualReflectionData.NativeFlowJet
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_smul → smooth_smul
open FlowBasis
local notation "flow_directions_span" => FlowBasis.directions_span
local notation "flow_coefficients" => FlowBasis.coefficients
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local notation "ρ" => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
local notation "W" => actualRightWord F R.A.zeta12 R.A.primitive_zeta12
local notation "d" => chartDerivative F R.A.zeta12 R.A.primitive_zeta12

private theorem actualRightWord_eq_adelic (w : List (Fin (groupDimension F)))
    (f : Functions R) : W w f =
      AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord, AdelicRightLieWords.actualRightWord]
    rw [ih]
    rfl

theorem actualRight_flowDirection (b : Fin (groupDimension F)) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) :
    actualRight F R.A.zeta12 R.A.primitive_zeta12 b f =
      d (flowDirection F (nativeBasis F b)) f := by
  ext g
  have hd := smooth_chart_differentiable F R.A.zeta12 R.A.primitive_zeta12 f hf g
  have hh := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (flowChart_hasDeriv F (nativeBasis F b)) (flowChart_zero F _).symm
  have he : (fun t => f (g * nativeCurve F R.A.zeta12 R.A.primitive_zeta12 b t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => f (g * archChart F R.A.zeta12 R.A.primitive_zeta12
        (flowChart F (nativeBasis F b) t))) := by
    filter_upwards [flowChart_reconstruct F R.A.zeta12 R.A.primitive_zeta12 (nativeBasis F b)] with t ht
    rw [ht]
    rfl
  rw [actualRight_nativeCurve]
  change deriv _ 0 = _
  rw [he.deriv_eq]
  exact hh.deriv

theorem chartDerivative_native_sum (X : ArchCoordinates F) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) :
    d X f = ∑ b : Fin (groupDimension F),
      (flow_coefficients F X (nativeBasis F b) : ℂ) •
        actualRight F R.A.zeta12 R.A.primitive_zeta12 b f := by
  have he : (nativeBasis F) = ((lieEnumeration F).trans
      (KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F)) := rfl
  have hspan := flow_directions_span F X
  rw [← Equiv.sum_comp ((lieEnumeration F).trans
    (KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F))] at hspan
  conv_lhs => rw [hspan]
  ext g
  simp only [chartDerivative, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    Complex.real_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [actualRight_flowDirection R b f hf]
  rfl

theorem chartDerivative_translate (a : Group R) :
    ∃ L : ArchCoordinates F →L[ℝ] ArchCoordinates F,
      ∀ (f : Functions R), KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f →
      ∀ X, d X (ρ a f) = ρ a (d (L X) f) := by
  obtain ⟨L,hL⟩ := KPActualReflectionData.AffineCompactConjugation.right_derivative_conjugation
    F R.A.zeta12 R.A.primitive_zeta12 a⁻¹
  refine ⟨L,fun f hf X => ?_⟩
  have ht := KPLiteralPeriod.NonzeroResidue.smooth_right_translate
    F R.A.zeta12 R.A.primitive_zeta12 f hf a
  ext g
  have h := hL (ρ a f)
    (smooth_chart_differentiable F R.A.zeta12 R.A.primitive_zeta12 _ ht) X (g*a)
  change (fderiv ℝ (fun x => f (((g*a)*a⁻¹*archChart F R.A.zeta12 R.A.primitive_zeta12 x)*a)) (archBase F)) X =
    (fderiv ℝ (fun x => f (((g*a)*archChart F R.A.zeta12 R.A.primitive_zeta12 x*a⁻¹)*a)) (archBase F)) (L X) at h
  change (fderiv ℝ (fun x => f ((g*archChart F R.A.zeta12 R.A.primitive_zeta12 x)*a)) (archBase F)) X =
    (fderiv ℝ (fun x => f ((g*a)*archChart F R.A.zeta12 R.A.primitive_zeta12 x)) (archBase F)) (L X)
  simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_one] using h

theorem hcHeckeSpan_smooth {Q : AdmissibleFlatSources R} (T : Realization R Q)
    {f : Functions R} (hf : f ∈ hcHeckeSpan T) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v,a,w,rfl⟩ := hf
    simpa only [actualRightWord_eq_adelic R,
      _root_.DedekindZetaZeroFree.MomentSources.Realization.theta] using
      KPLiteralPeriod.NonzeroResidue.smooth_right_translate
        F R.A.zeta12 R.A.primitive_zeta12 _
        (SharedSource.actualRightWord_smooth _ (T.automorphic v).1 w) a
  | zero => exact (wordRecovery R T).zero_mem.1
  | add f g hf hg ihf ihg => exact smooth_add F R.A.zeta12 R.A.primitive_zeta12 f g ihf ihg
  | smul c f hf ih => exact smooth_smul F R.A.zeta12 R.A.primitive_zeta12 c f ih

theorem hcHeckeSpan_translate {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (a : Group R) {f : Functions R} (hf : f ∈ hcHeckeSpan T) : ρ a f ∈ hcHeckeSpan T := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v,b,w,rfl⟩ := hf
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨v,a*b,w,rfl⟩
  | zero => simpa using (hcHeckeSpan T).zero_mem
  | add f g hf hg ihf ihg => simpa only [map_add] using (hcHeckeSpan T).add_mem ihf ihg
  | smul c f hf ih => simpa only [map_smul] using (hcHeckeSpan T).smul_mem c ih

theorem hcHeckeSpan_right {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (b : Fin (groupDimension F)) {f : Functions R} (hf : f ∈ hcHeckeSpan T) :
    actualRight F R.A.zeta12 R.A.primitive_zeta12 b f ∈ hcHeckeSpan T := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v,a,w,rfl⟩ := hf
    rw [← actualRightWord_eq_adelic R w (T.theta v)]
    have hs : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (W w (T.theta v)) :=
      SharedSource.actualRightWord_smooth _ (T.automorphic v).1 w
    have ht := KPLiteralPeriod.NonzeroResidue.smooth_right_translate
      F R.A.zeta12 R.A.primitive_zeta12 _ hs a
    obtain ⟨L,hL⟩ := chartDerivative_translate R a
    rw [actualRight_flowDirection R b _ ht, hL _ hs,
      chartDerivative_native_sum R _ _ hs, map_sum]
    apply Submodule.sum_mem
    intro c hc
    rw [map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨v,a,c::w,by
      rw [← actualRightWord_eq_adelic R] <;> rfl⟩
  | zero =>
    have hz := SharedSource.actualRightWord_smul (F := F) (ζ := R.A.zeta12)
      (hζ := R.A.primitive_zeta12) (0 : ℂ) (0 : Functions R)
      ((wordRecovery R T).zero_mem.1) [b]
    have he : actualRight F R.A.zeta12 R.A.primitive_zeta12 b (0 : Functions R) = 0 := by
      simpa only [smul_zero, actualRightWord, zero_smul] using hz
    rw [he]
    exact (hcHeckeSpan T).zero_mem
  | add f g hf hg ihf ihg =>
    have he := SharedSource.actualRightWord_add f g (hcHeckeSpan_smooth R T hf)
      (hcHeckeSpan_smooth R T hg) [b]
    change W [b] (f+g) ∈ hcHeckeSpan T
    rw [he]
    exact (hcHeckeSpan T).add_mem ihf ihg
  | smul c f hf ih =>
    have he := SharedSource.actualRightWord_smul c f (hcHeckeSpan_smooth R T hf) [b]
    change W [b] (c • f) ∈ hcHeckeSpan T
    rw [he]
    exact (hcHeckeSpan T).smul_mem c ih

theorem hcHeckeSpan_le_wordRecovery {Q : AdmissibleFlatSources R} (T : Realization R Q) :
    hcHeckeSpan T ≤ wordRecovery R T := by
  intro f hf
  refine ⟨hcHeckeSpan_smooth R T hf,fun w a => hcHeckeSpan_translate R T a ?_⟩
  induction w with
  | nil => exact hf
  | cons b w ih => exact hcHeckeSpan_right R T b ih

theorem wordRecovery_translate {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (a : Group R) {f : Functions R} (hf : f ∈ wordRecovery R T) :
    ρ a f ∈ wordRecovery R T := by
  apply hcHeckeSpan_le_wordRecovery R T
  apply hcHeckeSpan_translate R T a
  simpa only [actualRightWord, map_one, Module.End.one_apply] using hf.2 [] 1

end DedekindZetaZeroFree.RootDerivatives

end
