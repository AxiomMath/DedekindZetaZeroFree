module

public import DedekindZetaZeroFree.Eisenstein.Induction.SphericalTensor.FlatPreimages
public import DedekindZetaZeroFree.Eisenstein.Residues.LieActionComparison

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory RootDerivatives
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem spherical_word_smul
    (R : PrincipalMellin.ActualRecipe S η) (c : ℂ) (f : Functions R)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w (c • f) =
      c • KPContActualSphericalRightFieldIdentification.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord, ih]
    funext g
    simp only [KPContActualSphericalRightFieldIdentification.actualRight, Pi.smul_apply, smul_eq_mul]
    exact deriv_const_mul_field c

theorem normalized_spherical_factorization_exists
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A)
    (P : NormalizedSphericalTensor R A D) (L : SphericalFlatPreimages R A D P)
    (hNative : SourceNativeLie R A.factorization) :
    ∃ B : JointExteriorCoefficientSources R N, SourceNativeLie R B.factorization ∧ B.sources.dq = A.sources.dq ∧
      (∀ v, B.realization.theta v = tensorFunction R A.factorization D.tensor.stage P.entries) ∧
      (∀ v, (B.sources.flat v).val 0 ≠ 0) ∧
      (∀ v, B.realization.theta v ≠ 0) ∧
      (∀ v, fourier R B.sources.dq (B.realization.theta v) 1 ≠ 0) := by
  let B5 : JointRootAlignedSources R N := ⟨A.aligned, N, rfl, L.sources⟩
  obtain ⟨C, ⟨H⟩⟩ := selected_scalar_source_exists  R B5
  choose G hG using fun v => selected_source_smooth_germ_of_scalar_germ  R B5 C v (H v)
  let T := EisensteinSmoothGerms.assemble C G
  have hpin (v) : T.theta v = tensorFunction R A.factorization D.tensor.stage P.entries :=
    (funext (fun g => FlatScalarResidue.value_unique (realizationScalarResidue T v) (L.residue v) g)).trans
      (L.residue_exact v)
  have hscaled : T.theta 1 = P.scalar • D.tensor.value := (hpin 1).trans P.realization_exact
  have hspan : sphericalHCSpan R D.tensor.value ≤ hcHeckeSpan T := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, w, rfl⟩
    have hm : KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a
        (KPContActualSphericalRightFieldIdentification.actualRightWord
          F R.A.zeta12 R.A.primitive_zeta12 w (T.theta 1)) ∈ hcHeckeSpan T :=
      Submodule.subset_span ⟨1, a, w, by
        have h : KPContActualSphericalRightFieldIdentification.actualRightWord
            F R.A.zeta12 R.A.primitive_zeta12 w (T.theta 1) =
            AdelicRightLieWords.actualRightWord
              F R.A.zeta12 R.A.primitive_zeta12 w (T.theta 1) := by
          induction w with
          | nil => rfl
          | cons b w ih =>
            simp only [KPContActualSphericalRightFieldIdentification.actualRightWord,
              AdelicRightLieWords.actualRightWord]
            rw [ih]
            rfl
        rw [h]⟩
    rw [hscaled, spherical_word_smul, map_smul] at hm
    have hi := Submodule.smul_mem (hcHeckeSpan T) P.scalar⁻¹ hm
    exact (by simpa only [smul_smul, inv_mul_cancel₀ P.scalar_nonzero, one_smul] using hi :
      KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a
        (KPContActualSphericalRightFieldIdentification.actualRightWord
          F R.A.zeta12 R.A.primitive_zeta12 w D.tensor.value) ∈ hcHeckeSpan T)
  let core := RestrictedTensorSimple.stageInclusion _ A.factorization.references A.factorization.bad
    D.tensor.stage (PiTensorProduct.tprod ℂ P.entries)
  let E : SourceFactorization R L.sources T := {
    finiteData := A.factorization.finiteData
    references := A.factorization.references
    bad := A.factorization.bad
    bad_exact := A.factorization.bad_exact
    ell := A.factorization.ell
    reference_value := A.factorization.reference_value
    scalarSlot := A.factorization.scalarSlot
    coreMap := A.factorization.coreMap
    selected := fun _ => core
    selected_eq := fun v => (hpin v).symm
    selected_frozen_stage := fun _ => ⟨D.tensor.stage, P.entries, D.tensor.stage_exact, rfl⟩
    core_injective := A.factorization.core_injective
    core_same_residue := fun x => ⟨hspan (D.core_generated x), (A.factorization.core_same_residue x).2⟩
    finite_intertwining := A.factorization.finite_intertwining
    complex_intertwining := A.factorization.complex_intertwining
    product_integrable := by rw [L.dq_exact]; exact A.factorization.product_integrable
    product_exact := by rw [L.dq_exact]; exact A.factorization.product_exact
    spherical_reference := A.factorization.spherical_reference
    detected_tensor := by rw [L.dq_exact]; exact A.factorization.detected_tensor
    period_integrable := fun v g => FourierContinuation.theta_period_integrable T v g
    detected := ⟨1, by rw [L.dq_exact, hpin]; exact P.period_nonzero⟩ }
  let B : JointExteriorCoefficientSources R N := {
    toJointRootAlignedSources := B5
    realization := T
    factorization := E
    localHaarTransport := ?_
    exterior := ⟨A.exterior.rational_exact, A.exterior.crt_product, A.exterior.local_exact⟩ }
  · refine ⟨B, hNative, L.dq_exact, hpin, L.source_nonzero, ?_, ?_⟩
    · intro v
      rw [hpin]
      exact P.realization_nonzero
    · intro v
      rw [L.dq_exact, hpin]
      exact P.period_nonzero
  · intro q
    change N.finiteHaar q = ENNReal.ofReal (PoissonS.integerVolume F q) •
      (A.factorization.finiteData q).haar
    exact (congrArg (fun M : TraceHaarTransport R => M.finiteHaar q) A.transport_exact).symm.trans
      (A.localHaarTransport q)

end DedekindZetaZeroFree.ThetaExpansion

end
