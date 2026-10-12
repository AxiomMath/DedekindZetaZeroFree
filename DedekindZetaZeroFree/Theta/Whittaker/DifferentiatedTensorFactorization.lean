module

public import DedekindZetaZeroFree.Eisenstein.Residues.LieActionComparison
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.ProjectedFactorization

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources ThetaExpansion NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
variable (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
variable (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)
variable {Q' : AdmissibleFlatSources R} (T' : Realization R Q')
variable (hdq : Q'.dq = A.sources.dq)
variable (hpin : ∀ v, T'.theta v = _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.rootProjectorWord R I c t
  (Finset.univ : Finset R.A.Sf).toList (A.realization.theta v))

include I c t hdq hpin

theorem projected_factorization_native
    (hn : ∀ v, fourier R Q'.dq (T'.theta v) 1 ≠ 0)
    (hNative : SourceNativeLie R A.factorization) :
    ∃ D' : SourceFactorization R Q' T', SourceNativeLie R D' ∧
      (∀ q, D'.finiteData q = A.factorization.finiteData q) ∧
      (∀ q, (D'.finiteData q).haar = (A.factorization.finiteData q).haar) ∧
      ExteriorCoefficients R Q' T' D' := by
  let D := A.factorization
  have hf := fun v => FiniteWhittakerProjectors.selected_rootProjectorWord_frozen R D I c t
    (Finset.univ : Finset R.A.Sf).toList v
  choose s x hs hx using hf
  have hsp := FiniteWhittakerProjectors.projected_rows_recovery R A I c t T' hdq hpin hn
  have hhc := FiniteWhittakerProjectors.hcHeckeSpan_le_of_finite_recovery R A.realization T' hsp
  let D' : SourceFactorization R Q' T' := {
    finiteData := D.finiteData
    references := D.references
    bad := D.bad
    bad_exact := D.bad_exact
    ell := D.ell
    reference_value := D.reference_value
    scalarSlot := D.scalarSlot
    coreMap := D.coreMap
    selected := fun v => RestrictedTensorSimple.stageInclusion _ D.references D.bad (s v) (PiTensorProduct.tprod ℂ (x v))
    selected_eq := fun v => (hx v).trans (hpin v).symm
    selected_frozen_stage := fun v => ⟨s v,x v,hs v,rfl⟩
    core_injective := D.core_injective
    core_same_residue := fun z => ⟨hhc (D.core_same_residue z).1,(D.core_same_residue z).2⟩
    finite_intertwining := D.finite_intertwining
    complex_intertwining := D.complex_intertwining
    product_integrable := by rw [hdq]; exact D.product_integrable
    product_exact := by rw [hdq]; exact D.product_exact
    spherical_reference := D.spherical_reference
    detected_tensor := by rw [hdq]; exact D.detected_tensor
    period_integrable := fun v g => FourierContinuation.theta_period_integrable T' v g
    detected := by obtain ⟨v,_⟩ := D.detected; exact ⟨v,hn v⟩ }
  refine ⟨D',hNative,fun _ => rfl,fun _ => rfl,?_⟩
  exact ⟨A.exterior.rational_exact,A.exterior.crt_product,A.exterior.local_exact⟩
end DedekindZetaZeroFree.RootDerivatives

end
