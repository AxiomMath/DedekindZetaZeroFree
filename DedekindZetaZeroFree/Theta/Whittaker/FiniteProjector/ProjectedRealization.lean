module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.ProjectedSources

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end

section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem projected_realization  (hR : RootAligned R)
    {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
    (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F) (l : List R.A.Sf) :
    ∃ (Q : AdmissibleFlatSources R) (T : Realization R Q), Q.dq = A.sources.dq ∧
      ∀ v, T.theta v = FiniteWhittakerProjectors.rootProjectorWord R I c t l (A.realization.theta v) := by
  obtain ⟨Q,hq,hB⟩ := projected_sources R A I c t l
  let P : JointRootAlignedSources R N := ⟨hR,N,rfl,Q⟩
  obtain ⟨C,⟨H⟩⟩ := selected_scalar_source_exists  R P
  have hg := fun v => selected_source_smooth_germ_of_scalar_germ  R P C v (H v)
  choose G hG using hg
  let T := EisensteinSmoothGerms.assemble C G
  refine ⟨Q,T,hq,?_⟩
  intro v
  obtain ⟨B,hb⟩ := hB v
  exact (funext (fun g => FlatScalarResidue.value_unique (realizationScalarResidue T v) B g)).trans hb
end DedekindZetaZeroFree.RootDerivatives

end
end
