module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactSmoothRealization
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGerms.CanonicalCauchyCoefficients
public import DedekindZetaZeroFree.Eisenstein.Residues.RealizationAndPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
variable {C : ScalarContinuation R Q}

theorem scalar_family_realization_constructed (H : ∀ v, ScalarGerm C v) :
    ∃ T : Realization R Q, T.E = C.E ∧
      (∀ v, T.radius ≤ (H v).radius) ∧
      (∀ v s, T.cleared v s = ((H v).cleared s : Functions R)) ∧
      (∀ v n, T.coefficients v n = (H v).coefficients n) := by
  choose G hrad he hc using (fun v => scalarGerm_upgrade_canonical (H v))
  let T := EisensteinSmoothGerms.assemble C G
  have hb := (Classical.choose_spec (EisensteinSmoothGerms.common_radius G)).2.2
  refine ⟨T, rfl, ?_, ?_, ?_⟩
  · intro v
    exact (hb v).trans (hrad v)
  · intro v s
    exact congrFun (he v) s
  · intro v n
    exact congrFun (hc v) n

end DedekindZetaZeroFree.SharedSource

end
