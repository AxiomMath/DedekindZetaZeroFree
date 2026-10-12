module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarGermUniqueness
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactRestrictionUpperRootPeriods

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem selected_upper_period_continuation
    (C : JointForwardIdentitySources R N) :
    ∃ (U : Set ℂ) (r : ℝ) (I : R.A.UnitQuotient → ℂ → Group R → ℂ),
      IsOpen U ∧ IsConnected U ∧ U ⊆ KPContinuation.spectralDomain ∧
      {s : ℂ | (1 / 3 : ℝ) < s.re} ⊆ U ∧
      0 < r ∧ r ≤ C.realization.radius ∧ Metric.ball (0 : ℂ) r ⊆ U ∧
      (∀ v g, MeromorphicOn (fun s => I v s g) U) ∧
      (∀ v s, (1 / 3 : ℝ) < s.re → ∀ g,
        Integrable (fun q => KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
          C.sources.K (C.sources.flat v) s
          (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) C.sources.dq ∧
        I v s g = chamberPeriod C v s g) ∧
      (∀ v s, s ∈ Metric.ball (0 : ℂ) r → s ≠ 0 → ∀ g,
        Integrable (fun q => C.realization.cleared v s
          (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) C.sources.dq ∧
        clearedPeriod C v s g = s * I v s g) := by
  exact DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation.selected_upper_period_continuation_proved C

end DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods

end
