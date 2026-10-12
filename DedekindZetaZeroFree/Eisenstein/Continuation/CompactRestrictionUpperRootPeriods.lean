module

public import DedekindZetaZeroFree.Theta.Periods.UpperOrbitContinuation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation
open MomentSources ThetaExpansion.ChamberPeriods
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem selected_upper_period_continuation_proved (C : JointForwardIdentitySources R N) :
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
  choose I hm hch hclear using native_period_exists C
  refine ⟨KPContinuation.spectralDomain, C.realization.radius, fun v s g => I v g s,
    KPContinuation.spectralDomain_isOpen, KPContinuation.spectralDomain_isConnected,
    Set.Subset.rfl, KPContinuation.convergenceHalfPlane_subset_spectralDomain,
    C.realization.radius_pos, le_rfl, C.realization.disc_domain, hm, ?_, ?_⟩
  · intro v s hs g
    exact ⟨selected_chamber_period_integrable C v s hs g, hch v g s hs⟩
  · intro v s hs hn g
    exact ⟨CompactPeriod.cleared_integrable C.realization v s hs g, hclear v g s hs hn⟩

end DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

end
