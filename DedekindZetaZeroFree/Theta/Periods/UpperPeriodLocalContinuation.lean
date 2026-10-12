module

public import DedekindZetaZeroFree.Eisenstein.Residues.CompactPeriodLaurentGerms
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberAnalyticity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity
open MomentSources
open ThetaExpansion.ChamberPeriods
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem selected_chamber_period_integrable (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    Integrable (fun q => KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
      C.sources.K (C.sources.flat v) s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) C.sources.dq :=
  Chamber.upper_integrable F R.A.zeta12 R.A.primitive_zeta12 C.sources.K C.sources.iwasawa
    (C.sources.flat v) C.sources.dq C.sources.quotientHaar s hs g

end DedekindZetaZeroFree.CompactPeriodAnalyticity

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity
open MomentSources
open ThetaExpansion.ChamberPeriods
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem selected_chamber_period_analytic (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (g : Group R) : AnalyticOnNhd ℂ (fun s => chamberPeriod C v s g)
      {s : ℂ | (1 / 3 : ℝ) < s.re} :=
  Chamber.upper_analyticOnNhd C.sources v g

theorem selected_cleared_period_analytic (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (g : Group R) : AnalyticOnNhd ℂ (fun s => clearedPeriod C v s g)
      (Metric.ball (0 : ℂ) C.realization.radius) :=
  CompactPeriod.upper_cleared_analyticOnNhd C.realization v g

end DedekindZetaZeroFree.CompactPeriodAnalyticity

end
end
