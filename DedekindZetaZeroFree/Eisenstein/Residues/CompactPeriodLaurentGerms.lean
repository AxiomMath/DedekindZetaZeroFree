module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.JointContinuity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

def archDiagonal (w : InfinitePlace F) (z : w.Completionˣ) : Group R :=
  KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z)

def weylWeight (w : InfinitePlace F) (z : w.Completionˣ) (s : ℂ) : ℂ :=
  KPGlobalExceptionalParameter.realLogPower (‖(z : w.Completion)‖ ^ 2) (1 / 3 - s)

def incoming (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient) (s : ℂ) (g : Group R) : ℂ :=
  (C.sources.flat v).val s g

def clearedPeriod (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient) (s : ℂ) (g : Group R) : ℂ :=
  upper R C.sources.dq (C.realization.cleared v s) g

def chamberPeriod (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient) (s : ℂ) (g : Group R) : ℂ :=
  upper R C.sources.dq
    (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 C.sources.K (C.sources.flat v) s) g

theorem residue_integrable (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient) (g : Group R) :
    Integrable (fun q => C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) C.sources.dq := by
  have hp : Continuous (fun q : KPAdditiveQuotient F => (adelicTraceQuotientCharacter F q : ℂ)) :=
    continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)
  have hi := (C.factorization.period_integrable v g).mul_bdd hp.aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall (fun q => by simp))
  apply hi.congr
  filter_upwards [] with q
  rw [mul_assoc]
  have hunit : star (adelicTraceQuotientCharacter F q : ℂ) *
      (adelicTraceQuotientCharacter F q : ℂ) = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
    simp
  rw [hunit, mul_one]

theorem selected_compact_period_germ (C : JointForwardIdentitySources R N) :
    (∀ v s, s ∈ Metric.ball (0 : ℂ) C.realization.radius → ∀ g,
      Integrable (fun q => C.realization.cleared v s
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) C.sources.dq) ∧
    (∀ v g, ContinuousAt (fun s => clearedPeriod C v s g) 0) := by
  constructor
  · intro v s hs g
    exact DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod.cleared_integrable C.realization v s hs g
  · intro v g
    exact DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod.upper_cleared_continuousAt_zero C.realization v g

end DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods

end
