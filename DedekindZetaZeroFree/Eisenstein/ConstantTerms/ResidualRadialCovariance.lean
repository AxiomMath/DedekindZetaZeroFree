module

public import DedekindZetaZeroFree.Theta.Profiles.DetectedFirstRootFamily
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ComplexWeylIntegralWeight
public import DedekindZetaZeroFree.Eisenstein.Residues.ConstantTermCovariance

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

namespace ChamberPeriods
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.ResidueCovariance renaming cleared_limit_of_chamber_transformation → cleared_limit_of_chamber_transformation

theorem incoming_entire (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient) (g : Group R) :
    Differentiable ℂ (fun s => incoming C v s g) := by
  have he : (fun s => incoming C v s g) = (fun s =>
      KPLiteralChamber.compactExtension F R.A.zeta12 R.A.primitive_zeta12
        C.sources.K C.sources.iwasawa ((C.sources.flat v).val 0) s g) := by
    funext s
    exact (KPLiteralChamber.compactExtension_eq_flat F R.A.zeta12 R.A.primitive_zeta12
      C.sources.K C.sources.iwasawa (C.sources.flat v) s g).symm
  rw [he]
  unfold KPLiteralChamber.compactExtension KPGlobalExceptionalParameter.realLogPower
  fun_prop

theorem weylWeight_entire (w : InfinitePlace F) (z : w.Completionˣ) :
    Differentiable ℂ (weylWeight w z) := by
  unfold weylWeight KPGlobalExceptionalParameter.realLogPower
  fun_prop

theorem weylWeight_zero (w : InfinitePlace F) (z : w.Completionˣ) :
    weylWeight w z 0 =
      (Real.rpow (‖(z : w.Completion)‖ ^ 2) (1 / 3) : ℂ) := by
  unfold weylWeight KPGlobalExceptionalParameter.realLogPower
  rw [sub_zero, Real.rpow_eq_pow,
    Real.rpow_def_of_pos (pow_pos (norm_pos_iff.mpr z.ne_zero) 2), Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem chamber_transformation (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (w : InfinitePlace F)
    (z : w.Completionˣ) (g : Group R) :
    chamberPeriod C v s (archDiagonal w z * g) - incoming C v s (archDiagonal w z * g) =
      weylWeight w z s * (chamberPeriod C v s g - incoming C v s g) := by
  have hbase := selected_chamber_two_cells C v s hs g
  have hleft := selected_chamber_two_cells C v s hs (archDiagonal w z * g)
  rw [hbase.2.2.2, hleft.2.2.2,
    selected_outgoing_weyl_weight C v s hs w z g hbase.2.2.1 hleft.2.2.1]
  ring

theorem selected_residue_radial (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (w : InfinitePlace F) (z : w.Completionˣ) (g : Group R) :
    upper R C.sources.dq (C.realization.theta v) (archDiagonal w z * g) =
      (Real.rpow (‖(z : w.Completion)‖ ^ 2) (1 / 3) : ℂ) *
        upper R C.sources.dq (C.realization.theta v) g := by
  obtain ⟨U, r, I, hU, hc, _hdom, hchsub, hr, _hrr, hball, hmer, hIch, hclear⟩ :=
    selected_upper_period_continuation C
  have hcont := (selected_compact_period_germ C).2
  have hC : (fun s => clearedPeriod C v s (archDiagonal w z * g)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => s * I v s (archDiagonal w z * g)) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)] with s hs0 hsball
    exact (hclear v s hsball hs0 (archDiagonal w z * g)).2
  have hD : (fun s => clearedPeriod C v s g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => s * I v s g) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)] with s hs0 hsball
    exact (hclear v s hsball hs0 g).2
  have hp := incoming_entire C v (archDiagonal w z * g)
  have hq := incoming_entire C v g
  have hm := weylWeight_entire w z
  have he := cleared_limit_of_chamber_transformation
    (fun s => I v s (archDiagonal w z * g)) (fun s => I v s g)
    (fun s => clearedPeriod C v s (archDiagonal w z * g)) (fun s => clearedPeriod C v s g)
    (fun s => incoming C v s (archDiagonal w z * g)) (fun s => incoming C v s g)
    (weylWeight w z) U {s : ℂ | (1 / 3 : ℝ) < s.re}
    hU hc (hball (Metric.mem_ball_self hr))
    (isOpen_lt continuous_const Complex.continuous_re)
    (by refine ⟨1, ?_⟩; norm_num) hchsub (hmer _ _) (hmer _ _)
    (fun s _ => (hp.analyticAt s).meromorphicAt)
    (fun s _ => (hq.analyticAt s).meromorphicAt)
    (fun s _ => (hm.analyticAt s).meromorphicAt)
    (fun s hs => by
      rw [(hIch v s hs (archDiagonal w z * g)).2, (hIch v s hs g).2]
      exact chamber_transformation C v s hs w z g)
    (hcont _ _) (hcont _ _) hp.continuous.continuousAt hq.continuous.continuousAt
    hm.continuous.continuousAt hC hD
  rw [weylWeight_zero] at he
  exact he

theorem constantTerm_of_jointForwardIdentitySources (C : JointForwardIdentitySources R N) :
    ResidualConstantTerm R C.sources C.realization where
  integrable := residue_integrable C
  radial := selected_residue_radial C

end ChamberPeriods

theorem residual_constant_term (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) (N : TraceHaarTransport R)
    (prior : Nonempty (JointForwardIdentitySources R N)) : Nonempty (JointResidualConstantTermSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨{ toJointForwardIdentitySources := C, constantTerm := ChamberPeriods.constantTerm_of_jointForwardIdentitySources C }⟩
end DedekindZetaZeroFree.ThetaExpansion

end
