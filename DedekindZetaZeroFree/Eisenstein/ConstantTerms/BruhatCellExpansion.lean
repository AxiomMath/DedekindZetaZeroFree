module

public import DedekindZetaZeroFree.Eisenstein.Continuation.UpperRootPeriods

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
open _root_.DedekindZetaZeroFree.KPLiteralChamberWeight renaming standard_integrable → standard_integrable
open _root_.DedekindZetaZeroFree.KPLiteralChamberWeight renaming literal_two_cells → literal_two_cells

def outgoing (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient) (s : ℂ) (g : Group R) : ℂ :=
  ∫ x : KPAdeles F, incoming C v s
    (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g)
    ∂KPAdditiveHaar.adelicMeasure F

theorem chamber_norm_summable (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    Summable (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
      ‖incoming C v s (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out c) * g)‖) := by
  obtain ⟨b, hb, hbound⟩ := KPLiteralChamber.chamber_scalar_compact_majorants
    F R.A.zeta12 R.A.primitive_zeta12 C.sources.K C.sources.iwasawa (C.sources.flat v)
    {s} isCompact_singleton (by rintro t rfl; exact hs) {g} isCompact_singleton
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hb
  intro c
  exact hbound c s (Set.mem_singleton s) g (Set.mem_singleton g)

theorem outgoing_integrable (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    Integrable (fun x : KPAdeles F => incoming C v s
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g))
      (KPAdditiveHaar.adelicMeasure F) :=
  standard_integrable F R.A.zeta12 R.A.primitive_zeta12 C.sources.K
    C.sources.iwasawa (C.sources.flat v) s hs g

theorem chamber_two_cells_identity (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    chamberPeriod C v s g = incoming C v s g + outgoing C v s g := by
  have hmass : C.sources.dq.real Set.univ = 1 := by
    simp [Measure.real, C.sources.probability]
  have h := literal_two_cells F R.A.zeta12 R.A.primitive_zeta12 C.sources.K
    C.sources.iwasawa C.sources.dq C.sources.quotientHaar (C.sources.flat v) s hs g
  rw [hmass, Complex.ofReal_one, one_mul] at h
  exact h

theorem chamber_upper_integrable (C : JointForwardIdentitySources R N) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    Integrable (fun q => KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
      C.sources.K (C.sources.flat v) s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out q) * g)) C.sources.dq :=
  DedekindZetaZeroFree.CompactPeriodAnalyticity.Chamber.upper_integrable F R.A.zeta12 R.A.primitive_zeta12
    C.sources.K C.sources.iwasawa (C.sources.flat v) C.sources.dq C.sources.quotientHaar s hs g

theorem selected_chamber_two_cells (C : JointForwardIdentitySources R N) :
    ∀ v s, (1 / 3 : ℝ) < s.re → ∀ g,
      Summable (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
        ‖incoming C v s (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12
          (Quotient.out c) * g)‖) ∧
      Integrable (fun q => KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        C.sources.K (C.sources.flat v) s
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) C.sources.dq ∧
      Integrable (fun x : KPAdeles F => incoming C v s
        (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
          KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g))
        (KPAdditiveHaar.adelicMeasure F) ∧
      chamberPeriod C v s g = incoming C v s g + outgoing C v s g := by
  intro v s hs g
  refine ⟨chamber_norm_summable C v s hs g, ?_,
    outgoing_integrable C v s hs g, chamber_two_cells_identity C v s hs g⟩
  exact chamber_upper_integrable C v s hs g

end DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods

end
