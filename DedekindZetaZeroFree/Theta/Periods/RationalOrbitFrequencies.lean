module

public import DedekindZetaZeroFree.Theta.Whittaker.FourierPeriodRegularity
public import DedekindZetaZeroFree.Theta.Periods.WeightedQuotientIntegrability
public import DedekindZetaZeroFree.Adeles.Quotients.RationalDilation
public import DedekindZetaZeroFree.Adeles.Characters.QuotientParametrizationAndAnnihilator

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def rationalCharacter (_R : PrincipalMellin.ActualRecipe S η) (a : Fˣ) (q : KPAdditiveQuotient F) : Circle :=
  adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * Quotient.out q)

lemma rationalCharacter_eq (a : Fˣ) (q : KPAdditiveQuotient F) :
    rationalCharacter R a q =
      KPAdelicQuotient.rationalTraceQuotientCharacter F (a : F) q := by
  have h := KPAdelicQuotient.rationalTraceQuotientCharacter_mk F (a : F) (Quotient.out q)
  have hq : KPAdelicQuotient.quotientMap F (Quotient.out q) = q := Quotient.out_eq q
  rw [hq] at h
  exact h.symm

theorem rationalCharacter_continuous (a : Fˣ) : Continuous (rationalCharacter R a) := by
  have he : rationalCharacter R a = KPAdelicQuotient.rationalTraceQuotientCharacter F (a : F) :=
    funext (rationalCharacter_eq R a)
  rw [he]
  exact KPAdelicQuotient.continuous_rationalTraceQuotientCharacter F (a : F)

def rationalIntegrand {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) (q : KPAdditiveQuotient F) : ℂ :=
  T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (Quotient.out q) * g) * star (rationalCharacter R a q : ℂ)

def rationalValue {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) : ℂ :=
  ∫ q, rationalIntegrand R T v a g q ∂Q.dq

theorem rationalIntegrand_joint_continuous {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (a : Fˣ) :
    Continuous (fun p : KPAdditiveQuotient F × Group R =>
      rationalIntegrand R T v a p.2 p.1) := by
  exact (SheetRescaling.theta_quotient_joint_continuous T v).mul
    (((continuous_subtype_val.comp (rationalCharacter_continuous R a)).star).comp continuous_fst)

theorem rationalIntegrand_integrable {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) :
    Integrable (rationalIntegrand R T v a g) Q.dq := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have hc := (rationalIntegrand_joint_continuous R T v a).comp
    (continuous_id.prodMk (continuous_const (y := g)))
  simpa [Function.comp_def] using
    hc.continuousOn.integrableOn_compact' (μ := Q.dq) isCompact_univ MeasurableSet.univ

theorem rationalValue_continuous {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (a : Fˣ) :
    Continuous (rationalValue R T v a) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
  · exact ((rationalIntegrand_joint_continuous R T v a).comp continuous_swap).continuousOn
  · intro p x hp hx
    exact False.elim (hx (Set.mem_univ x))

theorem frequencyIntegrand_integrable {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient)
    (ξ : ThetaReflectionData.Frequency R.A) (g : Group R) :
    Integrable (frequencyIntegrand R Q T v ξ g) Q.dq :=
  rationalIntegrand_integrable R T v (Quotient.out ξ) g

theorem orbitFrequencyIntegrand_integrable {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (g : Group R) : Integrable (orbitFrequencyIntegrand R Q T v i g) Q.dq :=
  rationalIntegrand_integrable R T v ((Quotient.out i.1) * i.2.val) g

theorem frequencyValue_continuous {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient)
    (ξ : ThetaReflectionData.Frequency R.A) :
    Continuous (frequencyValue R Q T v ξ) :=
  rationalValue_continuous R T v (Quotient.out ξ)

theorem orbitFrequencyValue_continuous {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient)
    (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A) :
    Continuous (orbitFrequencyValue R Q T v i) :=
  rationalValue_continuous R T v ((Quotient.out i.1) * i.2.val)

end DedekindZetaZeroFree.OrbitFrequencies

end
