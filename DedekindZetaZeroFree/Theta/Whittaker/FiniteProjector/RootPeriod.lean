module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.PeriodLinearity
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.QuotientDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField MeasureTheory
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

private lemma circle_mul_star (z : Circle) : (z : ℂ) * star (z : ℂ) = 1 := by
  have hs : star (z : ℂ) = (↑(z⁻¹) : ℂ) := (Circle.coe_inv_eq_conj z).symm
  rw [hs, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]

lemma root_integrand_mk (f : Functions R)
    (hf : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (x : KPAdeles F) (g : Group R) :
    f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out (QuotientAddGroup.mk x : KPAdditiveQuotient F)) * g) =
    f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add
    (AdeleRing.principalSubgroup (𝓞 F) F) x
  obtain ⟨t, ht⟩ := r.property
  rw [hr, ← ht, add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc,
    ← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact hf _ _

lemma root_integrand_add (f : Functions R)
    (hf : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (q : KPAdditiveQuotient F) (x : KPAdeles F) (g : Group R) :
    f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g)) =
    f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out (q + QuotientAddGroup.mk x)) * g) := by
  have hq : (QuotientAddGroup.mk (Quotient.out q) : KPAdditiveQuotient F) = q := Quotient.out_eq q
  conv_rhs => rw [← hq, ← QuotientAddGroup.mk_add, root_integrand_mk R f hf]
  rw [KPGlobalTorusFunctionData.N_add, mul_assoc]

theorem fourier_upper (dq : Measure (KPAdditiveQuotient F)) [dq.IsAddHaarMeasure]
    (f : Functions R)
    (hf : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (x : KPAdeles F) (g : Group R)
    (_hbase : PeriodIntegrable R dq f g)
    (_hshift : PeriodIntegrable R dq f
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g)) :
    MomentSources.fourier R dq f
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ) * MomentSources.fourier R dq f g := by
  unfold MomentSources.fourier
  simp_rw [root_integrand_add R f hf]
  let t : KPAdditiveQuotient F := QuotientAddGroup.mk x
  have heq (q : KPAdditiveQuotient F) :
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (q + t)) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ) =
      (adelicTraceQuotientCharacter F t : ℂ) *
        (f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (q + t)) * g) *
          star (adelicTraceQuotientCharacter F (q + t) : ℂ)) := by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, star_mul]
    have hi : (adelicTraceQuotientCharacter F t : ℂ) *
        star (adelicTraceQuotientCharacter F t : ℂ) = 1 :=
      circle_mul_star (adelicTraceQuotientCharacter F t)
    calc
      _ = ((adelicTraceQuotientCharacter F t : ℂ) * star (adelicTraceQuotientCharacter F t : ℂ)) *
          (f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out (q + t)) * g) *
            star (adelicTraceQuotientCharacter F q : ℂ)) := by rw [hi, one_mul]
      _ = _ := by ring
  refine (integral_congr_ae (Filter.Eventually.of_forall heq)).trans ?_
  refine (integral_const_mul _ _).trans ?_
  exact congrArg (fun z : ℂ => (adelicTraceQuotientCharacter F t : ℂ) * z)
    (integral_add_right_eq_self (μ := dq) (fun q : KPAdditiveQuotient F =>
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) t)

theorem stage08_fourier_upper {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (v : R.A.UnitQuotient) (x : KPAdeles F) (g : Group R) :
    MomentSources.fourier R A.sources.dq (A.realization.theta v)
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ) *
        MomentSources.fourier R A.sources.dq (A.realization.theta v) g := by
  letI := A.sources.quotientHaar
  exact fourier_upper R A.sources.dq (A.realization.theta v)
    (A.realization.automorphic v).2.1 x g
    (A.factorization.period_integrable v g)
    (A.factorization.period_integrable v _)

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
