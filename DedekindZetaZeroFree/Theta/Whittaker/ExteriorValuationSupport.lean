module

public import DedekindZetaZeroFree.Theta.Whittaker.RationalDiagonalFactorization
public import DedekindZetaZeroFree.Theta.Digits.ForwardMaskInversion

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming order_finite_support → order_finite_support
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma order_eq_zero_iff (p : KPFinitePlace F) (a : Fˣ) :
    ThetaBranch.order p a = 0 ↔ p.valuation F (a : F) = 1 := by
  have hn : p.valuation F (a : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  constructor
  · intro h
    have hh : WithZero.log (p.valuation F (a : F)) = 0 := neg_eq_zero.mp h
    rw [← WithZero.exp_log hn, hh, WithZero.exp_zero]
  · intro h
    simp [ThetaBranch.order, h]

lemma exterior_order_support_finite (a : Fˣ) :
    {p : ThetaBranch.ExteriorPrime R.A | ThetaBranch.order p.val a ≠ 0}.Finite :=
  (order_finite_support a).preimage Subtype.val_injective.injOn

lemma sphericalFactor_order_zero (p : ThetaBranch.ExteriorPrime R.A) (a : Fˣ)
    (ha : ThetaBranch.order p.val a = 0) :
    ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p a = 1 := by
  simp [ThetaBranch.sphericalFactor, ha, sexticSphericalCoefficient]

lemma exteriorValue_unit {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (p : ThetaBranch.ExteriorPrime R.A) (a : Fˣ) (ha : p.val.valuation F (a : F) = 1) :
    C.factorization.exteriorValue R p a = 1 := by
  rw [C.exterior.rational_exact]
  exact sphericalFactor_order_zero R p a ((order_eq_zero_iff p.val a).mpr ha)

def forwardExterior {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N) (a : Fˣ) : ℂ :=
  ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, C.factorization.exteriorValue R p a

lemma forwardExterior_finite {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N) (a : Fˣ) :
    Function.HasFiniteMulSupport (fun p => C.factorization.exteriorValue R p a) := by
  apply (exterior_order_support_finite R a).subset
  intro p hp
  by_contra hn
  simp only [Set.mem_setOf_eq, not_not] at hn
  exact hp (exteriorValue_unit R C p a ((order_eq_zero_iff p.val a).mp hn))

lemma forwardExterior_eq_prod {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (a : Fˣ) (P : Finset (ThetaBranch.ExteriorPrime R.A))
    (hP : ∀ p ∉ P, p.val.valuation F (a : F) = 1) :
    forwardExterior R C a = ∏ p ∈ P, C.factorization.exteriorValue R p a := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hn
  exact hp (exteriorValue_unit R C p a (hP p hn))

lemma fourier_rational_finprod {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (a : Fˣ) (y : R.A.G) :
    OrbitFrequencies.rationalValue R C.realization v a (diagonal R y) =
      forwardExterior R C a * (R.σ ((R.A.H_S (R.A.diagonal a) y : Fˣ) : F) ^ 2)⁻¹ *
        C.packet.forwardProfile v (R.A.diagonal a * y) := by
  let P := (exterior_order_support_finite R a).toFinset
  have hp (p : ThetaBranch.ExteriorPrime R.A) (h : p ∉ P) :
      p.val.valuation F (a : F) = 1 := by
    apply (order_eq_zero_iff p.val a).mp
    simpa only [P, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using h
  rw [OrbitFrequencies.rationalValue_eq_fourier]
  rw [fourier_rational_diagonal R C v a y P.toList P.nodup_toList
    (by simpa only [Finset.mem_toList] using hp)]
  rw [forwardExterior_eq_prod R C a P hp]
  congr 2
  exact Finset.prod_map_toList _ _

lemma order_negative_of_valuation_gt_one (p : KPFinitePlace F) (a : Fˣ)
    (ha : 1 < p.valuation F (a : F)) : ThetaBranch.order p a < 0 := by
  have hn : p.valuation F (a : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  have he : WithZero.exp (0 : ℤ) < WithZero.exp (WithZero.log (p.valuation F (a : F))) := by
    simpa only [WithZero.exp_zero, WithZero.exp_log hn] using ha
  have hl : 0 < WithZero.log (p.valuation F (a : F)) := WithZero.exp_lt_exp.mp he
  exact neg_neg_of_pos hl

lemma forwardExterior_nonintegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (a : Fˣ) (p : ThetaBranch.ExteriorPrime R.A) (ha : 1 < p.val.valuation F (a : F)) :
    forwardExterior R C a = 0 := by
  unfold forwardExterior
  apply finprod_eq_zero _ p _ (forwardExterior_finite R C a)
  rw [C.exterior.rational_exact]
  simp only [ThetaBranch.sphericalFactor, sexticSphericalCoefficient,
    if_pos (order_negative_of_valuation_gt_one p.val a ha), zero_mul]

lemma rationalValue_nonintegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (a : Fˣ) (y : R.A.G)
    (ha : (a : F) ∉ R.A.R) :
    OrbitFrequencies.rationalValue R C.realization v a (diagonal R y) = 0 := by
  have hn : ∃ p : ThetaBranch.ExteriorPrime R.A, 1 < p.val.valuation F (a : F) := by
    change ¬ (∀ p, p ∉ R.A.Sf → p.valuation F (a : F) ≤ 1) at ha
    push Not at ha
    obtain ⟨p, hp, hv⟩ := ha
    exact ⟨⟨p, hp⟩, hv⟩
  obtain ⟨p, hp⟩ := hn
  rw [fourier_rational_finprod, forwardExterior_nonintegral R C a p hp, zero_mul, zero_mul]

lemma forward_digits_nonintegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (i : ThetaExpansion.SignedExpansion.OrbitIndex R) (y : R.A.G)
    (ha : (orbitFrequency R i : F) ∉ R.A.R) :
    (∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
      digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
        (signedArgument R m true y d)) = 0 := by
  rw [forward_digit_average]
  have hv : orbitFrequencyValue R C.sources C.realization v i (diagonal R y) = 0 :=
    rationalValue_nonintegral R C v (orbitFrequency R i) y ha
  rw [hv, mul_zero]

end DedekindZetaZeroFree.OrbitExpansion

end
