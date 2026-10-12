module

public import DedekindZetaZeroFree.Theta.Periods.RationalPeriodContinuity
public import DedekindZetaZeroFree.Adeles.Characters.StandardAdditiveCharacter
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.RationalFourierExpansion

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical Topology
open _root_.DedekindZetaZeroFree.ThetaRationalFourierSummation renaming hasSum_of_summable_coefficients → hasSum_of_summable_coefficients
open _root_.DedekindZetaZeroFree.ThetaRationalFourierSummation renaming freq → freq
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem negativeFrequency_eq_star_rationalCharacter (a : F) (q : KPAdditiveQuotient F) :
    freq F (PrincipalOfKP.standardCharacter F) a q =
      star (adelicRationalFrequencyQuotientCharacter F a q : ℂ) := by
  change (adelicTraceQuotientCharacter F
    (QuotientAddGroup.mk (-(algebraMap F (KPAdeles F) a * Quotient.out q))) : ℂ) = _
  rw [show (QuotientAddGroup.mk (-(algebraMap F (KPAdeles F) a * Quotient.out q)) :
    KPAdditiveQuotient F) = QuotientAddGroup.mk'
      (AdeleRing.principalSubgroup (𝓞 F) F)
        (-(algebraMap F (KPAdeles F) a * Quotient.out q)) from rfl,
    adelicTraceQuotientCharacter_mk, AddChar.map_neg_eq_inv, Circle.coe_inv,
    rationalCharacter_out]
  exact Complex.inv_eq_conj (Circle.norm_coe _)

theorem rationalPeriod_hasSum_of_norm_summable {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (g : Group R)
    (hs : Summable (fun a : F => ‖rationalPeriod R T v a g‖)) :
    HasSum (fun a : F => rationalPeriod R T v a g) (T.theta v g) := by
  letI : Q.dq.IsAddHaarMeasure := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have he (a : F) : (∫ q, thetaFiber R T v g q *
      freq F (PrincipalOfKP.standardCharacter F) a q ∂Q.dq) =
        rationalPeriod R T v a g := by
    simp only [negativeFrequency_eq_star_rationalCharacter, rationalPeriod]
  have h := hasSum_of_summable_coefficients F (PrincipalOfKP.standardCharacter F)
    (PrincipalOfKP.standardCharacter_nontrivial F) Q.dq (thetaFiber R T v g)
    (thetaFiber_continuous R T v g) (by simpa only [he] using hs)
  simpa only [he, thetaFiber_zero] using h

theorem orbitFrequencyValue_hasSum_of_rationalPeriod_norm_summable
    {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R)
    (hs : Summable (fun a : F => ‖rationalPeriod R T v a g‖)) :
    HasSum (fun i : OrbitIndex R => orbitFrequencyValue R Q T v i g)
      (T.theta v g - upper R Q.dq (T.theta v) g) := by
  have ht := hasSum_ite_sub_hasSum (rationalPeriod_hasSum_of_norm_summable R T v g hs) (0 : F)
  have hsupport : Function.support (fun a : F =>
      if a = 0 then 0 else rationalPeriod R T v a g) ⊆ {a : F | a ≠ 0} := by
    intro a ha
    by_contra h
    simp only [Set.mem_setOf_eq, not_not] at h
    subst a
    simpa using ha
  have ht' := (hasSum_subtype_iff_of_support_subset hsupport).mpr ht
  have ht'' := (unitsEquivNeZero.hasSum_iff).mpr ht'
  rw [rationalPeriod_zero] at ht''
  have hu : HasSum (fun a : Fˣ => rationalPeriod R T v (a : F) g)
      (T.theta v g - upper R Q.dq (T.theta v) g) := by
    convert ht'' using 1
    funext a
    change rationalPeriod R T v (a : F) g =
      if (a : F) = 0 then 0 else rationalPeriod R T v (a : F) g
    rw [if_neg a.ne_zero]
  have hr := (hasSum_orbitFrequency_iff R _ _).mpr hu
  simpa only [orbitFrequencyValue_eq_rationalPeriod] using hr

theorem rationalPeriod_norm_summable_at_smooth_level {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (g : Group R)
    (K : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
    (hKc : IsCompact (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
    (hKo : IsOpen (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
    (hl : HasSmoothAdditiveLevel K (thetaFiber R T v g))
    (hj : IsArchSmooth (thetaFiber R T v g)) :
    Summable (fun a : F => ‖rationalPeriod R T v a g‖) := by
  letI : Q.dq.IsAddHaarMeasure := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  let f := thetaFiber R T v g
  have hB (n : ℕ) (v : Fin n → mixedEmbedding.mixedSpace F) :
      BddAbove (Set.range (fun q => ‖smoothArchJet n f q v‖)) :=
    (isCompact_range (((hj.2.2 n).eval continuous_const).norm)).bddAbove
  have hunif : IsUniformArchSmoothFamily (fun z : Unit × KPAdditiveQuotient F => f z.2)
      (fun n v => sSup (Set.range (fun q => ‖smoothArchJet n f q v‖))) := by
    refine ⟨hj.1.comp continuous_snd, fun _ => hj,
      fun n => (hj.2.2 n).comp continuous_snd, ?_⟩
    intro n v p q
    exact le_csSup (hB n v) (Set.mem_range_self q)
  obtain ⟨b, hb, hp, hbound⟩ := ThetaRationalFourierSummation.rational_fourier_uniform_majorant F
    (PrincipalOfKP.standardCharacter F) (PrincipalOfKP.standardCharacter_nontrivial F)
    Q.dq K hKc hKo (fun z : Unit × KPAdditiveQuotient F => f z.2)
    (fun _ => hl) _ hunif
  apply hb.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro a
  have h := hbound () a
  change ‖∫ q, f q * freq F (PrincipalOfKP.standardCharacter F) a q ∂Q.dq‖ ≤ b a at h
  simpa only [negativeFrequency_eq_star_rationalCharacter, f, rationalPeriod] using h

theorem orbitSheet_hasSum_of_rationalPeriod_norm_summable
    {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (l : ThetaProfileHaarSheets.PositiveAxis) (z : ThetaProfileHaarSheets.Sheet R.A l)
    (hs : ∀ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
      Summable (fun a : F => ‖rationalPeriod R C.realization v a
        (signedArgument R m b z.val d)‖)) :
    HasSum (fun i : OrbitIndex R => orbitSheet R C v m b i l z)
      (weightedDigits R C.sources C.realization C.packet v m b z.val -
        weightedUpper R C.sources C.realization C.packet v m b z.val) := by
  have hh := hasSum_sum (s := Finset.univ) (fun d _ =>
    (orbitFrequencyValue_hasSum_of_rationalPeriod_norm_summable R C.realization v
      (signedArgument R m b z.val d) (hs d)).mul_left
        (digitWeight R m d))
  have hh := (hh.mul_left ((C.packet.branch v z.val)⁻¹)).mul_left
    (if QuotientGroup.mk' R.A.sixthPowers z.val ∈ R.probe.correction.B
      then (1 : ℂ) else 0)
  simpa only [orbitSheet, weightedDigits,
    weightedUpper, signedDigits, upperDigits, Finset.sum_sub_distrib, mul_sub, mul_assoc] using hh

end DedekindZetaZeroFree.OrbitExpansion

end
