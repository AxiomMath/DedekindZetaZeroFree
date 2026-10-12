module

public import DedekindZetaZeroFree.Theta.Unfolding.PrimeGeneratorFrequencyIndex
public import DedekindZetaZeroFree.Theta.Unfolding.SignedIdentityFromEvaluations

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma groupedOrbitTerm_forward_generator {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m)
    (Z : ℝ) (hZ : 0 < Z) (j : ForwardIndex R) :
    groupedOrbitTerm R C (QuotientGroup.mk D.epsilon) m true Z hZ (forwardFrequency R j) =
      ThetaReflectionData.forwardSummand R.A R.probe.coefficients m Z j.1 j.2 := by
  let a := forwardGenerator R j.1 j.2
  have he : (QuotientGroup.mk (Quotient.out (forwardFrequency R j)) : ThetaReflectionData.Frequency R.A) =
      QuotientGroup.mk a := Quotient.out_eq _
  have hg : ThetaReflectionData.rationalClass R.A (Quotient.out (forwardFrequency R j)) ∈
      R.probe.correction.B := by
    have hh := congrArg (ThetaReflectionData.frequencyClass R.A) he
    simp only [ThetaReflectionData.frequencyClass_mk] at hh
    rw [hh]
    exact forwardGenerator_allowed R j.1 j.2
  have hi : (Quotient.out (forwardFrequency R j) : Fˣ).val ∈ R.A.R := by
    let γ : ThetaReflectionData.rationalGamma R.A :=
      ⟨Quotient.out (forwardFrequency R j) / a, QuotientGroup.eq_iff_div_mem.mp he⟩
    have h : Quotient.out (forwardFrequency R j) = a * γ.val := by dsimp [γ]; simp
    rw [h]
    have ha := forwardGenerator_integral R j.1 j.2
    intro p hp
    simp only [Units.val_mul, map_mul, gamma_valuation R γ ⟨p, hp⟩, mul_one]
    exact ha p hp
  rw [groupedOrbitTerm_forward_allowed R C hx _ m _ Z hZ hi hg,
    forwardMask_eq_of_frequency_eq R m _ a he,
    forwardExterior_eq_of_frequency_eq R C _ a he,
    L_eq_of_frequency_eq R C _ _ a he]
  have hq : (q R.A (Quotient.out (forwardFrequency R j))).val = (q R.A a).val := by
    exact congrArg (ThetaReflectionData.frequencyNorm R.A) he
  rw [hq]
  have hm := forwardMask_mul_L R m D (forwardIdeal R j.1 j.2)
    (ThetaReflectionData.forwardModulus R.A R.probe.coefficients j.1 j.2) a
    (forwardModulus_generates R j.1 j.2) (forwardGenerator_val R j.1 j.2)
    (forwardGenerator_allowed R j.1 j.2)
  change _ = _ at hm
  have hmul : forwardMask R m a * forwardExterior R C a * Characters.L R (QuotientGroup.mk D.epsilon) a =
      forwardExterior R C a * (forwardMask R m a * Characters.L R (QuotientGroup.mk D.epsilon) a) := by ring
  rw [hmul, hm, forwardExterior_generator R C, ← forwardGenerator_theta,
    forwardGenerator_norm R, ← forwardGenerator_rowCharacter]
  unfold ThetaReflectionData.forwardSummand ThetaReflectionData.forwardArithmeticWeight
  ring

lemma groupedOrbitTerm_forward_support {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (Z : ℝ) (hZ : 0 < Z) (ξ : ThetaReflectionData.Frequency R.A)
    (hξ : groupedOrbitTerm R C v m true Z hZ ξ ≠ 0) :
    ξ ∈ Set.range (forwardFrequency R) := by
  by_cases ha : (Quotient.out ξ : Fˣ).val ∈ R.A.R
  · by_cases hb : ThetaReflectionData.rationalClass R.A (Quotient.out ξ) ∈ R.probe.correction.B
    · have he := groupedOrbitTerm_forward_allowed R C hx v m ξ Z hZ ha hb
      have hn : forwardExterior R C (Quotient.out ξ) ≠ 0 := by
        intro hz
        rw [hz, mul_zero, zero_mul, zero_mul] at he
        exact hξ he
      obtain ⟨j, hj⟩ := forwardFrequency_exists R (Quotient.out ξ) hb
        (fun p => forwardExterior_supported R C _ hn p)
      exact ⟨j, hj.trans (Quotient.out_eq ξ)⟩
    · exact False.elim (hξ (groupedOrbitTerm_forward_nonallowed R C v m ξ Z hZ ha hb))
  · exact False.elim (hξ (groupedOrbitTerm_forward_nonintegral R C v m ξ Z hZ ha))

theorem forward_orbit_evaluation {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (u : R.A.Rˣ) (h d : R.A.Exterior)
    (hh : Powerful h.val) (hd : Squarefree d.val) (hc : h.val ⊔ d.val = ⊤)
    (Z : ℝ) (hZ : 0 < Z) :
    HasSum (orbitTerm R C (rowClass R u)
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z hZ)
      (ThetaReflectionData.forwardB R.A R.probe.coefficients
        (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z) := by
  let m := ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d
  obtain ⟨D, _, _⟩ := SignedUnfoldingSub7.dyadic_row_factorization R u h d hh hd hc
  have hv := dyadicRow_companion R u h d D
  have heval (j : ForwardIndex R) : groupedOrbitTerm R C (rowClass R u) m true Z hZ (forwardFrequency R j) =
      ThetaReflectionData.forwardSummand R.A R.probe.coefficients m Z j.1 j.2 := by
    rw [← hv]
    exact groupedOrbitTerm_forward_generator R C hx m D Z hZ j
  have heq : (∑' ξ, groupedOrbitTerm R C (rowClass R u) m true Z hZ ξ) =
      ThetaReflectionData.forwardB R.A R.probe.coefficients m Z := by
    rw [← (forwardFrequency_injective R).tsum_eq
      (fun ξ => groupedOrbitTerm_forward_support R C hx (rowClass R u) m Z hZ ξ)]
    simp_rw [heval]
    exact (MomentSources.forward_hasSum R m Z hZ).tsum_eq
  have hg := groupedOrbitTerm_hasSum R C hx (rowClass R u) m true Z hZ
  have hall := (hx (rowClass R u) m true Z hZ).2.2.1.of_norm.hasSum
  have htotal : (∑' i, orbitTerm R C (rowClass R u) m true Z hZ i) =
      ThetaReflectionData.forwardB R.A R.probe.coefficients m Z := hg.tsum_eq.symm.trans heq
  rw [← htotal]
  exact hall

end DedekindZetaZeroFree.OrbitExpansion

end
