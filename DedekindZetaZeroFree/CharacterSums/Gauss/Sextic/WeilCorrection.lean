module

public import DedekindZetaZeroFree.CharacterSums.Gauss.Sextic.LocalTable

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.CanonicalGaussCorrection
open LocalFiniteSums CanonicalLocalGaussTable
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem depth_one_mask_eq (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (a : ℤ) (x : Residue C p 1) :
    maskedPower C p 1 a x = A.sexticResiduePowerChar σ (primeIdeal p) a (depthOneEquiv C p x) := by
  have hr : reduction C p 1 (by decide) x = depthOneEquiv C p x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [reduction, depthOneEquiv, Ideal.quotEquivOfEq_mk]
  unfold maskedPower
  rw [dif_neg (show (1 : ℕ) ≠ 0 by decide), hr]
  split_ifs with hx
  · rfl
  · symm
    apply A.sexticResiduePowerChar_nonunit
    intro hu
    exact hx (by simpa using hu.map (depthOneEquiv C p).symm.toRingHom)
private theorem qPower_neg_half (p : ExteriorPrime A) : qPower p (-1 / 2) = (Real.sqrt (Q p) : ℂ)⁻¹ := by
  unfold qPower
  have heq : (-1 / 2 : ℂ) * (Real.log (Q p) : ℂ) = -((Real.log (Q p) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hpos : 0 < Q p := lt_of_lt_of_le zero_lt_one (idealNorm_ge_one p.val.asIdeal p.val.ne_bot)
  rw [heq, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hpos]
private theorem depth_one_trace_eq (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (x : Residue C p 1) :
    quotientTrace C p 1 x = A.residueTraceCharacter hS (primeIdeal p) (generator C p)
      (generator_generates C p) (depthOneEquiv C p x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotientTrace C p 1 (residueMap C p 1 x) = _
  rw [LocalFiniteSumCompatibility.quotientTrace_mk]
  simp only [depthOneEquiv, Ideal.quotEquivOfEq_mk, A.residueTraceCharacter_apply]
  rw [← LocalFiniteSumCompatibility.fieldTrace_eq_negative_localTrace C p 1 x]
  simp

theorem tau_mul_qPower_eq_idealGauss (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) :
    tau C p a * qPower p (-1 / 2) =
      A.idealGauss σ hS (primeIdeal p) (generator C p) (generator_generates C p) a := by
  rw [qPower_neg_half]
  unfold tau T
  simp only [one_mul]
  unfold SArithmeticData.idealGauss
  rw [mul_comm]
  congr 1
  letI : Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) := A.exteriorResidue_finite _
  letI : Fintype (A.R ⧸ A.extendIdeal (primeIdeal p)) := Fintype.ofFinite _
  apply Fintype.sum_equiv (depthOneEquiv C p).toEquiv
  intro x
  rw [depth_one_mask_eq]
  unfold psi
  rw [depth_one_trace_eq]
  rfl

theorem gammaTwo_vartheta_tau_one (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    gammaTwo C p * vartheta C p * tau C p 1 * qPower p (-1 / 2) =
      -η p.val.asIdeal := by
  obtain ⟨x, hx⟩ := A.exists_exterior_ideal_representative (primeIdeal p)
  let a := Units.mk0 (generator C p : F)
    (by exact_mod_cast (generator_generates C p).1)
  have hp := C.correction.prime_theta (primeIdeal p) p.val rfl
    (generator C p) (generator_generates C p) a (generator_allowed C p) rfl x hx
  have hv : vartheta C p =
      (A.correctionTheta C.correction.Λ C.correction.G C.correction.η_id
        (QuotientGroup.mk x) : ℂ) := by
    exact congrArg (fun t : Circle => (t : ℂ))
      (C.correction.theta_ideal_local (primeIdeal p) x a (generator C p) hx
        (generator_generates C p) rfl).symm
  calc
    _ = (tau C p 1 * qPower p (-1 / 2)) * gammaTwo C p * vartheta C p := by ring
    _ = _ := by rw [tau_mul_qPower_eq_idealGauss, hv]; exact hp

end DedekindZetaZeroFree.CanonicalGaussCorrection

end
