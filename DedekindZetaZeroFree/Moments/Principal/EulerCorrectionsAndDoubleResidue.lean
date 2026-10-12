module

public import DedekindZetaZeroFree.LFunctions.Hecke.UniformRegularizationBoundaryBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.RegularizationStripGrowth
public import DedekindZetaZeroFree.Analysis.PhragmenLindelof.PolynomialBoundaryBounds
public import DedekindZetaZeroFree.ZeroDetection.Conductors.HolomorphicLogarithmControl
public import DedekindZetaZeroFree.Moments.Principal.Corrections.ThreeVariableProductAndContinuation
public import DedekindZetaZeroFree.Moments.Principal.Corrections.PrincipalSpecialization
public import DedekindZetaZeroFree.Moments.Principal.Corrections.SummableMajorants
public import DedekindZetaZeroFree.Moments.Reflected.ProbeExponentBound
public import DedekindZetaZeroFree.Arithmetic.Units.SixthPowerRepresentatives
public import DedekindZetaZeroFree.Arithmetic.Kummer.QuadraticCharacterFamilyAndConductorShape
public import DedekindZetaZeroFree.Moments.Probes.ForwardGaussianSeriesBounds
public import DedekindZetaZeroFree.Moments.Probes.NormalizedPrincipalProbeExistence

@[expose] public section

open scoped NumberField Classical Topology

noncomputable section
namespace DedekindZetaZeroFree.PrincipalCorrection
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors InitialSeparatedEuler
open FrequencyCharacterMasks MaskedHeckeMeromorphic MeromorphicSeparationGluing

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem probe_arithmetic_compatibility
    (C : A.GeneralArithmeticContext σ η hS)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (hPC : P.correction = C.correction)
    (B : PrincipalProbeConstruction.ArithmeticBinding A σ η hS
      C P.allowed P.coefficients) :
    WeightedFiniteCoefficient.ArithmeticCompatibility A P.coefficients σ η hS
      C.correction := by
  refine ⟨?_, B.fieldTrace, ?_, ?_, ?_⟩
  · intro I
    have hu : WeightedFiniteCoefficient.fieldUnit A (P.coefficients.generator I)
        (P.coefficients.generates I).1 = P.allowed.generator I := by
      apply Units.ext
      exact (B.sameGenerator I).symm
    rw [hu]
    change ThetaReflectionData.rationalClass A (P.allowed.generator I) ∈ C.correction.B
    rw [← B.sameComplement]
    exact P.allowed.allowed I
  · intro I a ha
    ext x
    rw [NormalizedProbe.PrincipalData.character_eq_sexticResiduePowerChar A σ η hS P I a ha]
    have ht {J K : Ideal A.R} (h : J = K) (χ : MulChar (A.R ⧸ J) ℂ)
        (x : A.R ⧸ K) :
        GeneratorInvariance.transportCharacter J K h χ x =
          χ (Ideal.quotientEquivAlgOfEq A.R h.symm x) := by
      subst K
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    exact (ht ha.2.symm _ x).symm
  · intro c
    letI := P.coefficients.finiteResidue (P.coefficients.generator c.val)
      (P.coefficients.generates c.val).1
    letI := A.exteriorResidue_finite c.val
    letI := Fintype.ofFinite (A.R ⧸ A.extendIdeal c.val)
    rw [B.gammaTwo c]
    unfold ThetaReflectionData.gammaTwoRecipe SArithmeticData.idealGauss
    congr 1
    let a := P.coefficients.generator c.val
    let ha := P.coefficients.generates c.val
    let E := Ideal.quotientEquivAlgOfEq A.R ha.2
    unfold FiniteTransform.gaussSum FiniteTransform.gaussSumWithLifts
    apply Fintype.sum_equiv E.toEquiv
    intro x
    have hχ : (P.coefficients.character a ^ 2) x =
        A.sexticResiduePowerChar σ c.val 2 (E x) := by
      rw [MulChar.pow_apply' _ (by norm_num)]
      rw [NormalizedProbe.PrincipalData.character_eq_sexticResiduePowerChar A σ η hS P c.val a ha]
      simp [SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent,
        MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0), E]
    rw [hχ]
    congr 1
    rw [B.fieldTrace]
    have hout : Ideal.Quotient.mk (Ideal.span {a})
        ((FiniteTransform.canonicalLifts A.R.toSubring a).val x) = x :=
      (FiniteTransform.canonicalLifts A.R.toSubring a).property x
    have hE : E.toEquiv x = Ideal.Quotient.mk (A.extendIdeal c.val)
        ((FiniteTransform.canonicalLifts A.R.toSubring a).val x) := by
      conv_lhs => rw [← hout]
      exact Ideal.quotientEquivAlgOfEq_mk A.R ha.2 _
    rw [hE, SArithmeticData.residueTraceCharacter_apply]
    change (A.fieldTraceCharacter ((1 : F) *
      ((FiniteTransform.canonicalLifts A.R.toSubring a).val x : F) / (a : F)) : ℂ) = _
    rw [one_mul]
  · intro a ha
    rw [B.theta ⟨a, ha⟩]
    have hηid : C.correction.η_id = 1 := by
      rw [← hPC]
      exact P.principalIdele
    rw [hηid]
    rfl

theorem principal_specialization (C : A.GeneralArithmeticContext σ η hS)
    (U : Frequency C) (hU : U.u = 1) :
    (∀ (p : ExteriorPrime A) (s : ℂ), s ∈ principalRegion →
      localFactor C U p s 1 (1 / 6) = h_p C p s ∧
      h_p C p s =
        (1 - qPower p (-2)) *
          (1 - (1 - qPower p (-1)) * η p.val.asIdeal * qPower p (-s) -
            vartheta C p ^ 6 * qPower p (2 - 6 * s)) /
          ((1 - vartheta C p ^ 6 * qPower p (3 - 6 * s)) *
            (1 - η p.val.asIdeal * qPower p (-s)))) ∧
    (∀ s : ℂ, (499 / 500 : ℝ) - 1 / 100000 < s.re →
      ∃ hm : Multipliable (fun p : ExteriorPrime A => localFactor C U p s 1 (1 / 6)),
        H_u C U s 1 (1 / 6) hm = H_eta C s) := by
  refine ⟨fun p s hs => ⟨principal_localFactor_eq_h_p C U hU p s hs, rfl⟩, ?_⟩
  intro s hs
  exact principal_product_specialization C U hU s hs

end DedekindZetaZeroFree.PrincipalCorrection

end
