module

public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.PoissonOrbitEvaluation
public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.AbsoluteIntegralExchanges

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.TripleMellin
open TripleMellinRaw
noncomputable section
open MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

abbrev FrequencyIndex (P : PrincipalData A σ η hS) :=
  {u // u ∈ P.frequencies.reps} × A.Exterior

def frequencyRow (P : PrincipalData A σ η hS) (j : FrequencyIndex P) :
    ProbeOrbitNormSum.Nonzero A :=
  ⟨j.1.val.val * P.coefficients.generator j.2 ^ 6,
    mul_ne_zero j.1.val.property (pow_ne_zero _ (P.coefficients.generates j.2).1)⟩

def frequencyOrbit (P : PrincipalData A σ η hS) (j : FrequencyIndex P) :
    ProbeOrbitNormSum.Orbit A := ProbeOrbitNormSum.orbitMk A (frequencyRow P j)

private lemma rowUnit_frequencyRow (P : PrincipalData A σ η hS) (j : FrequencyIndex P) :
    ThetaReflectionData.rowUnit A (frequencyRow P j) =
      ThetaReflectionData.rowUnit A j.1.val * P.allowed.generator j.2 ^ 6 := by
  apply Units.ext
  simp only [frequencyRow, ThetaReflectionData.rowUnit, Units.val_mk0, Units.val_mul,
    Units.val_pow_eq_pow_val, Subalgebra.coe_mul, Subalgebra.coe_pow]
  rw [show ((P.coefficients.generator j.2 : A.R) : F) = (P.allowed.generator j.2 : F) from
    (P.sameGenerator j.2).symm]

private lemma gamma_val_eq_sixth (γ : ProbeOrbitNormSum.Gamma A) :
    ∃ δ : A.U, (γ.val : Fˣ) = (δ : Fˣ) ^ 6 := by
  obtain ⟨δ, hδ⟩ := γ.property
  refine ⟨δ, ?_⟩
  rw [← hδ, powMonoidHom_apply, Subgroup.coe_pow]

theorem frequencyOrbit_bijective (P : PrincipalData A σ η hS) :
    Function.Bijective (frequencyOrbit P) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨u, I⟩ ⟨u', I'⟩ heq
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact heq.symm)
    obtain ⟨δ, hδ⟩ := gamma_val_eq_sixth γ
    have hF : ((δ : Fˣ) : F) ^ 6 * ((frequencyRow P (u, I)).val : F) =
        ((frequencyRow P (u', I')).val : F) := by
      have h1 : ((γ • frequencyRow P (u, I)).val : F) =
          ((frequencyRow P (u', I')).val : F) :=
        congrArg (fun x : ProbeOrbitNormSum.Nonzero A => (x.val : F)) hγ
      have h2 : ((γ • frequencyRow P (u, I)).val : F) =
          ((δ : Fˣ) : F) ^ 6 * ((frequencyRow P (u, I)).val : F) := by
        change ((γ.val : Fˣ) : F) * ((frequencyRow P (u, I)).val : F) = _
        rw [hδ, Units.val_pow_eq_pow_val]
      rw [h2] at h1
      exact h1
    have hU : ThetaReflectionData.rowUnit A (frequencyRow P (u', I')) =
        (δ : Fˣ) ^ 6 * ThetaReflectionData.rowUnit A (frequencyRow P (u, I)) := by
      apply Units.ext
      simp only [ThetaReflectionData.rowUnit, Units.val_mk0, Units.val_mul,
        Units.val_pow_eq_pow_val]
      exact hF.symm
    have hkey : ThetaReflectionData.rowUnit A (frequencyRow P (u', I')) =
        ThetaReflectionData.rowUnit A u.val * P.allowed.generator I ^ 6 * (δ : Fˣ) ^ 6 := by
      rw [hU, rowUnit_frequencyRow P (u, I)]
      ac_rfl
    obtain ⟨x0, hx0, huniq⟩ := P.frequencies.factorization (frequencyRow P (u', I'))
    have hx1 : (u, I) = x0 := huniq (u, I) ⟨δ, hkey⟩
    have hx2 : (u', I') = x0 := by
      refine huniq (u', I') ⟨1, ?_⟩
      rw [rowUnit_frequencyRow P (u', I')]
      simp
    exact hx1.trans hx2.symm
  · intro o
    induction o using Quotient.inductionOn with | h h =>
      obtain ⟨x0, hx0, -⟩ := P.frequencies.factorization h
      obtain ⟨γ, hγ⟩ := hx0
      refine ⟨x0, ?_⟩
      refine (Quotient.sound ?_).symm
      refine MulAction.orbitRel_apply.mpr
        ⟨⟨γ ^ 6, ⟨γ, by rw [powMonoidHom_apply]⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have hγF : (h.val : F) =
          (x0.1.val.val : F) * ((P.allowed.generator x0.2 : Fˣ) : F) ^ 6 *
            ((γ : Fˣ) : F) ^ 6 := by
        have := congrArg (fun y : Fˣ => (y : F)) hγ
        simpa [ThetaReflectionData.rowUnit, Units.val_mk0, Units.val_mul,
          Units.val_pow_eq_pow_val] using this
      have hrow : ((frequencyRow P x0).val : F) =
          (x0.1.val.val : F) * ((P.allowed.generator x0.2 : Fˣ) : F) ^ 6 := by
        simp only [frequencyRow, Subalgebra.coe_mul, Subalgebra.coe_pow]
        rw [show ((P.coefficients.generator x0.2 : A.R) : F) =
          (P.allowed.generator x0.2 : F) from (P.sameGenerator x0.2).symm]
      change ((A.unitEquiv (γ ^ 6) : A.R) * (frequencyRow P x0).val : F) = (h.val : F)
      rw [show ((A.unitEquiv (γ ^ 6) : A.R) : F) = ((γ : Fˣ) : F) ^ 6 from by
          rw [map_pow]; rfl,
        hrow, hγF]
      ring

def frequencyEquiv (P : PrincipalData A σ η hS) :
    FrequencyIndex P ≃ ProbeOrbitNormSum.Orbit A :=
  Equiv.ofBijective (frequencyOrbit P) (frequencyOrbit_bijective P)

private theorem orbitNorm_orbitMk_eq_exteriorNorm (A : SArithmeticData F)
    (h : ProbeOrbitNormSum.Nonzero A) :
    ProbeOrbitNormSum.orbitNorm A (ProbeOrbitNormSum.orbitMk A h) =
      (FiniteTransform.exteriorNorm A.R.toSubring h.val : ℝ) := by
  unfold FiniteTransform.exteriorNorm ProbeOrbitNormSum.orbitNorm
  rw [ProbeOrbitNormSum.orbitIdeal_mk]
  change A.exteriorNorm (ProbeOrbitNormSum.principalExterior A h) =
    (Nat.card (A.R ⧸ Ideal.span {h.val}) : ℝ)
  rw [(ProbeOrbitNormSum.principalExterior_generates A h).2, A.exteriorResidue_card]
  rfl

private theorem norm_diagonal_rowUnit_eq_orbitNorm (A : SArithmeticData F)
    (h : ProbeOrbitNormSum.Nonzero A) :
    A.norm (A.diagonal (ThetaReflectionData.rowUnit A h)) =
      ProbeOrbitNormSum.orbitNorm A (ProbeOrbitNormSum.orbitMk A h) :=
  (ProbeOrbitNormSum.orbitNorm_eq_snorm A h (ThetaReflectionData.rowUnit A h) rfl).symm

private theorem norm_diagonal_rowUnit (A : SArithmeticData F)
    (h : ProbeOrbitNormSum.Nonzero A) :
    A.norm (A.diagonal (ThetaReflectionData.rowUnit A h)) =
      (FiniteTransform.exteriorNorm A.R.toSubring h.val : ℝ) :=
  (norm_diagonal_rowUnit_eq_orbitNorm A h).trans (orbitNorm_orbitMk_eq_exteriorNorm A h)

private theorem normPow (A : SArithmeticData F) (x : A.G) (n : ℕ) :
    A.norm (x ^ n) = A.norm x ^ n := by
  induction n with
  | zero => simp [SArithmeticData.norm]
  | succ n ih => rw [pow_succ, ProbeSheet.norm_mul, ih, pow_succ]

theorem frequencyOrbit_norm (P : PrincipalData A σ η hS) (j : FrequencyIndex P) :
    ProbeOrbitNormSum.orbitNorm A (frequencyOrbit P j) =
      (FiniteTransform.exteriorNorm A.R.toSubring j.1.val.val : ℝ) *
        A.exteriorNorm j.2 ^ 6 := by
  have hg : (FiniteTransform.exteriorNorm A.R.toSubring (P.coefficients.generator j.2) : ℝ) =
      A.exteriorNorm j.2 := by
    change (Nat.card (A.R ⧸ Ideal.span {P.coefficients.generator j.2}) : ℝ) = _
    rw [(P.coefficients.generates j.2).2, A.exteriorResidue_card]
    rfl
  have hrow : ThetaReflectionData.rowUnit A (frequencyRow P j) =
      ThetaReflectionData.rowUnit A j.1.val *
        (ThetaReflectionData.rowUnit A
          ⟨P.coefficients.generator j.2, (P.coefficients.generates j.2).1⟩) ^ 6 := by
    apply Units.ext
    simp only [frequencyRow, ThetaReflectionData.rowUnit, Units.val_mk0, Units.val_mul,
      Units.val_pow_eq_pow_val]
    push_cast
    ring
  rw [frequencyOrbit,
    ProbeOrbitNormSum.orbitNorm_eq_snorm A (frequencyRow P j)
      (ThetaReflectionData.rowUnit A (frequencyRow P j)) rfl,
    hrow, map_mul, map_pow, ProbeSheet.norm_mul, normPow,
    norm_diagonal_rowUnit A j.1.val,
    norm_diagonal_rowUnit A ⟨P.coefficients.generator j.2, (P.coefficients.generates j.2).1⟩,
    hg]

def frequencySection (P : PrincipalData A σ η hS) (o : ProbeOrbitNormSum.Orbit A) :
    ProbeOrbitNormSum.Nonzero A := frequencyRow P ((frequencyEquiv P).symm o)

theorem frequencySection_leftInverse (P : PrincipalData A σ η hS) :
    Function.LeftInverse (ProbeOrbitNormSum.orbitMk A) (frequencySection P) := by
  intro o
  change frequencyEquiv P ((frequencyEquiv P).symm o) = o
  simp

def orbitIndexEquiv (P : PrincipalData A σ η hS) :
    MellinSeriesIndex P ≃ ProbePoissonOrbitFormula.Index A where
  toFun i := (i.2.2.2.1, i.2.1, i.2.2.1, frequencyEquiv P (i.1, i.2.2.2.2))
  invFun i := ((frequencyEquiv P).symm i.2.2.2 |>.1,
    i.2.1, i.2.2.1, i.1, (frequencyEquiv P).symm i.2.2.2 |>.2)
  left_inv i := by simp
  right_inv i := by simp

theorem probe_eq_reindexed_sum (P : PrincipalData A σ η hS)
    (N : MellinNormalizationData A σ η hS P)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (hρ : Function.LeftInverse (ProbeOrbitNormSum.orbitMk A) ρ)
    (X Y Z : {x : ℝ // 0 < x}) :
    principalProbe A σ η hS P X Y Z =
      ∑' i : MellinSeriesIndex P, ProbePoissonOrbitFormula.term A σ η hS P ρ
        X.val Y.val Z.val (orbitIndexEquiv P i) := by
  rw [(probe_eq_orbit_sum P N ρ hρ X Y Z).2]
  exact ((orbitIndexEquiv P).tsum_eq _).symm

end
end DedekindZetaZeroFree.NormalizedProbe.TripleMellin
