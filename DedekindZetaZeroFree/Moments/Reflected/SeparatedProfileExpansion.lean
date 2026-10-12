module

public import DedekindZetaZeroFree.Theta.Whittaker.QuadraticPhaseSeparation
public import DedekindZetaZeroFree.Theta.Profiles.LogConvolutionRegularity

@[expose] public section

namespace DedekindZetaZeroFree.RMSeparatedExpansion
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch ThetaPhaseSeparation

variable {F : Type} [Field F] [NumberField F]

def activeSupport (A : SArithmeticData F) (T : Frozen A) :
    ExteriorSquarefreeIdeal A.cS :=
  ⟨T.f, T.f_squarefree⟩

def rowClass (A : SArithmeticData F) (G : AllowedRecipe A)
    (d : A.Exterior) : G.B :=
  ⟨ThetaReflectionData.rationalClass A (G.generator d), G.allowed d⟩

def termClass (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (T : Frozen A) (d c : A.Exterior) : A.V :=
  profileIndex A G U T (rowClass A G d) (rowClass A G c)

def summand (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ) (T : Frozen A)
    (d : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS) (Z : ℝ) : ℂ :=
  separatedCoefficient A G U σ ψ L T d c.val *
    H (termClass A G U T d c.val) (profileArgument A T d c.val Z)

abbrev Index (A : SArithmeticData F) (h : A.Exterior) :=
  {T : Frozen A // T.h = h} × ExteriorSquarefreeIdeal A.cS

def expansion (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ) (h d : A.Exterior) (Z : ℝ) : ℂ :=
  ∑' i : Index A h, summand A G U σ ψ L H i.1.val d i.2 Z

theorem omegaMajorant_eq_betaIdeal (A : SArithmeticData F) (T : Frozen A) :
    omegaMajorant A T = betaIdeal (activeSupport A T) T.a.val := by
  rw [betaIdeal, if_pos ⟨T.a.property.1, T.a.property.2, T.a_supported⟩]
  unfold omegaMajorant support activeSupport
  refine Finset.prod_preimage IsDedekindDomain.HeightOneSpectrum.asIdeal
    (idealPrimeSupport T.f.val) _
    (fun p => betaLocal (idealNorm p) (idealPrimeExponent p T.a.val)) ?_
  intro p hp hprange
  exfalso
  apply hprange
  have hprime : Prime p := UniqueFactorizationMonoid.prime_of_normalized_factor p
    (by simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp)
  exact ⟨IsDedekindDomain.HeightOneSpectrum.ofPrime hprime, rfl⟩

theorem factors_norm_le_betaIdeal (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x : Fˣ, ‖L x‖ = 1)
    (T : Frozen A) (d c : A.Exterior) :
    ‖omega A G U σ ψ L T‖ ≤ betaIdeal (activeSupport A T) T.a.val ∧
    ‖rho A G U σ ψ L T d‖ ≤ 1 ∧ ‖lambda A G U σ ψ L T c‖ ≤ 1 := by
  simpa only [omegaMajorant_eq_betaIdeal] using
    factors_norm_le A G U σ ψ hψ L hL T d c

theorem separatedCoefficient_support (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (T : Frozen A) (d c : A.Exterior) :
    separatedCoefficient A G U σ ψ L T d c =
      if d.val ⊔ (T.h.val * T.n.val) = ⊤ ∧ c.val ⊔ T.f.val = ⊤ ∧
          d.val ⊔ c.val = ⊤ then
        omega A G U σ ψ L T * rho A G U σ ψ L T d *
          lambda A G U σ ψ L T c * idealSymbol A σ d (G.generator c) ^ 3 /
            ((Real.sqrt (A.exteriorNorm c) : ℂ) * (A.exteriorNorm T.n : ℂ))
      else 0 := by
  simp only [separatedCoefficient, rowMask, columnMask, quadraticPairing]
  split_ifs <;> simp_all

theorem coordinate_summand_exact_squarefree (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x : Fˣ, ‖L x‖ = 1)
    (hrec : SquarefreeGeneratorReciprocity A G σ) (H : A.V → ℝ → ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (b : Branch A G m D) (v : Coordinates A G m D b) (Z : ℝ) :
    exactCoefficient A G U σ ψ m D b v *
        (L (coordinateRepresentative A G U m D b v))⁻¹ *
        H (ThetaReflectionData.frequencyClass A (coordinateFrequency A G U m D b v))
          (Z * ThetaReflectionData.frequencyNorm A (coordinateFrequency A G U m D b v)) =
      summand A G U σ ψ L H (freeze A G m D b v) D.d ⟨v.c, v.c_squarefree⟩ Z := by
  rw [exact_coefficient_separated_squarefree A G U σ ψ hψ L hL hrec m D b v]
  obtain ⟨hc, hn⟩ := coordinate_class_norm A G U m D b v
    (rowClass A G D.d) (rowClass A G v.c) rfl rfl Z
  simp only [summand, termClass, hc, hn]

def FiniteProfiles (A : SArithmeticData F) (H : A.V → ℝ → ℂ) : Prop :=
  ∃ (I : Finset A.V) (P : I → ℝ → ℂ),
    (∀ v, ∃ i : I, H v = P i) ∧
    (∀ i, ContDiff ℝ 2 (logProfile (P i))) ∧
    ∀ (B : ℝ), 0 < B → ∃ K : ℝ, 0 < K ∧
      ∀ (i : I) (j : ℕ), j ≤ 2 → ∀ x : ℝ, 0 < x →
        ‖iteratedDeriv j (logProfile (P i)) (Real.log x)‖ ≤
          K * min (Real.rpow x (1 / 8)) (Real.rpow x (-B))

def FiniteProfileFamily (A : SArithmeticData F)
    (H : A.UnitQuotient → A.V → ℝ → ℂ) : Prop :=
  ∃ (I : Finset (A.UnitQuotient × A.V)) (P : I → ℝ → ℂ),
    (∀ u v, ∃ i : I, H u v = P i) ∧
    (∀ i, ContDiff ℝ 2 (logProfile (P i))) ∧
    ∀ (B : ℝ), 0 < B → ∃ K : ℝ, 0 < K ∧
      ∀ (i : I) (j : ℕ), j ≤ 2 → ∀ x : ℝ, 0 < x →
        ‖iteratedDeriv j (logProfile (P i)) (Real.log x)‖ ≤
          K * min (Real.rpow x (1 / 8)) (Real.rpow x (-B))

end
end DedekindZetaZeroFree.RMSeparatedExpansion
