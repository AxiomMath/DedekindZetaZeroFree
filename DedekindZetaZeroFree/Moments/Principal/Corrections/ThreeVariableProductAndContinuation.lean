module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.MeromorphicQuotientGluing
public import DedekindZetaZeroFree.Moments.Principal.Corrections.FrequencySubpowerBound

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.ThreeVariableProduct
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors InitialSeparatedEuler
open FrequencyCharacterMasks MaskedHeckeMeromorphic MeromorphicSeparationGluing

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem three_variable_product (C : A.GeneralArithmeticContext σ η hS) :
    (∀ U : Frequency C,
      (∀ (K : Set Coordinates), IsCompact K → K ⊆ Omega →
        HasProdUniformlyOn
          (fun (p : ExteriorPrime A) (x : Coordinates) =>
            localFactor C U p x.1 x.2.1 x.2.2)
          (fun x : Coordinates =>
            ∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2) K) ∧
      HasProdLocallyUniformlyOn
        (fun (p : ExteriorPrime A) (x : Coordinates) =>
          localFactor C U p x.1 x.2.1 x.2.2)
        (fun x : Coordinates =>
          ∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2) Omega ∧
      Continuous (fun x : Omega =>
        H_u C U x.val.1 x.val.2.1 x.val.2.2
          (multipliable_localFactor C U x.val x.property)) ∧
      SeparatelyHolomorphicOn
        (fun x : Coordinates =>
          ∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2) Omega) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ Cε : ℝ, 0 < Cε ∧
        ∀ (U : Frequency C) (x : Coordinates) (hx : x ∈ Omega),
          ‖H_u C U x.1 x.2.1 x.2.2 (multipliable_localFactor C U x hx)‖ ≤
            Cε * (A.exteriorNorm U.ideal) ^ ε) ∧
    (∀ (U : Frequency C) (D : ComparisonPoissonCoefficientData F A),
      WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction →
      ∀ (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re),
        minusL U ξ ≠ 0 ∧
        comparisonEulerPoissonSeries F A D U.u ξ w z =
          zetaS A (6 * z) * plusL U w *
            H_u C U ξ w z (correction_multipliable_initial U ξ w z hξ hw hz) /
              minusL U ξ) ∧
    (
      ∀ (U : Frequency C) (D : ComparisonPoissonCoefficientData F A),
        WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS C.correction →
        ∃ (P : PrimitiveInducers U) (R : ∀ i : Row, RowContinuation U P i),
          GlobalQuotientCertificate (numerator U P R) (denominator U P R)
            (fun x => comparisonEulerPoissonSeries F A D U.u x.1 x.2.1 x.2.2) ∧
          ∀ N' D' : Coordinates → ℂ,
            GlobalQuotientCertificate N' D'
              (fun x => comparisonEulerPoissonSeries F A D U.u x.1 x.2.1 x.2.2) →
            CrossMultipliedOn (numerator U P R) (denominator U P R) N' D' Omega) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U
    exact ⟨fun K hK hKO => hasProdUniformlyOn_localFactor C U K hK hKO,
      hasProdLocallyUniformlyOn_localFactor C U,
      continuous_H_u C U,
      ⟨differentiableOn_H_u_xi C U, differentiableOn_H_u_w C U,
        differentiableOn_H_u_z C U⟩⟩
  · intro ε hε
    exact H_u_uniform_subpower_bound C ε hε
  · intro U D hD ξ w z hξ hw hz
    exact ⟨(initial_separated_euler U D hD ξ w z hξ hw hz).1,
      initial_separated_euler_quotient U D hD ξ w z hξ hw hz⟩
  · intro U D hD
    obtain ⟨P, R, hcert⟩ := meromorphic_separation_gluing U D hD
    exact ⟨P, R, hcert, fun N' D' h' => cross_multiplication_unique _ _ _ _ _ hcert h'⟩

end DedekindZetaZeroFree.ThreeVariableProduct

end
