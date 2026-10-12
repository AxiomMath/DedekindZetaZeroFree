module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.SU2HaarCharacterAverages

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartDerivativeBounds

open KPCplxCharacterHaar

private theorem symmetricPowerTrace_eq_symPower_character (d : ℕ) (g : ComplexSU2) :
    KPCompactHarmonic.symmetricPowerTrace d
      ⟨g.val, (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1⟩ =
    (TauCeti.SU2.symPower d).character g := by
  have hd : Matrix.det g.val = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  induction d using Nat.twoStepInduction with
  | zero => simp [KPCompactHarmonic.symmetricPowerTrace, TauCeti.SU2.character_symPower_zero]
  | one => simp [KPCompactHarmonic.symmetricPowerTrace, TauCeti.SU2.character_symPower_one_eq_trace]
  | more d h0 h1 =>
    simp only [KPCompactHarmonic.symmetricPowerTrace, h0, h1, hd, one_mul]
    have h := TauCeti.SU2.trace_mul_character_symPower d g
    linear_combination h

private theorem su2HarmonicCharacter_eq_symPower_character (ℓ : ℕ) (g : ComplexSU2) :
    su2HarmonicCharacter ℓ g = (TauCeti.SU2.symPower (2 * ℓ)).character g := by
  have hd : Matrix.det g.val = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  simp only [su2HarmonicCharacter, KPCompactHarmonic.rankOneCharacter, hd, one_pow,
    div_one, symmetricPowerTrace_eq_symPower_character]

theorem su2_character_continuous_norm_bound (ℓ : ℕ) :
    Continuous (su2HarmonicCharacter ℓ) ∧
      ∀ k : ComplexSU2, ‖su2HarmonicCharacter ℓ k‖ ≤ (2 * ℓ + 1 : ℕ) := by
  have hfun : su2HarmonicCharacter ℓ =
      fun k => (TauCeti.SU2.symPower (2 * ℓ)).character k :=
    funext fun k => su2HarmonicCharacter_eq_symPower_character ℓ k
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact TauCeti.SU2.continuous_character_symPower (2 * ℓ)
  · intro k
    rw [su2HarmonicCharacter_eq_symPower_character ℓ k]

    obtain ⟨z, hz⟩ := TauCeti.SU2.exists_isConj_torusHom k
    have hconj : (TauCeti.SU2.symPower (2 * ℓ)).character k =
        (TauCeti.SU2.symPower (2 * ℓ)).character (TauCeti.SU2.torusHom z) := by
      obtain ⟨u, hu⟩ := isConj_iff.mp hz
      rw [← hu, Representation.char_conj]
    rw [hconj, TauCeti.SU2.character_symPower_torusHom]

    calc ‖∑ i ∈ Finset.range (2 * ℓ + 1),
            (z : ℂ) ^ i * ((z : ℂ))⁻¹ ^ (2 * ℓ - i)‖
        ≤ ∑ i ∈ Finset.range (2 * ℓ + 1),
            ‖(z : ℂ) ^ i * ((z : ℂ))⁻¹ ^ (2 * ℓ - i)‖ := norm_sum_le _ _
      _ = ∑ _i ∈ Finset.range (2 * ℓ + 1), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, norm_pow, norm_pow, norm_inv, Circle.norm_coe]
          simp
      _ = (2 * ℓ + 1 : ℕ) := by simp

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartDerivativeBounds
