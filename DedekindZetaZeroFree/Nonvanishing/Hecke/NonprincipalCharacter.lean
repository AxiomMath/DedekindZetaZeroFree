module

public import DedekindZetaZeroFree.Nonvanishing.Hecke.GaloisCharacter
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.RayCharacterGaloisRealization
public import DedekindZetaZeroFree.LFunctions.Hecke.EulerProducts.RayCharacterFiniteCorrection
public import ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension

@[expose] public section

namespace DedekindZetaZeroFree.HeckeCorollary

open scoped NumberField
open AbelianQuotient IsDedekindDomain

theorem nonprincipalRayCharacter_ne_zero
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m)
    (hχ : ¬ χ.IsPrincipal) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      (∀ s, 31 / 32 < s.re → f s ≠ 0) := by
  obtain ⟨R, ρ, hρ, hρprime⟩ := exists_rayCharacter_galoisRealization K m hm χ
  have hρne : ρ ≠ 1 := fun h => hχ (hρ.mp h)
  obtain ⟨m₀, χ₀, f₀, hm₀, _hχ₀, hprime, hf₀, hsum₀, hnz₀⟩ :=
    galoisCharacter_ne_zero K R.extension ρ hρne
  let S := (narrowIdealModulus K m hm).finitePart.support
  have hzero : ∀ P ∈ S, χ P.asIdeal = 0 :=
    fun P hP => rayCharacter_eq_zero_of_mem_modulus_support K m hm χ P hP
  have hagree : ∀ P ∉ S, χ P.asIdeal = χ₀ P.asIdeal := by
    intro P hP
    obtain ⟨Q⟩ := Ideal.nonempty_primesOver (R := 𝓞 K) (S := 𝓞 R.extension) P.asIdeal
    let W : HeightOneSpectrum (𝓞 R.extension) :=
      ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩
    exact (hρprime P hP W Q.2.2).trans (hprime P W Q.2.2).symm
  refine ⟨fun s => f₀ s * finiteEulerCorrection K χ₀ S s,
    hf₀.mul (finiteEulerCorrection_differentiable K χ₀ S), ?_, ?_⟩
  · intro s hs
    have hsum := (weightedIdealSummability K χ χ.map_mul' χ.map_top'
      ((χ.eq_zero_iff' ⊥).mpr (Or.inl rfl))
      (rayCharacter_norm_le_one K m hm χ) s hs).of_norm.hasSum
    rw [rayCharacter_eulerCorrection K m m₀ hm hm₀ χ χ₀ S hzero hagree s hs,
      (hsum₀ s hs).tsum_eq] at hsum
    exact hsum
  · intro s hs
    exact mul_ne_zero (hnz₀ s hs) (finiteEulerCorrection_ne_zero K χ₀
      (rayCharacter_norm_le_one K m₀ hm₀ χ₀) S s (by linarith))

end DedekindZetaZeroFree.HeckeCorollary
