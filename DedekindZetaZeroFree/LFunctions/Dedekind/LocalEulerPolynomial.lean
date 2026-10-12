module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.FrobeniusOrderModuloInertia
public import DedekindZetaZeroFree.LFunctions.Hecke.InertiaCharacterEulerPolynomial

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField BigOperators

local instance (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsAbelianGalois K L] : CommGroup (L ≃ₐ[K] L) :=
  { (inferInstance : Group (L ≃ₐ[K] L)) with
    mul_comm := fun σ τ => mul_comm' σ τ }

theorem localEulerPolynomial
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (W : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hw : W.asIdeal.LiesOver p.asIdeal) (x : ℂ) :
    (∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
      (1 - x ^ Q.inertiaDeg (𝓞 K))) =
      ∏ ρ : ComplexDual (L ≃ₐ[K] L), (1 - primeArtinValue ρ W * x) := by
  classical
  letI : W.asIdeal.LiesOver p.asIdeal := hw
  have hf := frobeniusQuotientOrder K L p W hw
  have hdet := inertiaCharacterDeterminant
    (Ideal.inertia (L ≃ₐ[K] L) W.asIdeal)
    (ClassFieldTheory.arithmeticFrobeniusAt (K := K) W) x
  dsimp only at hdet
  rw [hf.1, hf.2] at hdet
  have hpos : 0 < W.asIdeal.inertiaDeg (𝓞 K) :=
    Ideal.inertiaDeg_pos W.asIdeal (𝓞 K)
  rw [Nat.mul_div_cancel _ hpos] at hdet
  rw [show (∏ ρ : ComplexDual (L ≃ₐ[K] L), (1 - primeArtinValue ρ W * x)) =
      (1 - x ^ W.asIdeal.inertiaDeg (𝓞 K)) ^
        (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L)).card from hdet]
  calc
    _ = ∏ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L),
        (1 - x ^ W.asIdeal.inertiaDeg (𝓞 K)) := by
      apply Finset.prod_congr rfl
      intro Q hQ
      have hQ' := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 L)).mp hQ
      letI : Q.IsPrime := hQ'.1
      letI : Q.LiesOver p.asIdeal := hQ'.2
      rw [Ideal.inertiaDeg_eq_of_isGaloisGroup p.asIdeal Q W.asIdeal (L ≃ₐ[K] L)]
    _ = _ := by rw [Finset.prod_const]

end DedekindZetaZeroFree.AbelianQuotient
