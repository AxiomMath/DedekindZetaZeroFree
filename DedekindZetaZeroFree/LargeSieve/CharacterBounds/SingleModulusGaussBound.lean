module

public import DedekindZetaZeroFree.CharacterSums.Gauss.PrimitiveResidueCharacters
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.FiniteCharacterBessel

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Classical

theorem detector_single_modulus_gauss_sieve
    (B : Type*) [CommRing B] [Fintype B]
    (J : Type*) [Fintype J]
    (χ : J → MulChar B ℂ) (hχ : Function.Injective χ)
    (ψ : AddChar B ℂ)
    (hprimitive : ∀ j : J, IsPrimitiveResidueCharacter (χ j))
    (horthogonal : IsOrthogonalResidueAddChar ψ)
    (T : Type*) [Fintype T] (n : T → B) (c : T → ℂ) :
    ((∑ j : J, ‖∑ t : T, c t * χ j (n t)‖ ^ 2) ≤
      ((Fintype.card Bˣ : ℝ) / (Fintype.card B : ℝ)) *
        ∑ d : Bˣ, ‖∑ t : T, c t * ψ (n t * (d : B))‖ ^ 2) ∧
    (((Fintype.card Bˣ : ℝ) / (Fintype.card B : ℝ)) *
        ∑ d : Bˣ, ‖∑ t : T, c t * ψ (n t * (d : B))‖ ^ 2 ≤
      ∑ d : Bˣ, ‖∑ t : T, c t * ψ (n t * (d : B))‖ ^ 2) := by
  classical
  let A : Bˣ → ℂ := fun d => ∑ t : T, c t * ψ (n t * (d : B))
  let η : J → (Bˣ →* ℂˣ) := fun j => MulChar.equivToUnitHom (χ j)
  have hη : Function.Injective η := MulChar.equivToUnitHom.injective.comp hχ
  have hB : 0 < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  have hexpand (j : J) : (∑ t : T, c t * χ j (n t)) =
      (gaussSum (χ j)⁻¹ ψ)⁻¹ *
        ∑ d : Bˣ, star ((η j d : ℂˣ) : ℂ) * A d := by
    obtain ⟨_, ht, _⟩ := detector_gauss_residue B (χ j) ψ (hprimitive j) horthogonal
    simp_rw [ht]
    simp only [η, MulChar.coe_equivToUnitHom, MulChar.star_apply', A,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hnorm (j : J) : ‖∑ t : T, c t * χ j (n t)‖ ^ 2 =
      (Fintype.card B : ℝ)⁻¹ *
        ‖∑ d : Bˣ, star ((η j d : ℂˣ) : ℂ) * A d‖ ^ 2 := by
    rw [hexpand, norm_mul, mul_pow, norm_inv, inv_pow,
      (detector_gauss_residue B (χ j) ψ (hprimitive j) horthogonal).1]
  have hbes := detector_finite_character_bessel Bˣ J η hη A
  have hcard : (Fintype.card Bˣ : ℝ) ≤ (Fintype.card B : ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective Units.val Units.val_injective
  have hnonneg : 0 ≤ ∑ d : Bˣ, ‖A d‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  constructor
  · simp_rw [hnorm]
    rw [← Finset.mul_sum]
    calc
      _ ≤ (Fintype.card B : ℝ)⁻¹ *
          ((Fintype.card Bˣ : ℝ) * ∑ d : Bˣ, ‖A d‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbes (le_of_lt (inv_pos.mpr hB))
      _ = _ := by dsimp [A]; ring
  · have hratio : (Fintype.card Bˣ : ℝ) / (Fintype.card B : ℝ) ≤ 1 :=
      (div_le_one hB).mpr hcard
    simpa [A] using mul_le_mul_of_nonneg_right hratio hnonneg

end DedekindZetaZeroFree
