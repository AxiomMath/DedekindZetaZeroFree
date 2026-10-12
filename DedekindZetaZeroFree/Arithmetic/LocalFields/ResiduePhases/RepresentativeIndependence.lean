module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.Definitions

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.CRTRawLocalModel
open LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem congruent_symm (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) {x y : LocalField p}
    (h : Congruent C p n x y) : Congruent C p n y x := by
  obtain ⟨r, hr⟩ := h
  refine ⟨-r, ?_⟩
  change y - x = uniformizer C p ^ n * -(r : LocalField p)
  linear_combination -hr

theorem congruent_trans (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) {x y z : LocalField p}
    (h : Congruent C p n x y) (h' : Congruent C p n y z) :
    Congruent C p n x z := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨q, hq⟩ := h'
  refine ⟨r + q, ?_⟩
  change x - z = uniformizer C p ^ n * ((r : LocalField p) + q)
  linear_combination hr + hq

theorem numeratorCongruence_independent (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (a h : (LocalIntegers p)ˣ)
    {d d' : LocalField p} (hd : Congruent C p k d d') :
    numeratorCongruence C p t k J a h d ↔
      numeratorCongruence C p t k J a h d' := by
  obtain ⟨r, hr⟩ := hd
  let π : LocalIntegers p := ⟨uniformizer C p, CompatiblePrimeRawLocal.sInteger_local_integral_source p (generator C p)⟩
  have hh : Congruent C p k ((a.val : LocalField p) * uniformizer C p ^ t * d)
      ((a.val : LocalField p) * uniformizer C p ^ t * d') := by
    refine ⟨a.val * π ^ t * r, ?_⟩
    change _ = uniformizer C p ^ k * ((a.val : LocalField p) * uniformizer C p ^ t * r)
    linear_combination (a.val : LocalField p) * uniformizer C p ^ t * hr
  exact ⟨fun hc => congruent_trans C p k hc hh,
    fun hc => congruent_trans C p k hc (congruent_symm C p k hh)⟩

theorem rawPhase_representatives_independent
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (t k J : ℕ) (s a h : (LocalIntegers p)ˣ)
    (d d' v v' : LocalIntegers p)
    (hd : Congruent C p k (d : LocalField p) (d' : LocalField p))
    (hv : Congruent C p t (v : LocalField p) (v' : LocalField p))
    (hc : numeratorCongruence C p t k J a h (d : LocalField p)) :
    rawPhase C p t k J s a h (d : LocalField p) (v : LocalField p) =
      rawPhase C p t k J s a h (d' : LocalField p) (v' : LocalField p) := by
  obtain ⟨r, hr⟩ := hd
  obtain ⟨q, hq⟩ := hv
  obtain ⟨b, hb⟩ := hc
  let z : LocalIntegers p := (↑s⁻¹ * ↑a⁻¹) * b * q - ↑s⁻¹ * r * v'
  have hs : (s.val : LocalField p) ≠ 0 := by
    exact (s.isUnit.map (LocalIntegers p).subtype).ne_zero
  have ha : (a.val : LocalField p) ≠ 0 := by
    exact (a.isUnit.map (LocalIntegers p).subtype).ne_zero
  have hz := CRTRawLocalPhaseAlgebra.phase_difference
    (uniformizer C p) (s.val : LocalField p) (a.val : LocalField p)
    (h.val : LocalField p) (d : LocalField p) (d' : LocalField p)
    (v : LocalField p) (v' : LocalField p) (r : LocalField p)
    (q : LocalField p) (b : LocalField p) t k J
    (CRTRawLocalPhaseAlgebra.uniformizer_ne_zero C p) hs ha hr hq hb
  have hsi : ((↑s⁻¹ : LocalIntegers p) : LocalField p) = (s.val : LocalField p)⁻¹ := by
    exact (map_units_inv (LocalIntegers p).subtype s)
  have hai : ((↑a⁻¹ : LocalIntegers p) : LocalField p) = (a.val : LocalField p)⁻¹ := by
    exact map_units_inv (LocalIntegers p).subtype a
  have hz' : negativeTrace p
      (((h.val : LocalField p) * uniformizer C p ^ J -
        (a.val : LocalField p) * uniformizer C p ^ t * d) * v /
        ((s.val : LocalField p) * (a.val : LocalField p) * uniformizer C p ^ (k + t)) -
       ((h.val : LocalField p) * uniformizer C p ^ J -
        (a.val : LocalField p) * uniformizer C p ^ t * d') * v' /
        ((s.val : LocalField p) * (a.val : LocalField p) * uniformizer C p ^ (k + t))) = 1 := by
    rw [hz]
    convert CompatiblePrimeRawLocal.negativeTrace_integer_source C p z using 1
    change negativeTrace p _ = negativeTrace p
      ((LocalIntegers p).subtype (↑s⁻¹ * ↑a⁻¹ * b * q - ↑s⁻¹ * r * v'))
    simp only [map_sub, map_mul, ValuationSubring.coe_subtype, hsi, hai]
  rw [AddChar.map_sub_eq_div, div_eq_one] at hz'
  exact congrArg (fun x : Circle => (x : ℂ)) hz'

end DedekindZetaZeroFree.CRTRawLocalModel

end
