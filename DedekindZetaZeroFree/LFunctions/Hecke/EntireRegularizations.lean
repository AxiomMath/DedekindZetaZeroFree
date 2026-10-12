module

public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalRayContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalRayContinuation

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField

def heckeConductorScale (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) : ℝ :=
  (|NumberField.discr F| : ℤ) * (Ideal.absNorm 𝔪 : ℝ)

theorem one_le_heckeConductorScale (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) :
    1 ≤ heckeConductorScale F 𝔪 := by
  unfold heckeConductorScale
  have hd : (1 : ℝ) ≤ ((|NumberField.discr F| : ℤ) : ℝ) := by
    have h : (0 : ℤ) < |NumberField.discr F| := by
      rw [abs_pos]
      exact NumberField.discr_ne_zero F
    exact_mod_cast h
  have hm' : (1 : ℝ) ≤ (Ideal.absNorm 𝔪 : ℝ) := by
    have h : 1 ≤ Ideal.absNorm 𝔪 := by
      rw [Nat.one_le_iff_ne_zero]
      exact fun h0 => hm (Ideal.absNorm_eq_zero_iff.mp h0)
    exact_mod_cast h
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ ((|NumberField.discr F| : ℤ) : ℝ) * (Ideal.absNorm 𝔪 : ℝ) := by gcongr

theorem one_le_nrComplexPlaces_of_totallyComplex
    (F : Type*) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F) :
    1 ≤ NumberField.InfinitePlace.nrComplexPlaces F := by
  haveI := hF
  have hrank := NumberField.IsTotallyComplex.finrank F
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  omega

def heckeReciprocalCompletionFactor (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
    ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F

section Helpers

private lemma heckeConductorScale_cast_eq (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) :
    (heckeConductorScale F 𝔪 : ℂ) =
      ((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm 𝔪 : ℂ) := by
  unfold heckeConductorScale
  rw [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_natCast]

private lemma heckeConductorScale_ne_zero (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) : (heckeConductorScale F 𝔪 : ℂ) ≠ 0 := by
  have h0 : 0 < heckeConductorScale F 𝔪 :=
    lt_of_lt_of_le zero_lt_one (one_le_heckeConductorScale F 𝔪 hm)
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt h0)

private lemma Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  exact Complex.cpow_ne_zero_iff.mpr
    (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))

private lemma heckeCompletionFactor_eq_scale (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (s : ℂ) :
    heckeCompletionFactor F 𝔪 s =
      (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) *
        Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F := by
  rw [heckeCompletionFactor, heckeConductorScale_cast_eq F 𝔪]

private lemma reciprocalCompletion_mul_completion (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (s : ℂ) (hs : 0 < s.re) :
    heckeReciprocalCompletionFactor F 𝔪 s * heckeCompletionFactor F 𝔪 s = 1 := by
  have hQ : (heckeConductorScale F 𝔪 : ℂ) ≠ 0 := heckeConductorScale_ne_zero F 𝔪 hm
  have hG : Complex.Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_re_pos hs
  rw [heckeReciprocalCompletionFactor, heckeCompletionFactor_eq_scale F 𝔪 s]
  have hpow : (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
      (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) = 1 := by
    rw [← Complex.cpow_add (-s / 2) (s / 2) hQ,
      show -s / 2 + s / 2 = 0 by ring_nf, Complex.cpow_zero]
  have hgam : ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F *
      Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hG, one_pow]
  calc (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
        ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        ((heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F)
      = ((heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
          (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2)) *
        (((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F) := by ring
    _ = 1 := by rw [hpow, hgam, mul_one]

private lemma inv_pow_mul_pow_sub_one (r : ℕ) (hr : 1 ≤ r) {g : ℂ} (hg : g ≠ 0) :
    (g⁻¹) ^ (r - 1) * g ^ r = g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [Nat.succ_eq_add_one, add_tsub_cancel_right]
  rw [pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hg, one_pow, one_mul]

private lemma gamma_shift_inv_mul {s : ℂ} (hs : 0 < s.re) :
    s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ * Complex.Gammaℂ s = 1 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hG : Complex.Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_re_pos hs
  have hc : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  have hrec : Complex.Gammaℂ (s + 1) = Complex.Gammaℂ s * s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ := by
    rw [Complex.Gammaℂ_add_one hs0, div_eq_mul_inv, div_eq_mul_inv, Complex.ofReal_mul, mul_inv]
    norm_num
    ring
  rw [hrec, mul_inv, mul_inv, inv_inv]
  field_simp

private lemma principal_prefactor_mul (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (s : ℂ) (hs : 0 < s.re) :
    (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
      (Complex.Gammaℂ (s + 1))⁻¹ *
      ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
      (s * heckeCompletionFactor F 𝔪 s) = 1 := by
  rw [heckeCompletionFactor_eq_scale F 𝔪 s]
  have hQ : (heckeConductorScale F 𝔪 : ℂ) ≠ 0 := heckeConductorScale_ne_zero F 𝔪 hm
  have hG : Complex.Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_re_pos hs
  have hr : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces F :=
    one_le_nrComplexPlaces_of_totallyComplex F hF
  have hpow : (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
      (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) = 1 := by
    rw [← Complex.cpow_add (-s / 2) (s / 2) hQ,
      show -s / 2 + s / 2 = 0 by ring_nf, Complex.cpow_zero]
  have hgam := inv_pow_mul_pow_sub_one (NumberField.InfinitePlace.nrComplexPlaces F) hr hG
  have hshift : s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ *
      Complex.Gammaℂ s = 1 := gamma_shift_inv_mul hs
  have hshift' : Complex.Gammaℂ s *
      ((((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ * s) = 1 := by
    calc Complex.Gammaℂ s * ((((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ * s)
        = s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ *
            Complex.Gammaℂ s := by ac_rfl
      _ = 1 := hshift
  calc (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
        (Complex.Gammaℂ (s + 1))⁻¹ *
        ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
        (s * ((heckeConductorScale F 𝔪 : ℂ) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F))
      = ((heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
          (heckeConductorScale F 𝔪 : ℂ) ^ (s / 2)) *
        (((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F) *
        ((((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ * s) := by ac_rfl
    _ = 1 := by rw [hpow, hgam, one_mul, hshift']

end Helpers

theorem heckeReciprocalCompletionFactor_differentiable
    (F : Type*) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) :
    Differentiable ℂ (heckeReciprocalCompletionFactor F 𝔪) := by
  have hQ : (heckeConductorScale F 𝔪 : ℂ) ≠ 0 := heckeConductorScale_ne_zero F 𝔪 hm
  unfold heckeReciprocalCompletionFactor
  refine Differentiable.mul ?_ ?_
  · exact ((differentiable_id (𝕜 := ℂ)).neg.div_const (2 : ℂ)).const_cpow (Or.inl hQ)
  · exact Complex.differentiable_Gammaℂ_inv.pow _

def nonprincipalHeckeEntireContinuation
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F))
    (η : RayClassCharacter F 𝔪) (D : NonprincipalRayHeckeData F 𝔪 η)
    (s : ℂ) : ℂ :=
  heckeReciprocalCompletionFactor F 𝔪 s * D.Λ s

theorem nonprincipalHeckeEntireContinuation_differentiable
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (D : NonprincipalRayHeckeData F 𝔪 η) :
    Differentiable ℂ (nonprincipalHeckeEntireContinuation F 𝔪 η D) := by
  refine (heckeReciprocalCompletionFactor_differentiable F 𝔪 hm).mul D.Λ_entire

theorem nonprincipalHeckeEntireContinuation_eq
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (D : NonprincipalRayHeckeData F 𝔪 η) (s : ℂ) (hs : 0 < s.re) :
    nonprincipalHeckeEntireContinuation F 𝔪 η D s = D.L s := by
  rw [nonprincipalHeckeEntireContinuation, D.completed s hs, ← mul_assoc,
    reciprocalCompletion_mul_completion F 𝔪 hm s hs, one_mul]

def principalHeckeEntireRegularization
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F))
    (η : RayClassCharacter F 𝔪) (D : PrincipalRayHeckeData F 𝔪 η)
    (s : ℂ) : ℂ :=
  (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
    (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ *
    ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) * D.E s

theorem principalHeckeEntireRegularization_differentiable
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (D : PrincipalRayHeckeData F 𝔪 η) :
    Differentiable ℂ (principalHeckeEntireRegularization F 𝔪 η D) := by
  have hQ : (heckeConductorScale F 𝔪 : ℂ) ≠ 0 := heckeConductorScale_ne_zero F 𝔪 hm
  have hA : Differentiable ℂ
      (fun s : ℂ => (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2)) :=
    ((differentiable_id (𝕜 := ℂ)).neg.div_const (2 : ℂ)).const_cpow (Or.inl hQ)
  have hC : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℂ (s + 1))⁻¹) :=
    Complex.differentiable_Gammaℂ_inv.comp ((differentiable_id (𝕜 := ℂ)).add_const 1)
  have hD : Differentiable ℂ
      (fun s : ℂ => ((Complex.Gammaℂ s)⁻¹) ^
        (NumberField.InfinitePlace.nrComplexPlaces F - 1)) :=
    Complex.differentiable_Gammaℂ_inv.pow _
  have hpre : Differentiable ℂ (fun s : ℂ =>
      (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
        (Complex.Gammaℂ (s + 1))⁻¹ *
        ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1)) :=
    ((hA.mul (differentiable_const _)).mul hC).mul hD
  unfold principalHeckeEntireRegularization
  exact hpre.mul D.E_entire

theorem principalHeckeEntireRegularization_eq
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (D : PrincipalRayHeckeData F 𝔪 η) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    principalHeckeEntireRegularization F 𝔪 η D s = (s - 1) * D.L s := by
  rw [principalHeckeEntireRegularization, D.E_eq s hs, D.regularized s hs hs1]
  have hpre := principal_prefactor_mul F hF 𝔪 hm s hs
  calc (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
        (Complex.Gammaℂ (s + 1))⁻¹ *
        ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
        (s * heckeCompletionFactor F 𝔪 s * ((s - 1) * D.L s))
      = ((heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
          (Complex.Gammaℂ (s + 1))⁻¹ *
          ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
          (s * heckeCompletionFactor F 𝔪 s)) * ((s - 1) * D.L s) := by ac_rfl
    _ = (s - 1) * D.L s := by rw [hpre, one_mul]

theorem principalHeckeEntireRegularization_eq_bridge
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (D : PrincipalRayHeckeData F 𝔪 η) (s : ℂ) (hs : 0 < s.re) :
    principalHeckeEntireRegularization F 𝔪 η D s = D.R s := by
  rw [principalHeckeEntireRegularization, D.E_eq s hs]
  have hpre := principal_prefactor_mul F hF 𝔪 hm s hs
  calc (heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
        (Complex.Gammaℂ (s + 1))⁻¹ *
        ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
        (s * heckeCompletionFactor F 𝔪 s * D.R s)
      = ((heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
          (Complex.Gammaℂ (s + 1))⁻¹ *
          ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
          (s * heckeCompletionFactor F 𝔪 s)) * D.R s := by ac_rfl
    _ = D.R s := by rw [hpre, one_mul]

end
end DedekindZetaZeroFree
