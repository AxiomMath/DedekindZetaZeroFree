module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Classical ComplexConjugate
open RCLike

theorem detector_finite_character_bessel
    (G : Type*) [CommGroup G] [Fintype G]
    (J : Type*) [Fintype J]
    (χ : J → (G →* ℂˣ)) (hχ : Function.Injective χ)
    (A : G → ℂ) :
    (∑ j : J, ‖∑ g : G, star ((χ j g : ℂˣ) : ℂ) * A g‖ ^ 2) ≤
      (Fintype.card G : ℝ) * ∑ g : G, ‖A g‖ ^ 2 := by
  classical
  let ψ : J → AddChar (Additive G) ℂ := fun j =>
    { toFun := fun g => (χ j g.toMul : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intros; simp }
  have hψ : Function.Injective ψ := by
    intro i j h
    apply hχ
    ext g
    exact congrArg (fun f : AddChar (Additive G) ℂ => f (Additive.ofMul g)) h
  have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have ho (i j : J) :
      (∑ g : G, star (χ i g : ℂ) * (χ j g : ℂ)) =
        (Fintype.card G : ℂ) * if i = j then 1 else 0 := by
    have h := AddChar.wInner_cWeight_eq_boole (ψ i) (ψ j)
    simp only [wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card,
      RCLike.inner_apply, starRingEnd_apply, Fintype.card_additive] at h
    simp only [hψ.eq_iff] at h
    have hnC : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    rw [div_eq_iff hnC] at h
    have hs := Fintype.sum_equiv Additive.ofMul
      (fun g : G => star (χ i g : ℂ) * (χ j g : ℂ))
      (fun g : Additive G => (ψ j g) * star (ψ i g)) (by intro g; change star (χ i g : ℂ) * (χ j g : ℂ) = (χ j g : ℂ) * star (χ i g : ℂ); ring)
    rw [← hs] at h
    simpa only [mul_comm] using h
  let n : ℝ := Fintype.card G
  let c : ℝ := (Real.sqrt n)⁻¹
  have hn' : 0 < n := hn
  have hc : 0 ≤ c := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hc2 : c ^ 2 * n = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hn'.le, inv_mul_cancel₀ hn'.ne']
  let v : J → EuclideanSpace ℂ G := fun j =>
    WithLp.toLp 2 (fun g => (c : ℂ) * (χ j g : ℂ))
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [v, PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply,
      map_mul, Complex.star_def, Complex.conj_ofReal]
    have hh : (∑ g : G, ((c : ℂ) * (χ j g : ℂ)) * ((c : ℂ) * conj (χ i g : ℂ))) =
        (c : ℂ)^2 * ∑ g : G, star (χ i g : ℂ) * (χ j g : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [Complex.star_def]
      ring
    rw [hh, ho]
    have hcC : (c : ℂ)^2 * (Fintype.card G : ℂ) = 1 := by
      exact_mod_cast hc2
    rw [← mul_assoc, hcC, one_mul]
  have hb := hv.sum_inner_products_le (WithLp.toLp 2 A)
    (s := Finset.univ)
  have hvA (j : J) : inner ℂ (v j) (WithLp.toLp 2 A) =
      (c : ℂ) * ∑ g : G, star (χ j g : ℂ) * A g := by
    simp only [v, PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply,
      map_mul, Complex.star_def, Complex.conj_ofReal]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  simp only [hvA, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc,
    mul_pow, ← Finset.mul_sum, EuclideanSpace.norm_sq_eq, WithLp.ofLp_toLp] at hb
  have hb' := mul_le_mul_of_nonneg_left hb hn'.le
  rw [← mul_assoc, mul_comm n, hc2, one_mul] at hb'
  exact hb'

end DedekindZetaZeroFree
