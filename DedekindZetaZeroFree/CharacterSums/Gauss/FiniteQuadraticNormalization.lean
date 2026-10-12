module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable def finiteQuadraticPolarization {G : Type*} [AddCommGroup G] (Q : G → Circle)
    (x y : G) : Circle :=
  Q (x + y) / (Q x * Q y)

theorem weil_finite_quadratic_gauss_modulus
    {G : Type*} [AddCommGroup G] [Fintype G] (Q : G → Circle)
    (hQzero : Q 0 = 1)
    (hBleft : ∀ x x' y : G,
      finiteQuadraticPolarization Q (x + x') y =
        finiteQuadraticPolarization Q x y * finiteQuadraticPolarization Q x' y)
    (hBright : ∀ x y y' : G,
      finiteQuadraticPolarization Q x (y + y') =
        finiteQuadraticPolarization Q x y * finiteQuadraticPolarization Q x y')
    (hBnondegenerate : ∀ x : G, x ≠ 0 →
      ∃ y : G, finiteQuadraticPolarization Q x y ≠ 1) :
    ‖∑ x : G, (Q x : ℂ)‖ ^ 2 = (Fintype.card G : ℝ) := by
  classical
  have hsum (h : G) :
      ∑ y : G, (finiteQuadraticPolarization Q h y : ℂ) =
        if h = 0 then (Fintype.card G : ℂ) else 0 := by
    by_cases hh : h = 0
    · subst h
      simp [finiteQuadraticPolarization, hQzero]
    · obtain ⟨y₀, hy₀⟩ := hBnondegenerate h hh
      have hc : (finiteQuadraticPolarization Q h y₀ : ℂ) ≠ 1 := by
        intro heq
        apply hy₀
        exact Circle.coe_injective heq
      have htranslate :
          (finiteQuadraticPolarization Q h y₀ : ℂ) *
            ∑ y : G, (finiteQuadraticPolarization Q h y : ℂ) =
            ∑ y : G, (finiteQuadraticPolarization Q h y : ℂ) := by
        rw [Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.addLeft y₀) _ _ fun y ↦ by
          exact (congrArg (fun z : Circle ↦ (z : ℂ)) (hBright h y₀ y)).symm
      simpa [hh] using eq_zero_of_mul_eq_self_left hc htranslate
  have hterm (h y : G) : (Q (h + y) : ℂ) * star (Q y : ℂ) =
      (Q h : ℂ) * (finiteQuadraticPolarization Q h y : ℂ) := by
    change (Q (h + y) : ℂ) * (starRingEnd ℂ) (Q y : ℂ) = _
    erw [← Circle.coe_inv_eq_conj]
    have heq : Q (h + y) * (Q y)⁻¹ = Q h * finiteQuadraticPolarization Q h y := by
      unfold finiteQuadraticPolarization
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        Q (h + y) * (Q y)⁻¹ = (Q h * (Q h)⁻¹) * (Q (h + y) * (Q y)⁻¹) := by rw [mul_inv_cancel, one_mul]
        _ = Q h * (Q (h + y) * ((Q y)⁻¹ * (Q h)⁻¹)) := by ac_rfl
    exact congrArg (fun z : Circle ↦ (z : ℂ)) heq
  have hc : ((‖∑ x : G, (Q x : ℂ)‖ ^ 2 : ℝ) : ℂ) = (Fintype.card G : ℂ) := by
    rw [Complex.ofReal_pow]
    erw [← Complex.mul_conj']
    rw [map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      ∑ y : G, ∑ x : G, (Q x : ℂ) * star (Q y : ℂ) =
          ∑ y : G, ∑ h : G, (Q (h + y) : ℂ) * star (Q y : ℂ) := by
        congr 1
        funext y
        exact (Equiv.sum_comp (Equiv.addRight y) _).symm
      _ = ∑ h : G, (Q h : ℂ) * ∑ y : G, (finiteQuadraticPolarization Q h y : ℂ) := by
        simp_rw [hterm]
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ = (Fintype.card G : ℂ) := by simp [hsum, hQzero]
  exact_mod_cast hc

end DedekindZetaZeroFree
