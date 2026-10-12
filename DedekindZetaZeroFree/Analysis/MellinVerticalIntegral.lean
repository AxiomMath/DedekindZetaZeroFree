module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Reference only; no source code copied.
-/

noncomputable section
open MeasureTheory
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def verticalIntegral (c : ℝ) (f : ℂ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, f ((c : ℂ) + t * Complex.I)

theorem verticalIntegral_add (c : ℝ) (f g : ℂ → ℂ)
    (hf : Complex.VerticalIntegrable f c) (hg : Complex.VerticalIntegrable g c) :
    verticalIntegral c (fun s => f s + g s) =
      verticalIntegral c f + verticalIntegral c g := by
  unfold verticalIntegral
  rw [integral_add hf hg, mul_add]

theorem verticalIntegral_const_mul (c : ℝ) (z : ℂ) (f : ℂ → ℂ)
    (hf : Complex.VerticalIntegrable f c) :
    verticalIntegral c (fun s => z * f s) = z * verticalIntegral c f := by
  unfold verticalIntegral
  rw [integral_const_mul]
  ring

theorem verticalIntegral_one_sub (c : ℝ) (f : ℂ → ℂ) :
    verticalIntegral c (fun s => f (1 - s)) = verticalIntegral (1 - c) f := by
  unfold verticalIntegral
  congr 1
  have harg (t : ℝ) : (1 : ℂ) - ((c : ℂ) + t * Complex.I) =
      ((1 - c : ℝ) : ℂ) + (-t : ℝ) * Complex.I := by
    push_cast
    ring
  simp_rw [harg]
  exact integral_neg_eq_self (fun t : ℝ => f (((1 - c : ℝ) : ℂ) + t * Complex.I)) volume

theorem mellinInv_eq_verticalIntegral (c : ℝ) (f : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinInv c f x = verticalIntegral c (fun s => (x : ℂ) ^ (-s) * f s) := by
  simp [mellinInv, verticalIntegral, smul_eq_mul, Complex.ofReal_div,
    Complex.ofReal_mul]

end DedekindZetaZeroFree.LargeSieve.Vendor

end
