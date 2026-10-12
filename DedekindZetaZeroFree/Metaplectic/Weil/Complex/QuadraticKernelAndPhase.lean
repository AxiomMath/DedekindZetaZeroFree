module

public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.CompletionTraceOperatorKernel

@[expose] public section

noncomputable section
open Filter NumberField
open scoped Topology

namespace DedekindZetaZeroFree.ComplexWeil

theorem F_M_F_quadratic_kernel (β a : ℂ) (hβ : β ≠ 0) (ha : a ≠ 0)
    (f : SchwartzMap ℂ ℂ) (y : ℂ) :
    F β (M β a (F β (⇑f))) y =
      ((1 / (2 * ‖a‖) : ℝ) : ℂ) * psi β (-y ^ 2 / (4 * a)) *
        F β (M β (-1 / (4 * a)) (⇑f)) (y / (2 * a)) := by
  have h := FT_M_FT_schwartz β a hβ ha f y
  have hL : F β (M β a (F β (⇑f))) y =
      FT β (fun x : ℂ => psi β (a * x ^ 2) * FT β (⇑f) x) y := by
    rw [FT_eq_F]
    congr 1
    funext x
    rw [M, FT_eq_F]
  have hR : F β (M β (-1 / (4 * a)) (⇑f)) (y / (2 * a)) =
      FT β (fun z : ℂ => psi β (-z ^ 2 / (4 * a)) * f z) (y / (2 * a)) := by
    rw [FT_eq_F]
    congr 1
    funext z
    rw [M, show (-1 / (4 * a)) * z ^ 2 = -z ^ 2 / (4 * a) by ring]
  rw [hL, hR]
  exact h

end DedekindZetaZeroFree.ComplexWeil

namespace DedekindZetaZeroFree.SArithmeticData

theorem complexWeilPhase_eq_one
    {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
    (w : InfinitePlace F) (a : w.Completionˣ) : A.complexWeilPhase w a = 1 := by
  simp [complexWeilPhase, complexGamma]

end DedekindZetaZeroFree.SArithmeticData

end
