module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable def seminorm (j : ℕ) (φ : ComplexProjectiveLine → ℂ) : ℝ :=
  sSup ({0} ∪ {r : ℝ | ∃ q : ℕ, q ≤ j ∧ ∃ z : ℂ,
    z ∈ Metric.closedBall (0 : ℂ) 1 ∧
      (r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ∨
       r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖)})

noncomputable def ratio (g : ComplexGL2) : ℝ :=
  ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g

noncomputable def line (g : ComplexGL2) : ComplexProjectiveLine :=
  if (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 then projectiveInfinity 0
  else projectiveOpen
    ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 / (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)

noncomputable def reconstructedSection (s : ℂ) (φ : ComplexProjectiveLine → ℂ) (g : ComplexGL2) : ℂ :=
  Complex.exp (((4 / 3 : ℂ) + 2 * s) * (Real.log (ratio g) : ℂ)) * φ (line g)

noncomputable def operatorApply {n j : ℕ}
    (c : (q : Fin (j + 1)) → (Fin q.val → Fin n) → (Fin n → ℝ) → ℂ)
    (f : (Fin n → ℝ) → ℂ) (u : Fin n → ℝ) : ℂ :=
  ∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n,
    c q a u * iteratedFDeriv ℝ q.val f u (fun i => Pi.single (a i) (1 : ℝ))

noncomputable def envelope (p : ℝ) (x : ℂ) : ℝ :=
  Real.rpow (1 + ‖x‖ ^ 2) (-p)

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant
