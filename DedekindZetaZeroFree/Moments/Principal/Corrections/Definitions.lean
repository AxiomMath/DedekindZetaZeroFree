module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.GoodPrimeSeries
public import DedekindZetaZeroFree.Analysis.ComplexCoordinateBoxes
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.ValuationUnitParts

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

open LocalFiniteSums

abbrev Coordinates := ℂ × ℂ × ℂ

def omegaFirst : Set Coordinates :=
  {x | (499 / 500 : ℝ) - 1 / 100000 < x.1.re ∧
    (3 / 1000 : ℝ) - 1 / 100000 < x.2.1.re ∧
    (2 / 5 : ℝ) - 1 / 100000 < x.2.2.re}

def omegaSecond : Set Coordinates :=
  {x | (499 / 500 : ℝ) - 1 / 100000 < x.1.re ∧
    (19 / 20 : ℝ) - 1 / 100000 < x.2.1.re ∧
    (4 / 25 : ℝ) - 1 / 100000 < x.2.2.re}

def Omega : Set Coordinates := omegaFirst ∪ omegaSecond

theorem isOpen_Omega : IsOpen Omega := by
  exact (Contour.isOpen_box _ _ _).union (Contour.isOpen_box _ _ _)

def principalRegion : Set ℂ := {s | (2 / 3 : ℝ) < s.re}

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

structure Frequency (C : A.GeneralArithmeticContext σ η hS) where
  u : A.R
  ideal : A.Exterior
  generates : A.Generates ideal u
  allowed : A.IsAllowed C.correction.B
    (Units.mk0 (u : F) (by exact_mod_cast generates.1))
  sixthFree : ∀ p : ExteriorPrime A, idealPrimeExponent p.val.asIdeal ideal.val < 6

namespace Frequency

def j {C : A.GeneralArithmeticContext σ η hS} (U : Frequency C)
    (p : ExteriorPrime A) : Fin 6 :=
  ⟨idealPrimeExponent p.val.asIdeal U.ideal.val, U.sixthFree p⟩

theorem exists_unitPart {C : A.GeneralArithmeticContext σ η hS}
    (U : Frequency C) (p : ExteriorPrime A) :
    ∃ v : A.R, U.u = generator C p ^ (U.j p).val * v ∧
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) v) := by
  exact ValuationGenerator.exists_unitPart C U.ideal U.u U.generates p

def unitPart {C : A.GeneralArithmeticContext σ η hS} (U : Frequency C)
    (p : ExteriorPrime A) : A.R := Classical.choose (U.exists_unitPart p)

theorem unitPart_spec {C : A.GeneralArithmeticContext σ η hS}
    (U : Frequency C) (p : ExteriorPrime A) :
    U.u = generator C p ^ (U.j p).val * U.unitPart p ∧
      IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (U.unitPart p)) :=
  Classical.choose_spec (U.exists_unitPart p)

theorem unitPart_chi_norm {C : A.GeneralArithmeticContext σ η hS}
    (U : Frequency C) (p : ExteriorPrime A) :
    ‖chi (σ := σ) p
      (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (U.unitPart p))‖ = 1 := by
  exact LocalAlgebra.chi_norm p _ (U.unitPart_spec p).2

def theta {C : A.GeneralArithmeticContext σ η hS} (U : Frequency C)
    (p : ExteriorPrime A) : {θ : ℂ // ‖θ‖ = 1} :=
  ⟨chi (σ := σ) p
    (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (U.unitPart p)),
    U.unitPart_chi_norm p⟩

end Frequency

def V (p : ExteriorPrime A) (z : ℂ) : ℂ := qPower p (-6 * z)

def W (p : ExteriorPrime A) (u : A.R) (w : ℂ) : ℂ :=
  chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u) *
    qPower p (-w)

def D (p : ExteriorPrime A) (u : A.R) (ξ : ℂ) : ℂ :=
  η p.val.asIdeal *
    star (chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u)) *
    qPower p (-ξ)

def E (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (ξ z : ℂ) : ℂ := vartheta C p ^ 6 * qPower p (4 - 6 * ξ) * V p z

def goodRational (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (u : A.R) (ξ w z : ℂ) : ℂ :=
  let v := V p z
  let w₀ := W (σ := σ) p u w
  let d := D (σ := σ) (η := η) p u ξ
  let e := E C p ξ z
  1 / (1 - v) + w₀ / (1 - w₀) +
    e / (1 - e) * ((1 - (Q p : ℂ)⁻¹) / (1 - v) + w₀) -
    d / (1 - e) * (1 + ((Q p : ℂ) - 1) * w₀ * v / (1 - v))

def goodFactor (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (u : A.R) (ξ w z : ℂ) : ℂ :=
  (1 - V p z) * (1 - W (σ := σ) p u w) * goodRational C p u ξ w z /
    (1 - D (σ := σ) (η := η) p u ξ)

def badFactor (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1}) (ξ w z : ℂ) : ℂ :=
  (1 - V p z) * f C p j θ ξ w z

def localFactor (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (p : ExteriorPrime A) (ξ w z : ℂ) : ℂ :=
  if (U.j p).val = 0 then goodFactor C p U.u ξ w z
  else badFactor C p (U.j p) (U.theta p) ξ w z

theorem primitive_variables_zero (C : A.GeneralArithmeticContext σ η hS)
    (U : Frequency C) (p : ExteriorPrime A) (hp : (U.j p).val ≠ 0)
    (ξ w : ℂ) :
    W (σ := σ) p U.u w = 0 ∧ D (σ := σ) (η := η) p U.u ξ = 0 := by
  have hzero := ValuationGenerator.chi_eq_zero_of_decomposition C p U.u
    (U.unitPart p) (U.j p).val hp (U.unitPart_spec p).1
  simp [W, D, hzero]

def H_u (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (ξ w z : ℂ) (_hm : Multipliable (fun p : ExteriorPrime A =>
      localFactor C U p ξ w z)) : ℂ :=
  ∏' p : ExteriorPrime A, localFactor C U p ξ w z

def h_p (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (s : ℂ) : ℂ :=
  (1 - qPower p (-2)) *
    (1 - (1 - qPower p (-1)) * η p.val.asIdeal * qPower p (-s) -
      vartheta C p ^ 6 * qPower p (2 - 6 * s)) /
    ((1 - vartheta C p ^ 6 * qPower p (3 - 6 * s)) *
      (1 - η p.val.asIdeal * qPower p (-s)))

def H_eta (C : A.GeneralArithmeticContext σ η hS) (s : ℂ) : ℂ :=
  ∏' p : ExteriorPrime A, h_p C p s

end DedekindZetaZeroFree.CorrectionFactors

end
