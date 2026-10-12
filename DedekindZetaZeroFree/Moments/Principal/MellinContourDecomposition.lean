module

public import DedekindZetaZeroFree.Moments.Principal.NumeratorPoleExtraction

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open MeasureTheory Complex

namespace PrincipalZShift

def zLine : ℝ := 4 / 25

def c₀ (RS : ℂ) (M W : ℂ → ℂ) : ℂ :=
  RS ^ 2 / 6 * M (1 / 6) * W 1

def transformKernel (Z : ℝ) (L Hη : ℂ → ℂ) (ξ : ℂ) : ℂ :=
  comparisonRealPower Z (comparisonC ξ) *
    Complex.exp ((ξ - 5 / 6) ^ 2) * (Hη ξ / L ξ)

def f (Z : ℝ) (L Hη : ℂ → ℂ) : ℂ :=
  comparisonVerticalIntegral 2 (transformKernel Z L Hη)

def Rw (Z : ℝ) (M W ζ L : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ) : ℂ :=
  PrincipalWShift.J Z M W ζ L H comparisonSigma₁ (19 / 20) comparisonZeta₁

def Rz (Z : ℝ) (RS : ℂ) (M W ζ L : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) : ℂ :=
  RS * PrincipalWShift.doubleVerticalIntegral comparisonSigma₁ zLine
    (PrincipalWShift.residueKernel Z M W ζ L H)

def clearedKernel (Z : ℝ) (M W L R : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) (ξ z : ℂ) : ℂ :=
  comparisonRealPower (comparisonX Z) (1 / 2 - z) *
    comparisonRealPower Z (ξ + z - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * M z * W 1 *
    (R (6 * z) / 6 / L ξ) * H ξ 1 z

theorem clearedKernel_off_pole (Z : ℝ) (M W ζ L R : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) (ξ z : ℂ) (hz : z ≠ 1 / 6)
    (hR : R (6 * z) = (6 * z - 1) * ζ (6 * z)) :
    clearedKernel Z M W L R H ξ z =
      (z - 1 / 6) * PrincipalWShift.residueKernel Z M W ζ L H ξ z := by
  unfold clearedKernel PrincipalWShift.residueKernel
  rw [hR]
  ring

theorem c₀_ne_zero (RS : ℂ) (M W : ℂ → ℂ)
    (hRS : RS ≠ 0) (hM : M (1 / 6) ≠ 0) (hW : W 1 ≠ 0) :
    c₀ RS M W ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (div_ne_zero (pow_ne_zero 2 hRS) (by norm_num)) hM) hW

structure ZContourConditions (Z : ℝ) (M W ζ L R Hη : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) where
  U : Set ℂ
  C : ℝ
  C_nonneg : 0 ≤ C
  open_U : IsOpen U
  strip : comparisonClosedStrip zLine comparisonZeta₁ ⊆ U
  regularization : ∀ z ∈ U, z ≠ 1 / 6 →
    R (6 * z) = (6 * z - 1) * ζ (6 * z)
  holomorphic : ∀ ξ : ℂ, ξ.re = comparisonSigma₁ →
    DifferentiableOn ℂ (fun z => clearedKernel Z M W L R H ξ z) U
  decay : ∀ ξ z : ℂ, ξ.re = comparisonSigma₁ →
    z ∈ comparisonClosedStrip zLine comparisonZeta₁ → 1 ≤ |z.im| →
    ‖PrincipalWShift.residueKernel Z M W ζ L H ξ z‖ ≤
      C * (1 + |ξ.im|) ^ (-2 : ℝ) * (1 + |z.im|) ^ (-2 : ℝ)
  endpoints : ∀ σz ∈ ({zLine, comparisonZeta₁} : Set ℝ),
    Integrable (fun t : ℝ × ℝ =>
      PrincipalWShift.residueKernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (t.1 : ℂ) * I)
        ((σz : ℂ) + (t.2 : ℂ) * I))
  residue : Integrable (fun t : ℝ =>
    transformKernel Z L Hη ((comparisonSigma₁ : ℂ) + (t : ℂ) * I))

structure XiContourConditions (Z : ℝ) (L Hη : ℂ → ℂ) where
  U : Set ℂ
  C : ℝ
  C_nonneg : 0 ≤ C
  open_U : IsOpen U
  strip : comparisonClosedStrip comparisonSigma₁ 2 ⊆ U
  holomorphic : DifferentiableOn ℂ (transformKernel Z L Hη) U
  decay : ∀ ξ ∈ comparisonClosedStrip comparisonSigma₁ 2,
    ‖transformKernel Z L Hη ξ‖ ≤ C * (1 + |ξ.im|) ^ (-2 : ℝ)

theorem xi_shift (Z : ℝ) (L Hη : ℂ → ℂ)
    (hcontour : XiContourConditions Z L Hη) :
    Integrable (fun t : ℝ =>
      transformKernel Z L Hη ((comparisonSigma₁ : ℂ) + (t : ℂ) * I)) ∧
    Integrable (fun t : ℝ => transformKernel Z L Hη (2 + (t : ℂ) * I)) ∧
    comparisonVerticalIntegral comparisonSigma₁ (transformKernel Z L Hη) =
      f Z L Hη := by
  have hab : comparisonSigma₁ < (2 : ℝ) := by
    norm_num [comparisonSigma₁, comparisonDelta]
  have hi := verticalIntegral_integrable_of_strip_decay comparisonSigma₁ 2
    hcontour.C (transformKernel Z L Hη) hcontour.U hab hcontour.C_nonneg
    hcontour.open_U hcontour.strip hcontour.holomorphic hcontour.decay
  refine ⟨hi comparisonSigma₁ ⟨le_rfl, hab.le⟩, ?_, ?_⟩
  · simpa using hi 2 ⟨hab.le, le_rfl⟩
  · unfold f comparisonVerticalIntegral
    congr 1
    exact verticalIntegral_eq_of_strip_decay comparisonSigma₁ 2 hcontour.C
      (transformKernel Z L Hη) hcontour.U hab hcontour.C_nonneg
      hcontour.open_U hcontour.strip hcontour.holomorphic hcontour.decay

structure InitialContourConditions (Z : ℝ) (M W ζ L : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) where
  U : Set (ℂ × ℂ × ℂ)
  C : ℝ
  C_nonneg : 0 ≤ C
  open_U : IsOpen U
  corridor : ∀ ξ w z : ℂ,
    ξ.re ∈ Set.Icc comparisonSigma₁ 4 →
    w.re ∈ Set.Icc comparisonSigma₁ 4 →
    z.re ∈ Set.Icc comparisonZeta₁ 2 → (ξ, w, z) ∈ U
  holomorphic_xi : ∀ w z : ℂ,
    DifferentiableOn ℂ (fun ξ => PrincipalWShift.kernel Z M W ζ L H ξ w z)
      {ξ | (ξ, w, z) ∈ U}
  holomorphic_w : ∀ ξ z : ℂ,
    DifferentiableOn ℂ (fun w => PrincipalWShift.kernel Z M W ζ L H ξ w z)
      {w | (ξ, w, z) ∈ U}
  holomorphic_z : ∀ ξ w : ℂ,
    DifferentiableOn ℂ (fun z => PrincipalWShift.kernel Z M W ζ L H ξ w z)
      {z | (ξ, w, z) ∈ U}
  decay : ∀ ξ w z : ℂ, (ξ, w, z) ∈ U →
    ‖PrincipalWShift.kernel Z M W ζ L H ξ w z‖ ≤
      C * (1 + |ξ.im|) ^ (-2 : ℝ) *
        (1 + |w.im|) ^ (-2 : ℝ) * (1 + |z.im|) ^ (-2 : ℝ)

structure WContourConditions (Z : ℝ) (M W ζ L R : ℂ → ℂ)
    (H : ℂ → ℂ → ℂ → ℂ) where
  U : Set ℂ
  C : ℝ
  C_nonneg : 0 ≤ C
  open_U : IsOpen U
  strip : comparisonClosedStrip (19 / 20) comparisonSigma₁ ⊆ U
  regularization : ∀ w ∈ U, w ≠ 1 → R w = (w - 1) * ζ w
  holomorphic : ∀ ξ z : ℂ, ξ.re = comparisonSigma₁ → z.re = comparisonZeta₁ →
    DifferentiableOn ℂ (fun w => PrincipalWShift.clearedKernel Z M W ζ L R H ξ w z) U
  decay : ∀ ξ w z : ℂ,
    ξ.re = comparisonSigma₁ → z.re = comparisonZeta₁ →
    w ∈ comparisonClosedStrip (19 / 20) comparisonSigma₁ → 1 ≤ |w.im| →
    ‖PrincipalWShift.kernel Z M W ζ L H ξ w z‖ ≤
      C * (1 + |ξ.im|) ^ (-2 : ℝ) *
        (1 + |z.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ)
  endpoints : ∀ σw ∈ ({(19 / 20 : ℝ), comparisonSigma₁} : Set ℝ),
    Integrable (fun t : ℝ × ℝ × ℝ =>
      PrincipalWShift.kernel Z M W ζ L H
        ((comparisonSigma₁ : ℂ) + (t.1 : ℂ) * I)
        ((σw : ℂ) + (t.2.1 : ℂ) * I)
        ((comparisonZeta₁ : ℂ) + (t.2.2 : ℂ) * I))
  residue : Integrable (fun t : ℝ × ℝ =>
    PrincipalWShift.residueKernel Z M W ζ L H
      ((comparisonSigma₁ : ℂ) + (t.1 : ℂ) * I)
      ((comparisonZeta₁ : ℂ) + (t.2 : ℂ) * I))

end PrincipalZShift
end
end DedekindZetaZeroFree
