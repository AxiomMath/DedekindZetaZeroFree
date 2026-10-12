module

public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.IntegerSobolevEstimates

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContLocalOrbifold

open MeasureTheory
open KPContLocalNorm KPContLocalEnergy KPContLocalRegularity

structure LineChart (n : ℕ) where
  stabilizer : Type
  group : Group stabilizer
  finite : Fintype stabilizer
  action : stabilizer →* (Space n ≃ₗᵢ[ℝ] Space n)
  lineAction : stabilizer →* ℂˣ
  unitary : ∀ g, ‖(lineAction g : ℂ)‖ = 1
  inner : LocalBall n
  outer : LocalBall n
  concentric : inner.center = outer.center
  radii_lt : inner.radius < outer.radius
  fixes_center : ∀ g, action g outer.center = outer.center
  densityLower : ℝ
  densityUpper : ℝ
  ellipticityLower : ℝ
  ellipticityUpper : ℝ
  densityLower_pos : 0 < densityLower
  ellipticityLower_pos : 0 < ellipticityLower
  coefficients : Coefficients outer densityLower densityUpper
    ellipticityLower ellipticityUpper
  smooth_coefficients : SmoothNearClosedBall coefficients
  density_invariant : ∀ g, ∀ x ∈ outer.carrier,
    coefficients.density (action g x) = coefficients.density x
  cutoff : Space n → ℝ
  cutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ outer.carrier
  cutoff_one : ∀ x ∈ Metric.closedBall inner.center inner.radius, cutoff x = 1
  cutoff_invariant : ∀ g, ∀ x, cutoff (action g x) = cutoff x

attribute [instance] LineChart.group LineChart.finite

def Equivariant {n : ℕ} (D : LineChart n) (U : Set (Space n))
    (f : Space n → ℂ) : Prop :=
  ∀ g : D.stabilizer, ∀ x ∈ U,
    f (D.action g x) = (D.lineAction g : ℂ) * f x

def AEEquivariant {n : ℕ} (D : LineChart n) (B : LocalBall n)
    (f : Space n → ℂ) : Prop :=
  ∀ g : D.stabilizer, ∀ᵐ x ∂volume.restrict B.carrier,
    f (D.action g x) = (D.lineAction g : ℂ) * f x

def chartL2Norm {n : ℕ} (D : LineChart n) (B : LocalBall n)
    (f : Space n → ℂ) : ℝ :=
  Real.sqrt ((Fintype.card D.stabilizer : ℝ)⁻¹ *
    ∫ x in B.carrier, D.coefficients.density x * ‖f x‖ ^ 2)

 def chartRep_restrictCoefficients {n : ℕ} {A B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (hAB : A.carrier ⊆ B.carrier) (D : Coefficients B cρ Cρ κ Λ) :
    Coefficients A cρ Cρ κ Λ where
  density := D.density
  matrix := D.matrix
  density_smooth := D.density_smooth.mono hAB
  matrix_smooth i j := (D.matrix_smooth i j).mono hAB
  density_bounds x hx := D.density_bounds x (hAB hx)
  symmetric x hx := D.symmetric x (hAB hx)
  ellipticity x hx := D.ellipticity x (hAB hx)
  upper_bound x hx := D.upper_bound x (hAB hx)

 def chartRep_liftIndex {n k l : ℕ} (h : k ≤ l) (a : MultiIndex n k) : MultiIndex n l :=
  ⟨fun i => ⟨(a.val i).val, lt_of_lt_of_le (a.val i).isLt (Nat.add_le_add_right h 1)⟩,
    le_trans a.property h⟩
 lemma chartRep_liftIndex_zero {n k l : ℕ} (h : k ≤ l) :
    chartRep_liftIndex (n := n) h (zeroIndex n k) = zeroIndex n l := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl
 def chartRep_lowerSobolev {n k l : ℕ} {B : LocalBall n} (h : k ≤ l)
    (v : IntegerSobolev B l) : IntegerSobolev B k where
  derivatives a := v.derivatives (chartRep_liftIndex h a)
  weak_derivatives a := by
    have hv := v.weak_derivatives (chartRep_liftIndex h a)
    change ∀ φ, _ = _ at hv ⊢
    intro φ
    have heq := hv φ
    change (∫ x in B.carrier, v.derivatives (chartRep_liftIndex h (zeroIndex n k)) x *
      coordinateDerivative a (fun y => φ y) x) = _
    rw [chartRep_liftIndex_zero]
    exact heq

end DedekindZetaZeroFree.KPContLocalOrbifold

end
