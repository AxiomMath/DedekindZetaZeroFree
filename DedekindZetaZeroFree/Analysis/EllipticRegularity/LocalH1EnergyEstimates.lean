module

public import DedekindZetaZeroFree.Analysis.Sobolev.Restriction.IntegerOrderWeakDerivatives
public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.FirstOrderSmoothProducts
public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.H1TestContinuity
public import DedekindZetaZeroFree.Analysis.EllipticEquations.EnergyEstimates.CutoffQuadraticForms
public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.ClassicalToWeakSolutions
public import DedekindZetaZeroFree.Analysis.Sobolev.LocalEmbeddingAndSmoothRepresentatives

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.KPContLocalEnergy

open MeasureTheory
open KPContLocalNorm

def zeroIndex (n k : ℕ) : MultiIndex n k := ⟨fun _ => 0, by simp⟩

def firstIndex {n : ℕ} (i : Fin n) : MultiIndex n 1 :=
  ⟨fun j => if j = i then 1 else 0, by
    simp only [apply_ite Fin.val, Fin.val_one, Fin.val_zero]
    simp⟩

def value {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k) : BallL2 B :=
  u.derivatives (zeroIndex n k)

def gradient {n : ℕ} {B : LocalBall n} (u : IntegerSobolev B 1)
    (i : Fin n) : BallL2 B :=
  u.derivatives (firstIndex i)

structure Coefficients {n : ℕ} (B : LocalBall n) (cρ Cρ κ Λ : ℝ) where
  density : Space n → ℝ
  matrix : Space n → Matrix (Fin n) (Fin n) ℝ
  density_smooth : ContDiffOn ℝ (⊤ : ℕ∞) density B.carrier
  matrix_smooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => matrix x i j) B.carrier
  density_bounds : ∀ x ∈ B.carrier, cρ ≤ density x ∧ density x ≤ Cρ
  symmetric : ∀ x ∈ B.carrier, ∀ i j, matrix x i j = matrix x j i
  ellipticity : ∀ x ∈ B.carrier, ∀ ξ : Space n,
    κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, matrix x i j * ξ i * ξ j
  upper_bound : ∀ x ∈ B.carrier, ∀ ξ : Space n,
    (∑ i, ∑ j, matrix x i j * ξ i * ξ j) ≤ Λ * ‖ξ‖ ^ 2

def divergenceOperator {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (u : Space n → ℂ) : Space n → ℂ :=
  fun x => -(D.density x : ℂ)⁻¹ * ∑ i,
    fderiv ℝ (fun y => (D.density y : ℂ) *
      ∑ j, (D.matrix y i j : ℂ) * coordinateDerivativeList [j] u y) x
        (EuclideanSpace.single i 1)

def WeakEquation {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev B 1) (h : BallL2 B) : Prop :=
  ∀ φ : TestFunction B.toOpens ℂ ⊤,
    (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * value u x * star (φ x)) =
        ∫ x in B.carrier, (D.density x : ℂ) * h x * star (φ x)

def Represents {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k)
    (f : Space n → ℂ) : Prop :=
  ∀ᵐ x ∂volume.restrict B.carrier, value u x = f x

def RepresentsClassicalDerivatives {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (f : Space n → ℂ) : Prop :=
  ∀ α : MultiIndex n k,
    ∀ᵐ x ∂volume.restrict B.carrier, u.derivatives α x = coordinateDerivative α f x

def functionL2Norm {n : ℕ} (B : LocalBall n) (f : Space n → ℂ) : ℝ :=
  Real.sqrt (∫ x in B.carrier, ‖f x‖ ^ 2)

def WeakEnergyEstimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ) (M C : ℝ) : Prop :=
  ∀ (z : ℂ), ‖z‖ ≤ M → ∀ (u : IntegerSobolev outer 1) (h : BallL2 outer),
    WeakEquation D z u h → ∃ v : IntegerSobolev inner 1,
      Represents v (fun x => value u x) ∧
      v.sobolevNorm ≤ C * (‖value u‖ + ‖h‖)

def SmoothEnergyEstimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ) (M C : ℝ) : Prop :=
  ∀ (z : ℂ), ‖z‖ ≤ M → ∀ (u : Space n → ℂ) (h : BallL2 outer)
    (U : Set (Space n)), IsOpen U →
    Metric.closedBall outer.center outer.radius ⊆ U → ContDiffOn ℝ (⊤ : ℕ∞) u U →
    (∀ᵐ x ∂volume.restrict outer.carrier,
      divergenceOperator D u x - z * u x = h x) →
    ∃ v : IntegerSobolev inner 1, RepresentsClassicalDerivatives v u ∧
      v.sobolevNorm ≤ C * (functionL2Norm outer u + ‖h‖)

end DedekindZetaZeroFree.KPContLocalEnergy

namespace DedekindZetaZeroFree

open MeasureTheory KPContLocalNorm KPContLocalEnergy KPContLocalEnergy.SobolevEnergyEstimates

theorem kp_cont_local_energy_h1 (n : ℕ) (hn : 0 < n)
    (r R cρ Cρ κ Λ M : ℝ) (hr : 0 < r) (hrR : r < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (inner outer : LocalBall n),
      inner.center = outer.center → inner.radius = r → outer.radius = R →
      ∀ D : Coefficients outer cρ Cρ κ Λ,
        WeakEnergyEstimate inner outer D M C ∧ SmoothEnergyEstimate inner outer D M C := by
  obtain ⟨C, hC, hcutoff⟩ :=
    cutoff_quadratic_form_bound n hn r R cρ Cρ κ Λ M hr hrR hcρ hκ hM
  refine ⟨C, hC, ?_⟩
  intro inner outer hcenter hir hor D
  have hsub : inner.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hcenter, hir, hor]
    exact Metric.ball_subset_ball hrR.le
  obtain ⟨η, _hηone, hηenergy⟩ := hcutoff inner outer hcenter hir hor
  let Dr : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients outer cρ Cρ κ Λ :=
    { density := D.density
      matrix := D.matrix
      density_smooth := D.density_smooth
      matrix_smooth := D.matrix_smooth
      density_bounds := D.density_bounds
      symmetric := D.symmetric
      ellipticity := D.ellipticity
      upper_bound := D.upper_bound }
  have estimate : ∀ (z : ℂ), ‖z‖ ≤ M →
      ∀ (u : IntegerSobolev outer 1) (h : BallL2 outer), WeakEquation D z u h →
      ∃ v : IntegerSobolev inner 1,
        (∀ α : MultiIndex n 1, ∀ᵐ x ∂volume.restrict inner.carrier,
          v.derivatives α x = u.derivatives α x) ∧
        v.sobolevNorm ≤ C * (‖value u‖ + ‖h‖) := by
    intro z hz u h heq
    obtain ⟨w, hwvalue, hwgradient⟩ := multiply_smooth_compact outer η u
    have hwsupport : ∀ᵐ x ∂volume.restrict outer.carrier,
        x ∉ tsupport (fun y => η y) → value w x = 0 := by
      filter_upwards [hwvalue] with x hx
      intro hnot
      change KPContLocalEnergy.SobolevEnergyEstimates.Raw.value w x = 0
      rw [hx, image_eq_zero_of_notMem_tsupport hnot]
      simp
    obtain ⟨φ, hφ⟩ := approximate_compact_integerSobolev outer w
      (tsupport (fun y => η y)) η.hasCompactSupport η.tsupport_subset hwsupport
    have htest := weakEquation_of_test_limit outer cρ Cρ κ Λ hcρ hκ Dr z u h heq w φ hφ
    have hbound := hηenergy Dr z hz u h w hwvalue hwgradient htest
    obtain ⟨v, hvderivatives, hvnorm⟩ := restrict_integerSobolev inner outer hsub u
    refine ⟨v, hvderivatives, ?_⟩
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC.le (by positivity))).mp
    change v.sobolevNorm ^ 2 ≤ (C * (‖value u‖ + ‖h‖)) ^ 2
    rw [v.sobolevNorm_sq, hvnorm]
    exact hbound
  constructor
  · intro z hz u h heq
    obtain ⟨v, hv, hnorm⟩ := estimate z hz u h heq
    exact ⟨v, hv (zeroIndex n 1), hnorm⟩
  · intro z hz u h U hU hclosed hu heq
    obtain ⟨w, hwclassical, hweq, hwnorm⟩ :=
      smooth_solution_to_weak outer hcρ Dr z u h U hU hclosed hu heq
    obtain ⟨v, hv, hnorm⟩ := estimate z hz w h hweq
    refine ⟨v, ?_, ?_⟩
    · intro α
      have hwα := ae_restrict_of_ae_restrict_of_subset hsub (hwclassical α)
      filter_upwards [hv α, hwα] with x hxv hxw
      exact hxv.trans hxw
    · change ‖value w‖ = functionL2Norm outer u at hwnorm
      simpa only [hwnorm] using hnorm

end DedekindZetaZeroFree

end
