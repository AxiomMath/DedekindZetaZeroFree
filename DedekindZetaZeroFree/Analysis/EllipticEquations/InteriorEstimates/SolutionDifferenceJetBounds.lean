module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.HolomorphicFamilies.SolutionJetContinuity
public import DedekindZetaZeroFree.Geometry.Orbifolds.EllipticRegularity.EquivariantLineCharts

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContSmoothPromotion.LocalSolutionEstimates.LocalFamily
open MeasureTheory KPContLocalNorm KPContLocalOrbifold
open KPContLocalEnergy
open KPContLocalHolomorphyUpgrade.CauchyAssembly

private lemma pair_integrable {n : ℕ} {B : LocalBall n}
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (q : BallL2 B) (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => a x * q x * star (φ x)) (volume.restrict B.carrier) :=
  WeakJets.Raw.jet_localTest_integrable ha (WeakJets.Raw.conjugateTest φ) q

private lemma pair_sub {n : ℕ} {B : LocalBall n}
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (q r : BallL2 B) (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier, a x * (q-r) x * star (φ x)) =
      (∫ x in B.carrier, a x * q x * star (φ x)) -
      (∫ x in B.carrier, a x * r x * star (φ x)) := by
  rw [← integral_sub (pair_integrable ha q φ) (pair_integrable ha r φ)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub q r] with x hx
  simp only [hx, Pi.sub_apply, mul_sub, sub_mul]

private lemma difference_equation {n k : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (a₁ a₀ : ℂ)
    (u₁ u₀ : IntegerSobolev B 1) (g₁ g₀ : BallL2 B)
    (h₁ : WeakEquation D a₁ u₁ g₁) (h₀ : WeakEquation D a₀ u₀ g₀)
    (w : IntegerSobolev B k)
    (hw : Represents w (fun x => g₁ x - g₀ x + (a₁-a₀) * value u₁ x)) :
    WeakEquation D a₀ (subtractSobolev u₁ u₀) (value w) := by
  classical
  intro φ
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (D.density x : ℂ)) B.carrier :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn D.density_smooth
  have hρa (i j : Fin n) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => (D.density x : ℂ) * (D.matrix x i j : ℂ)) B.carrier :=
    hρ.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (D.matrix_smooth i j))
  let E := fun u : IntegerSobolev B 1 => fun x => (D.density x : ℂ) *
    ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
      star (coordinateDerivativeList [i] (fun y => φ y) x)
  have hE (u : IntegerSobolev B 1) : Integrable (E u) (volume.restrict B.carrier) := by
    have hterm (i j : Fin n) : Integrable (fun x =>
        (D.density x : ℂ) * (D.matrix x i j : ℂ) * gradient u j x *
          star (coordinateDerivativeList [i] (fun y => φ y) x))
        (volume.restrict B.carrier) := by
      exact pair_integrable (hρa i j) (gradient u j)
        (WeakJets.Raw.coordinateDerivativeTest (firstIndex i) φ) |>.congr
        (Filter.Eventually.of_forall (fun x => by
          change (D.density x : ℂ) * (D.matrix x i j : ℂ) * gradient u j x *
            star (coordinateDerivative (firstIndex i) (fun y => φ y) x) = _
          have hd : (firstIndex i).directions = [i] :=
            KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions i
          simp only [coordinateDerivative, hd]))
    have hh := integrable_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ (fun j _ => hterm i j))
    simpa only [E, Finset.mul_sum, mul_assoc] using hh
  have he : (∫ x in B.carrier, E (subtractSobolev u₁ u₀) x) =
      (∫ x in B.carrier, E u₁ x) - (∫ x in B.carrier, E u₀ x) := by
    rw [← integral_sub (hE u₁) (hE u₀)]
    apply integral_congr_ae
    have hs : ∀ᵐ x ∂volume.restrict B.carrier, ∀ j,
        gradient (subtractSobolev u₁ u₀) j x = gradient u₁ j x - gradient u₀ j x := by
      apply ae_all_iff.mpr
      intro j
      exact Lp.coeFn_sub (gradient u₁ j) (gradient u₀ j)
    filter_upwards [hs] with x hx
    simp only [E, hx, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hv : value (subtractSobolev u₁ u₀) = value u₁ - value u₀ := rfl
  have hf : (∫ x in B.carrier, (D.density x : ℂ) * value w x * star (φ x)) =
      (∫ x in B.carrier, (D.density x : ℂ) * g₁ x * star (φ x)) -
      (∫ x in B.carrier, (D.density x : ℂ) * g₀ x * star (φ x)) +
      (a₁-a₀) * (∫ x in B.carrier, (D.density x : ℂ) * value u₁ x * star (φ x)) := by
    calc
      _ = ∫ x in B.carrier,
          ((D.density x : ℂ) * g₁ x * star (φ x) -
            (D.density x : ℂ) * g₀ x * star (φ x)) +
            (a₁-a₀) * ((D.density x : ℂ) * value u₁ x * star (φ x)) := by
        apply integral_congr_ae
        filter_upwards [hw] with x hx
        rw [hx]
        ring
      _ = _ := by
        change (∫ x in B.carrier,
          ((fun x => (D.density x : ℂ) * g₁ x * star (φ x)) -
            (fun x => (D.density x : ℂ) * g₀ x * star (φ x))) x +
            (a₁-a₀) * ((D.density x : ℂ) * value u₁ x * star (φ x))) = _
        rw [integral_add ((pair_integrable hρ g₁ φ).sub (pair_integrable hρ g₀ φ))
          ((pair_integrable hρ (value u₁) φ).const_mul _)]
        simp only [Pi.sub_apply]
        rw [integral_sub (pair_integrable hρ g₁ φ) (pair_integrable hρ g₀ φ),
          integral_const_mul]
  change (∫ x in B.carrier, E (subtractSobolev u₁ u₀) x) -
    a₀ * (∫ x in B.carrier, (D.density x : ℂ) * value (subtractSobolev u₁ u₀) x * star (φ x)) = _
  rw [he, hv, pair_sub hρ, hf]
  linear_combination h₁ φ - h₀ φ

theorem chart_solution_difference_jet_estimate {n : ℕ} (D : LineChart n)
    (K : Set (Space n)) (hK : IsCompact K) (hKD : K ⊆ D.outer.carrier)
    (m : ℕ) (a₀ : ℂ) :
    ∃ C : LocalBall n, Metric.closedBall C.center C.radius ⊆ D.outer.carrier ∧
      ∃ T : ℝ, 0 < T ∧
        ∀ (a₁ : ℂ) (u₁ u₀ : IntegerSobolev D.outer 1)
          (g₁ g₀ : BallL2 D.outer) (f₁ f₀ : Space n → ℂ),
          KPContLocalEnergy.WeakEquation D.coefficients a₁ u₁ g₁ →
          KPContLocalEnergy.WeakEquation D.coefficients a₀ u₀ g₀ →
          ContDiffOn ℝ (⊤ : ℕ∞) f₁ D.outer.carrier →
          ContDiffOn ℝ (⊤ : ℕ∞) f₀ D.outer.carrier →
          KPContLocalEnergy.Represents u₁ f₁ →
          KPContLocalEnergy.Represents u₀ f₀ →
          ∀ w : IntegerSobolev C (m + n),
            KPContLocalEnergy.Represents w
              (fun x => g₁ x - g₀ x + (a₁ - a₀) * f₁ x) →
            ∀ α : MultiIndex n m, ∀ x : K,
              ‖coordinateDerivative α (fun y => f₁ y - f₀ y) x‖ ≤
                T * (‖KPContLocalEnergy.value u₁ - KPContLocalEnergy.value u₀‖ +
                  w.sobolevNorm) := by
  classical
  obtain ⟨r, ⟨hr, hrR⟩, hKr⟩ :=
    exists_pos_lt_subset_ball D.outer.radius_pos hK.isClosed hKD
  let A : LocalBall n := ⟨D.outer.dimension_pos, D.outer.center, r, hr⟩
  let B : LocalBall n := ⟨D.outer.dimension_pos, D.outer.center,
    (r + D.outer.radius) / 2, by linarith [D.outer.radius_pos]⟩
  let C : LocalBall n := ⟨D.outer.dimension_pos, D.outer.center,
    (B.radius + D.outer.radius) / 2, by dsimp [B]; linarith [D.outer.radius_pos]⟩
  have hAB : Metric.closedBall A.center A.radius ⊆ B.carrier :=
    Metric.closedBall_subset_ball (by dsimp [A, B]; linarith)
  have hBCr : B.radius < C.radius := by dsimp [B, C]; linarith
  have hBC : Metric.closedBall B.center B.radius ⊆ C.carrier :=
    Metric.closedBall_subset_ball hBCr
  have hCD : Metric.closedBall C.center C.radius ⊆ D.outer.carrier :=
    Metric.closedBall_subset_ball (by dsimp [C, B]; linarith)
  have hsub : C.carrier ⊆ D.outer.carrier := Metric.ball_subset_closedBall.trans hCD
  let DR : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients D.outer D.densityLower
      D.densityUpper D.ellipticityLower D.ellipticityUpper :=
    { density := D.coefficients.density
      matrix := D.coefficients.matrix
      density_smooth := D.coefficients.density_smooth
      matrix_smooth := D.coefficients.matrix_smooth
      density_bounds := D.coefficients.density_bounds
      symmetric := D.coefficients.symmetric
      ellipticity := D.coefficients.ellipticity
      upper_bound := D.coefficients.upper_bound }
  let DC : Coefficients C D.densityLower D.densityUpper
      D.ellipticityLower D.ellipticityUpper :=
    { density := D.coefficients.density
      matrix := D.coefficients.matrix
      density_smooth := D.coefficients.density_smooth.mono hsub
      matrix_smooth := fun i j => (D.coefficients.matrix_smooth i j).mono hsub
      density_bounds := fun x hx => D.coefficients.density_bounds x (hsub hx)
      symmetric := fun x hx => D.coefficients.symmetric x (hsub hx)
      ellipticity := fun x hx => D.coefficients.ellipticity x (hsub hx)
      upper_bound := fun x hx => D.coefficients.upper_bound x (hsub hx) }
  have hDC : KPContLocalRegularity.SmoothNearClosedBall DC :=
    ⟨D.outer.carrier, Metric.isOpen_ball, hCD,
      D.coefficients.density_smooth, D.coefficients.matrix_smooth⟩
  obtain ⟨L, hL, he, _⟩ := kp_cont_local_regularity_iterate_fixed_coefficients n B C
    rfl hBCr D.densityLower D.densityUpper D.ellipticityLower D.ellipticityUpper
    ‖a₀‖ D.densityLower_pos D.ellipticityLower_pos (norm_nonneg _) DC hDC (m+n)
  obtain ⟨E, hE, hjet⟩ := finite_jet_bound_of_sobolev_representative A B hAB (m+2)
  refine ⟨C, hCD, E*L, mul_pos hE hL, ?_⟩
  intro a₁ u₁ u₀ g₁ g₀ f₁ f₀ he₁ he₀ hf₁ hf₀ hu₁ hu₀ w hw α x
  have he₁R : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation DR a₁ u₁ g₁ := he₁
  have he₀R : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation DR a₀ u₀ g₀ := he₀
  obtain ⟨v₁, q₁, hv₁, hq₁, _, _, heq₁⟩ :=
    KPContLocalRegularity.SobolevIteration.restrict_weak_equation hsub DR a₁ u₁ g₁ he₁R
  obtain ⟨v₀, q₀, hv₀, hq₀, _, _, heq₀⟩ :=
    KPContLocalRegularity.SobolevIteration.restrict_weak_equation hsub DR a₀ u₀ g₀ he₀R
  have hw' : Represents w (fun y => q₁ y - q₀ y + (a₁-a₀) * value v₁ y) := by
    filter_upwards [hw, hq₁, hq₀, hv₁ (zeroIndex n 1),
      ae_restrict_of_ae_restrict_of_subset hsub hu₁] with y hwy hq₁y hq₀y hv₁y hu₁y
    change value w y = _ at hwy ⊢
    change value v₁ y = value u₁ y at hv₁y
    rw [hwy, hq₁y, hq₀y, hv₁y, hu₁y]
  have heq : WeakEquation DC a₀ (subtractSobolev v₁ v₀) (value w) :=
    difference_equation DC a₁ a₀ v₁ v₀ q₁ q₀ heq₁ heq₀ w hw'
  obtain ⟨v, hv, hb⟩ := he a₀ le_rfl (subtractSobolev v₁ v₀) w heq
  have hnorm : ‖value (subtractSobolev v₁ v₀)‖ ≤ ‖value u₁ - value u₀‖ := by
    have heqval : value (subtractSobolev v₁ v₀) =
        restrictBallL2 hsub (value u₁ - value u₀) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (value v₁) (value v₀),
        hv₁ (zeroIndex n 1), hv₀ (zeroIndex n 1),
        restrictBallL2_ae hsub (value u₁ - value u₀),
        ae_restrict_of_ae_restrict_of_subset hsub (Lp.coeFn_sub (value u₁) (value u₀))]
        with y hs h₁ h₀ hr hs'
      change value v₁ y = value u₁ y at h₁
      change value v₀ y = value u₀ y at h₀
      change (value v₁ - value v₀) y = _
      simp only [Pi.sub_apply] at hs hs'
      rw [hs, h₁, h₀, hr, hs']
    rw [heqval]
    exact norm_restrictBallL2_le hsub _
  have hBD : B.carrier ⊆ D.outer.carrier :=
    Metric.ball_subset_closedBall.trans (hBC.trans hsub)
  have hBCsub : B.carrier ⊆ C.carrier := Metric.ball_subset_closedBall.trans hBC
  have hrep : Represents v (fun y => f₁ y - f₀ y) := by
    have hs₁ : (fun y => value v₁ y) =ᵐ[volume.restrict C.carrier] f₁ := by
      filter_upwards [hv₁ (zeroIndex n 1),
        ae_restrict_of_ae_restrict_of_subset hsub hu₁] with y hvy huy
      exact hvy.trans huy
    have hs₀ : (fun y => value v₀ y) =ᵐ[volume.restrict C.carrier] f₀ := by
      filter_upwards [hv₀ (zeroIndex n 1),
        ae_restrict_of_ae_restrict_of_subset hsub hu₀] with y hvy huy
      exact hvy.trans huy
    have hs := subtractSobolev_represents v₁ v₀ f₁ f₀ hs₁ hs₀
    filter_upwards [hv, ae_restrict_of_ae_restrict_of_subset hBCsub hs] with y hvy hsy
    exact hvy.trans hsy
  have hex : ∃ v' : IntegerSobolev B (m+2+n),
      Represents v' (fun y => f₁ y-f₀ y) ∧
      v'.sobolevNorm ≤ L * (‖value u₁ - value u₀‖ + w.sobolevNorm) := by
    rw [show m+2+n = m+n+2 by omega]
    exact ⟨v, hrep, hb.trans (mul_le_mul_of_nonneg_left
      (by linarith : ‖value (subtractSobolev v₁ v₀)‖ + w.sobolevNorm ≤
        ‖value u₁ - value u₀‖ + w.sobolevNorm) hL.le)⟩
  obtain ⟨v', hv', hb'⟩ := hex
  let β : MultiIndex n (m+2) :=
    ⟨fun i => (α.val i).castLE (by omega),
      by simpa using α.property.trans (by omega : m ≤ m+2)⟩
  have hder : coordinateDerivative β (fun y => f₁ y-f₀ y) =
      coordinateDerivative α (fun y => f₁ y-f₀ y) := rfl
  rw [← hder]
  have hv'ae : (fun y => value v' y) =ᵐ[volume.restrict B.carrier]
      (fun y => f₁ y-f₀ y) := hv'
  exact (hjet v' (fun y => f₁ y-f₀ y) ((hf₁.sub hf₀).mono hBD)
    hv'ae.symm β x (Metric.ball_subset_closedBall (hKr x.property))).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb' hE.le)

end DedekindZetaZeroFree.KPContSmoothPromotion.LocalSolutionEstimates.LocalFamily

end
