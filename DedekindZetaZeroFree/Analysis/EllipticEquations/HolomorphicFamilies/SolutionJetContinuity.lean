module

public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.ScalarMultiplication

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

open MeasureTheory KPContLocalNorm

theorem finite_jet_bound_of_sobolev_representative {n : ℕ}
    (A C : LocalBall n) (hAC : KPContLocalCubeEmbedding.closedCarrier A ⊆ C.carrier)
    (m : ℕ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (w : IntegerSobolev C (m + n)) (g : Space n → ℂ),
      ContDiffOn ℝ (⊤ : ℕ∞) g C.carrier →
      (g =ᵐ[volume.restrict C.carrier]
        (fun x => w.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x)) →
      ∀ α : MultiIndex n m, ∀ x ∈ KPContLocalCubeEmbedding.closedCarrier A,
        ‖coordinateDerivative α g x‖ ≤ E * w.sobolevNorm := by
  obtain ⟨E, hE, hbound⟩ :=
    KPLocalCubeSobolevJets.finite_order_representative_interior_jet_bound A C hAC m
  refine ⟨E, hE, ?_⟩
  intro w g hg hgw α x hx
  obtain ⟨j, hj, hjbound⟩ := hbound w g (hg.of_le (by simp)) hgw
  letI : CompactSpace (KPContLocalCubeEmbedding.closedCarrier A) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall A.center A.radius)
  rw [← hj α ⟨x, hx⟩]
  exact (ContinuousMap.norm_coe_le_norm (j α) ⟨x, hx⟩).trans
    ((norm_le_pi_norm j α).trans hjbound)

theorem hilbert_difference_small {H : Type*} [NormedAddCommGroup H]
    (O : Set ℂ) (v : ℂ → H) (hv : ContinuousOn v O)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ O, dist z z₀ < δ → ‖v z - v z₀‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.mp (hv z₀ hz₀) ε hε
  exact ⟨δ, hδ, fun z hz hdist => by simpa [dist_eq_norm] using h hz hdist⟩

theorem smooth_holomorphic_jet_continuous {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (h : ℂ → Space n → ℂ)
    (hh : Raw.SmoothCompactOpenHolomorphicOn B h O) :
    Raw.JetContinuousOn B h O := by
  classical
  intro z₀ hz₀ K hK hKB m ε hε
  obtain ⟨ρ, hρ, hρO, coeff, hc⟩ := hh z₀ hz₀
  let r := ρ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : r < ρ := by dsimp [r]; linarith
  obtain ⟨N, hN⟩ := hc.2.2 K hK hKB m r hr.le hrρ (ε / 3) (by positivity)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let j : ℕ → CompactJets K m := fun q =>
    KPLocalCubeSobolevJets.finiteCompactJet B K hKB (coeff q)
      ((hc.1 q).of_le (by simp))
  let J : ℂ → CompactJets K m := fun z =>
    ∑ q ∈ Finset.range N, (z - z₀) ^ q • j q
  have hJ : Continuous J := by
    dsimp [J]
    fun_prop
  obtain ⟨δ, hδ, hδJ⟩ := Metric.continuousAt_iff.mp hJ.continuousAt
    (ε / 3) (by positivity)
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro z hz hdist α x
  have hzr : z ∈ Metric.closedBall z₀ r := by
    exact (Metric.mem_closedBall).mpr ((hdist.trans_le (min_le_right _ _)).le)
  have hzρ : z ∈ Metric.ball z₀ ρ :=
    Metric.closedBall_subset_ball hrρ hzr
  have hz₀r : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  have hz₀ρ : z₀ ∈ Metric.ball z₀ ρ := Metric.mem_ball_self hρ
  have hrem : ∀ t ∈ Metric.closedBall z₀ r,
      ‖J t α x - coordinateDerivative α (h t) x‖ < ε / 3 := by
    intro t ht
    have htρ := Metric.closedBall_subset_ball hrρ ht
    have he := coordinate_derivative_taylor_remainder B coeff hc.1 (h t)
      (hc.2.1 t htρ) (t - z₀) N α (hKB x.property)
    have hb := hN N le_rfl t ht α x
    rw [he] at hb
    have hval : J t α x = ∑ q ∈ Finset.range N,
        (t - z₀) ^ q * coordinateDerivative α (coeff q) x := by
      simp only [J, Finset.sum_apply, ContinuousMap.sum_apply,
        Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
      rfl
    rw [hval]
    exact hb
  have hmid : ‖J z α x - J z₀ α x‖ < ε / 3 := by
    have hb := hδJ (hdist.trans_le (min_le_left _ _))
    rw [dist_eq_norm] at hb
    exact lt_of_le_of_lt
      ((ContinuousMap.norm_coe_le_norm ((J z - J z₀) α) x).trans
        (norm_le_pi_norm (J z - J z₀) α)) hb
  rw [show coordinateDerivative α (fun y => h z y - h z₀ y) x =
      coordinateDerivative α (h z) x - coordinateDerivative α (h z₀) x from
    finite_coordinate_derivative_sub B (hc.2.1 z hzρ) (hc.2.1 z₀ hz₀ρ)
      α.directions (hKB x.property)]
  have hleft : ‖coordinateDerivative α (h z) x - J z α x‖ < ε / 3 := by
    rw [norm_sub_rev]
    exact hrem z hzr
  have hright := hrem z₀ hz₀r
  calc
    _ = ‖(coordinateDerivative α (h z) x - J z α x) +
        (J z α x - J z₀ α x) + (J z₀ α x - coordinateDerivative α (h z₀) x)‖ := by
      congr 1; ring
    _ ≤ ‖coordinateDerivative α (h z) x - J z α x‖ +
        ‖J z α x - J z₀ α x‖ + ‖J z₀ α x - coordinateDerivative α (h z₀) x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε := by linarith
 def iteratedDerivativeTest {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) (φ : TestFunction B.toOpens ℂ ⊤) :
    TestFunction B.toOpens ℂ ⊤ :=
  match l with
  | [] => φ
  | i :: l => TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1)
      (iteratedDerivativeTest l φ)

private theorem iteratedDerivativeTest_apply {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) (φ : TestFunction B.toOpens ℂ ⊤) :
    (fun x => iteratedDerivativeTest l φ x) = coordinateDerivativeList l (fun x => φ x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    simp only [iteratedDerivativeTest, coordinateDerivativeList]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM]
    rw [TestFunction.fderivCLM_apply_of_le _ (by simp)]
    change fderiv ℝ (fun y => iteratedDerivativeTest l φ y) x _ = _
    rw [ih]

private theorem lp_mul_test_integrable {n : ℕ} {B : LocalBall n}
    (u : BallL2 B) (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => u x * φ x) (volume.restrict B.carrier) :=
  (Lp.memLp u).integrable_mul
    (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport)

private theorem lp_mul_derivative_test_integrable {n k : ℕ} {B : LocalBall n}
    (u : BallL2 B) (α : MultiIndex n k) (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => u x * coordinateDerivative α (fun x => φ x) x)
      (volume.restrict B.carrier) := by
  simpa only [iteratedDerivativeTest_apply, coordinateDerivative] using
    lp_mul_test_integrable u (iteratedDerivativeTest α.directions φ)

theorem weak_derivative_sub {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u₁ u₂ d₁ d₂ : BallL2 B)
    (h₁ : IsWeakDerivative B α u₁ d₁) (h₂ : IsWeakDerivative B α u₂ d₂) :
    IsWeakDerivative B α (u₁ - u₂) (d₁ - d₂) := by
  intro φ
  have hleft : (∫ x in B.carrier, (u₁ - u₂) x *
      coordinateDerivative α (fun y => φ y) x) =
      (∫ x in B.carrier, u₁ x * coordinateDerivative α (fun y => φ y) x) -
      (∫ x in B.carrier, u₂ x * coordinateDerivative α (fun y => φ y) x) := by
    rw [← integral_sub (lp_mul_derivative_test_integrable u₁ α φ)
      (lp_mul_derivative_test_integrable u₂ α φ)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u₁ u₂] with x hx
    simp only [hx, Pi.sub_apply, sub_mul]
  have hright : (∫ x in B.carrier, (d₁ - d₂) x * φ x) =
      (∫ x in B.carrier, d₁ x * φ x) - (∫ x in B.carrier, d₂ x * φ x) := by
    rw [← integral_sub (lp_mul_test_integrable d₁ φ) (lp_mul_test_integrable d₂ φ)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub d₁ d₂] with x hx
    simp only [hx, Pi.sub_apply, sub_mul]
  change _ = (-1 : ℂ) ^ α.degree * _
  rw [hleft, hright, h₁ φ, h₂ φ, mul_sub]

def subtractSobolev {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) : IntegerSobolev B k where
  derivatives α := u.derivatives α - v.derivatives α
  weak_derivatives α := weak_derivative_sub B α _ _ _ _
    (u.weak_derivatives α) (v.weak_derivatives α)

theorem weak_derivative_smul {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (c : ℂ) (u d : BallL2 B) (h : IsWeakDerivative B α u d) :
    IsWeakDerivative B α (c • u) (c • d) := by
  intro φ
  have hleft : (∫ x in B.carrier, (c • u) x *
      coordinateDerivative α (fun y => φ y) x) =
      c * (∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hright : (∫ x in B.carrier, (c • d) x * φ x) =
      c * (∫ x in B.carrier, d x * φ x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c d] with x hx
    simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  change _ = (-1 : ℂ) ^ α.degree * _
  rw [hleft, hright, h φ]
  ring

def scaleSobolev {n k : ℕ} {B : LocalBall n}
    (c : ℂ) (u : IntegerSobolev B k) : IntegerSobolev B k where
  derivatives α := c • u.derivatives α
  weak_derivatives α := weak_derivative_smul B α c _ _ (u.weak_derivatives α)

theorem scaleSobolev_norm {n k : ℕ} {B : LocalBall n}
    (c : ℂ) (u : IntegerSobolev B k) :
    (scaleSobolev c u).sobolevNorm = ‖c‖ * u.sobolevNorm := by
  unfold IntegerSobolev.sobolevNorm IntegerSobolev.normSq
  simp only [scaleSobolev, norm_smul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_norm]

theorem subtractSobolev_norm_le {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) :
    (subtractSobolev u v).sobolevNorm ≤ 2 * (u.sobolevNorm + v.sobolevNorm) := by
  have hu : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  have hv : 0 ≤ v.sobolevNorm := Real.sqrt_nonneg _
  have hsq : (subtractSobolev u v).sobolevNorm ^ 2 ≤
      2 * (u.sobolevNorm ^ 2 + v.sobolevNorm ^ 2) := by
    rw [IntegerSobolev.sobolevNorm_sq, IntegerSobolev.sobolevNorm_sq,
      IntegerSobolev.sobolevNorm_sq]
    unfold IntegerSobolev.normSq
    simp only [subtractSobolev]
    calc
      _ ≤ ∑ α : MultiIndex n k, 2 * (‖u.derivatives α‖ ^ 2 + ‖v.derivatives α‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro α _
        have h := norm_sub_le (u.derivatives α) (v.derivatives α)
        have hnn := norm_nonneg (u.derivatives α - v.derivatives α)
        nlinarith [norm_nonneg (u.derivatives α), norm_nonneg (v.derivatives α),
          sq_nonneg (‖u.derivatives α‖ - ‖v.derivatives α‖)]
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hnn : 0 ≤ (subtractSobolev u v).sobolevNorm := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hu hv]

theorem subtractSobolev_represents {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) (f g : Space n → ℂ)
    (hu : (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] f)
    (hv : (fun x => v.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] g) :
    (fun x => (subtractSobolev u v).derivatives
      (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] (fun x => f x - g x) := by
  filter_upwards [hu, hv, Lp.coeFn_sub
    (u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k))
    (v.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k))] with x hx hy hsub
  change (u.derivatives _ - v.derivatives _) x = _
  simpa only [Pi.sub_apply, hx, hy] using hsub

theorem scaleSobolev_represents {n k : ℕ} {B : LocalBall n}
    (c : ℂ) (u : IntegerSobolev B k) (f : Space n → ℂ)
    (hu : (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] f) :
    (fun x => (scaleSobolev c u).derivatives
      (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] (fun x => c * f x) := by
  filter_upwards [hu, Lp.coeFn_smul c
    (u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k))] with x hx hsmul
  change (c • u.derivatives _) x = _
  simpa only [Pi.smul_apply, smul_eq_mul, hx] using hsmul

def addSobolev {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) : IntegerSobolev B k :=
  subtractSobolev u (scaleSobolev (-1) v)

theorem addSobolev_norm_le {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) :
    (addSobolev u v).sobolevNorm ≤ 2 * (u.sobolevNorm + v.sobolevNorm) := by
  simpa only [addSobolev, scaleSobolev_norm, norm_neg, norm_one, one_mul] using
    subtractSobolev_norm_le u (scaleSobolev (-1) v)

theorem addSobolev_represents {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) (f g : Space n → ℂ)
    (hu : (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] f)
    (hv : (fun x => v.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] g) :
    (fun x => (addSobolev u v).derivatives
      (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] (fun x => f x + g x) := by
  change (fun x => (subtractSobolev u (scaleSobolev (-1) v)).derivatives
      (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
    =ᵐ[volume.restrict B.carrier] (fun x => f x + g x)
  simpa only [neg_one_mul, sub_neg_eq_add] using
    subtractSobolev_represents u (scaleSobolev (-1) v) f (fun x => (-1 : ℂ) * g x)
      hu (scaleSobolev_represents (-1) v g hv)

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

end
