module

public import DedekindZetaZeroFree.Analysis.EllipticRegularity.IntegerSobolevEstimates

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContActualLocalSolutionFamily.CoefficientRestriction
open MeasureTheory KPContLocalNorm KPContLocalEnergy

 def wsr_restrictCoefficients {n : ℕ} {A B : LocalBall n} {cρ Cρ κ Λ : ℝ}
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

private lemma wsr_restrictCoefficients_smooth {n : ℕ} {A B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (hAB : A.carrier ⊆ B.carrier) (hclosed : Metric.closedBall A.center A.radius ⊆ B.carrier)
    (D : Coefficients B cρ Cρ κ Λ) :
    KPContLocalRegularity.SmoothNearClosedBall (wsr_restrictCoefficients hAB D) := by
  exact ⟨B.carrier, Metric.isOpen_ball, hclosed, D.density_smooth, D.matrix_smooth⟩

private lemma wsr_weakEquation_restrict {n : ℕ} {A B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (hAB : A.carrier ⊆ B.carrier) (D : Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev B 1) (h : BallL2 B) (hw : WeakEquation D z u h) :
    WeakEquation (wsr_restrictCoefficients hAB D) z (restrictSobolev hAB u)
      (restrictBallL2 hAB h) := by
  intro φ
  let ψ : TestFunction B.toOpens ℂ ⊤ :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hAB⟩
  have heq := hw ψ
  have hgrad : ∀ᵐ x ∂volume.restrict A.carrier,
      ∀ j, gradient (restrictSobolev hAB u) j x = gradient u j x := by
    apply ae_all_iff.mpr
    intro j
    exact restrictBallL2_ae hAB _
  have hv := restrictSobolev_represents hAB u
  have hh := restrictBallL2_ae hAB h
  change (∫ x in A.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient (restrictSobolev hAB u) j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in A.carrier, (D.density x : ℂ) * value (restrictSobolev hAB u) x *
        star (φ x)) =
        ∫ x in A.carrier, (D.density x : ℂ) * restrictBallL2 hAB h x * star (φ x)
  have hi : (∫ x in A.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient (restrictSobolev hAB u) j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) =
      ∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x) := by
    trans ∫ x in A.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)
    · apply integral_congr_ae
      filter_upwards [hgrad] with x hx
      simp only [hx]
    · symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hAB
      intro x hx
      have hz : ∀ i, coordinateDerivativeList [i] (fun y => φ y) x = 0 := by
        intro i
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        exact hx.2 (φ.tsupport_subset (coordinateDerivativeList_tsupport_subset [i] _ hm))
      simp [hz]
  have h0 (f : BallL2 B) :
      (∫ x in A.carrier, (D.density x : ℂ) * restrictBallL2 hAB f x * star (φ x)) =
      ∫ x in B.carrier, (D.density x : ℂ) * f x * star (φ x) := by
    trans ∫ x in A.carrier, (D.density x : ℂ) * f x * star (φ x)
    · apply integral_congr_ae
      filter_upwards [restrictBallL2_ae hAB f] with x hx
      rw [hx]
    · symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hAB
      intro x hx
      have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx.2 (φ.tsupport_subset hm))
      simp [hz]
  rw [hi, h0 h]
  change (∫ x in B.carrier, _) - z * (∫ x in A.carrier,
    (D.density x : ℂ) * restrictBallL2 hAB (value u) x * star (φ x)) = _
  rw [h0 (value u)]
  exact heq

 def wsr_liftIndex {n k l : ℕ} (h : k ≤ l) (a : MultiIndex n k) : MultiIndex n l :=
  ⟨fun i => ⟨(a.val i).val, lt_of_lt_of_le (a.val i).isLt (Nat.add_le_add_right h 1)⟩,
    le_trans a.property h⟩

 lemma wsr_liftIndex_zero {n k l : ℕ} (h : k ≤ l) :
    wsr_liftIndex (n := n) h (zeroIndex n k) = zeroIndex n l := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl

 def wsr_lowerSobolev {n k l : ℕ} {B : LocalBall n} (h : k ≤ l)
    (v : IntegerSobolev B l) : IntegerSobolev B k where
  derivatives a := v.derivatives (wsr_liftIndex h a)
  weak_derivatives a := by
    have hv := v.weak_derivatives (wsr_liftIndex h a)
    change ∀ φ, _ = _ at hv ⊢
    intro φ
    have heq := hv φ
    change (∫ x in B.carrier, v.derivatives (wsr_liftIndex h (zeroIndex n k)) x *
      coordinateDerivative a (fun y => φ y) x) = _
    rw [wsr_liftIndex_zero]
    exact heq

private lemma wsr_lowerSobolev_value {n k l : ℕ} {B : LocalBall n} (h : k ≤ l)
    (v : IntegerSobolev B l) : value (wsr_lowerSobolev h v) = value v := by
  change v.derivatives (wsr_liftIndex h (zeroIndex n k)) = _
  rw [wsr_liftIndex_zero]
  rfl

private lemma wsr_larger_ball {n : ℕ} (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) :
    ∃ C : LocalBall n, C.center = A.center ∧ A.radius < C.radius ∧
      Metric.closedBall C.center C.radius ⊆ B.carrier := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall A.center A.radius).exists_cthickening_subset_open
    Metric.isOpen_ball hAB
  rw [cthickening_closedBall hδ.le A.radius_pos.le] at hsub
  exact ⟨⟨A.dimension_pos, A.center, δ + A.radius, add_pos hδ A.radius_pos⟩,
    rfl, by dsimp; linarith, hsub⟩

private lemma wsr_smooth_forcing_memLp {n : ℕ} (B C : LocalBall n)
    (hCB : Metric.closedBall C.center C.radius ⊆ B.carrier)
    (f : Space n → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier) :
    MemLp f 2 (volume.restrict C.carrier) := by
  have hsub : C.carrier ⊆ Metric.closedBall C.center C.radius := Metric.ball_subset_closedBall
  have hcont : ContinuousOn f (Metric.closedBall C.center C.radius) :=
    hf.continuousOn.mono hCB
  obtain ⟨b, hb⟩ := (isCompact_closedBall C.center C.radius).exists_bound_of_continuousOn hcont
  haveI : IsFiniteMeasure (volume.restrict C.carrier) :=
    isFiniteMeasure_restrict.mpr (by
      exact (lt_of_le_of_lt (measure_mono hsub)
        ((isCompact_closedBall C.center C.radius).measure_lt_top (μ := volume))).ne)
  exact MemLp.of_bound ((hcont.mono hsub).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
    b ((ae_restrict_mem Metric.isOpen_ball.measurableSet).mono (fun x hx => hb x (hsub hx)))

private lemma wsr_forcing_toLp_eq {n : ℕ} {B C : LocalBall n}
    (hCB : C.carrier ⊆ B.carrier) (h : BallL2 B)
    (f : Space n → ℂ) (hf : f =ᵐ[volume.restrict B.carrier] (fun x => h x))
    (hL2 : MemLp f 2 (volume.restrict C.carrier)) :
    hL2.toLp f = restrictBallL2 hCB h := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp hL2, ae_restrict_of_ae_restrict_of_subset hCB hf,
    restrictBallL2_ae hCB h] with x hfx hxh hr
  exact hfx.trans (hxh.trans hr.symm)

private lemma wsr_local_all_sobolev {n : ℕ} (A : LocalBall n) {cρ Cρ κ Λ : ℝ}
    (D : Coefficients A cρ Cρ κ Λ) (hcρ : 0 < cρ) (hκ : 0 < κ) (z : ℂ)
    (u : IntegerSobolev A 1) (g : BallL2 A)
    (hw : WeakEquation D z u g)
    (h : Space n → ℂ) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h A.carrier)
    (hgh : h =ᵐ[volume.restrict A.carrier] (fun x => g x)) :
    KPContLocalCubeEmbedding.LocallyAllIntegerSobolev A.carrier (fun x => value u x) := by
  intro A' hA' k
  obtain ⟨C, hcen, hr, hC⟩ := wsr_larger_ball A' A hA'
  have hCA' : A'.center = C.center := hcen.symm
  have hsub : C.carrier ⊆ A.carrier := Metric.ball_subset_closedBall.trans hC
  let DC : Coefficients C cρ Cρ κ Λ := wsr_restrictCoefficients hsub D
  have hDC : KPContLocalRegularity.SmoothNearClosedBall DC :=
    wsr_restrictCoefficients_smooth hsub hC D
  let uC : IntegerSobolev C 1 := restrictSobolev hsub u
  have hfL2 : MemLp h 2 (volume.restrict C.carrier) :=
    wsr_smooth_forcing_memLp A C hC h hh
  have heq : WeakEquation DC z uC (hfL2.toLp h) := by
    rw [wsr_forcing_toLp_eq hsub g h hgh hfL2]
    exact wsr_weakEquation_restrict hsub D z u g hw
  obtain ⟨K, hK, _, he, _⟩ := kp_cont_local_regularity_iterate_fixed_coefficients n A' C
    hCA' hr cρ Cρ κ Λ ‖z‖ hcρ hκ (norm_nonneg _) DC hDC k
  obtain ⟨w, hwu, _⟩ := he z le_rfl uC h A.carrier Metric.isOpen_ball hC
    (hh.of_le (by simp)) hfL2 heq
  let v' : IntegerSobolev A' k := wsr_lowerSobolev (Nat.le_add_right k 2) w
  refine ⟨v', ?_⟩
  have heqw : (fun x => w.derivatives (zeroIndex n (k + 2)) x)
      =ᵐ[volume.restrict A'.carrier] (fun x => value uC x) := hwu
  have hA'C : A'.carrier ⊆ C.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hCA']
    exact Metric.ball_subset_ball hr.le
  have hval : (fun x => value uC x) =ᵐ[volume.restrict A'.carrier] (fun x => value u x) :=
    ae_restrict_of_ae_restrict_of_subset hA'C (restrictSobolev_represents hsub u)
  change (fun x => value u x) =ᵐ[volume.restrict A'.carrier] (fun x => value v' x)
  dsimp [v']
  rw [wsr_lowerSobolev_value]
  exact (heqw.trans hval).symm

theorem weighted_smooth_representative {n : ℕ} (A : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients A cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (hκ : 0 < κ)
    (hD : KPContLocalRegularity.SmoothNearClosedBall D)
    (z : ℂ) (v : IntegerSobolev A 1) (g : BallL2 A)
    (h : Space n → ℂ) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h A.carrier)
    (hg : h =ᵐ[volume.restrict A.carrier] (fun p => g p))
    (heq : WeakEquation D z v g) :
    ∃ f : Space n → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f A.carrier ∧
        (f =ᵐ[volume.restrict A.carrier] (fun p => value v p)) := by
  obtain ⟨f, hf, hfu, _⟩ :=
    KPContLocalCubeEmbedding.locally_all_orders_smooth_representative A.dimension_pos
      A.carrier Metric.isOpen_ball (fun x => value v x)
      (wsr_local_all_sobolev A D hcρ hκ z v g heq h hh hg)
  exact ⟨f, hf, hfu⟩

end DedekindZetaZeroFree.KPContActualLocalSolutionFamily.CoefficientRestriction

end
