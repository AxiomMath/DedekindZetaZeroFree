module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.InteriorEstimates.SolutionDifferenceJetBounds
public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContActualLocalSolutionFamily.CoefficientRestriction
open MeasureTheory KPContLocalNorm KPContLocalEnergy

open KPContLocalHolomorphyUpgrade.CauchyAssembly KPContLocalRegularity

private theorem forcing_jet_continuity {n : ℕ} (A : LocalBall n)
    (Ω : Set ℂ) (h : ℂ → Space n → ℂ)
    (hh : KPCutoffSource.ChartSmoothHolomorphicOn A h Ω) :
    Raw.JetContinuousOn A h Ω := by
  intro z₀ hz₀ K hK hKA m ε hε
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j, hj, hspec⟩ := hh.2 K hK hKA m
  obtain ⟨δ, hδ, hd⟩ := hilbert_difference_small Ω j hj.continuousOn hz₀ hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz hdist α x
  have hb := hd z hz hdist
  have hp := (ContinuousMap.norm_coe_le_norm ((j z - j z₀) α) x).trans
    (norm_le_pi_norm (j z - j z₀) α)
  change ‖j z α x - j z₀ α x‖ ≤ _ at hp
  rw [hspec z hz α x, hspec z₀ hz₀ α x] at hp
  rw [coordinateDerivative,
    finite_coordinate_derivative_sub A (hh.1 z hz) (hh.1 z₀ hz₀)
      α.directions (hKA x.property), ← coordinateDerivative, ← coordinateDerivative]
  exact hp.trans_lt hb

open KPContLocalOrbifold

private lemma deriv_smooth {n : ℕ} (B : LocalBall n) (u : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) (l : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) B.carrier := by
  induction l with
  | nil => exact hu
  | cons i l ih =>
    exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const

 def normFactor {n : ℕ} (C : LocalBall n) (k : ℕ) : ℝ :=
  (Fintype.card (MultiIndex n k) : ℝ) *
    (measureUnivNNReal (volume.restrict C.carrier) : ℝ) ^ (2 : ℝ)⁻¹ + 1

private lemma normFactor_pos {n : ℕ} (C : LocalBall n) (k : ℕ) :
    0 < normFactor C k := by unfold normFactor; positivity

private lemma smooth_bound {n : ℕ} (B C : LocalBall n)
    (hCB : Metric.closedBall C.center C.radius ⊆ B.carrier) (k : ℕ)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (P : ℝ) (hP : 0 ≤ P)
    (hb : ∀ α : MultiIndex n k, ∀ x ∈ C.carrier, ‖coordinateDerivative α u x‖ ≤ P) :
    ∃ w : IntegerSobolev C k, Represents w u ∧ w.sobolevNorm ≤ normFactor C k * P := by
  classical
  have hsub : C.carrier ⊆ Metric.closedBall C.center C.radius := Metric.ball_subset_closedBall
  haveI : IsFiniteMeasure (volume.restrict C.carrier) := isFiniteMeasure_restrict.mpr
    ((lt_of_le_of_lt (measure_mono hsub)
      ((isCompact_closedBall C.center C.radius).measure_lt_top (μ := volume))).ne)
  have hL2 : ∀ α : MultiIndex n k,
      MemLp (coordinateDerivative α u) 2 (volume.restrict C.carrier) := by
    intro α
    apply MemLp.of_bound
      (((deriv_smooth B u hu α.directions).continuousOn.mono (hsub.trans hCB)).aestronglyMeasurable
        Metric.isOpen_ball.measurableSet) P
    exact (ae_restrict_mem Metric.isOpen_ball.measurableSet).mono (fun x hx => hb α x hx)
  obtain ⟨w, hw⟩ := smooth_has_integerSobolev_data C u (hu.mono (hsub.trans hCB)) hL2
  have hd : ∀ α : MultiIndex n k, ‖w.derivatives α‖ ≤
      (measureUnivNNReal (volume.restrict C.carrier) : ℝ) ^ (2 : ℝ)⁻¹ * P := by
    intro α
    apply Lp.norm_le_of_ae_bound hP
    rw [hw α]
    filter_upwards [MemLp.coeFn_toLp (hL2 α), ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hx hxC
    rw [hx]
    exact hb α x hxC
  refine ⟨w, ?_, ?_⟩
  · unfold Represents value
    rw [hw]
    have he : coordinateDerivative (zeroIndex n k) u = u :=
      KPContLocalEnergy.SobolevEnergyEstimates.coordinateDerivative_zeroIndex u
    filter_upwards [MemLp.coeFn_toLp (hL2 (zeroIndex n k))] with x hx
    exact hx.trans (congrFun he x)
  · have hs : w.sobolevNorm ≤ ∑ α : MultiIndex n k, ‖w.derivatives α‖ := by
      apply (Real.sqrt_le_iff).2
      exact ⟨Finset.sum_nonneg (fun _ _ => norm_nonneg _),
        Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)⟩
    have hsum := Finset.sum_le_sum (fun α (_ : α ∈ Finset.univ) => hd α)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    unfold normFactor
    nlinarith

private lemma larger_ball {n : ℕ} (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) :
    ∃ C : LocalBall n, C.center = A.center ∧ A.radius < C.radius ∧
      Metric.closedBall C.center C.radius ⊆ B.carrier := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall A.center A.radius).exists_cthickening_subset_open
    Metric.isOpen_ball hAB
  rw [cthickening_closedBall hδ.le A.radius_pos.le] at hsub
  exact ⟨⟨A.dimension_pos, A.center, δ + A.radius, add_pos hδ A.radius_pos⟩,
    rfl, by dsimp; linarith, hsub⟩

 def lowIndex {n k l : ℕ} (hkl : k ≤ l) (α : MultiIndex n k) : MultiIndex n l :=
  ⟨fun i => ⟨(α.val i).val, by have := (α.val i).isLt; omega⟩, α.property.trans hkl⟩
 def lowSobolev {n k l : ℕ} {B : LocalBall n} (hkl : k ≤ l)
    (u : IntegerSobolev B l) : IntegerSobolev B k where
  derivatives α := u.derivatives (lowIndex hkl α)
  weak_derivatives α := u.weak_derivatives (lowIndex hkl α)
private lemma low_value {n k l : ℕ} {B : LocalBall n} (hkl : k ≤ l)
    (u : IntegerSobolev B l) : value (lowSobolev hkl u) = value u := rfl
private lemma low_norm {n k l : ℕ} {B : LocalBall n} (hkl : k ≤ l)
    (u : IntegerSobolev B l) : (lowSobolev hkl u).sobolevNorm ≤ u.sobolevNorm := by
  classical
  apply Real.sqrt_le_sqrt
  change (∑ α : MultiIndex n k, ‖u.derivatives (lowIndex hkl α)‖ ^ 2) ≤
    ∑ α : MultiIndex n l, ‖u.derivatives α‖ ^ 2
  apply Finset.sum_le_sum_of_injOn (lowIndex hkl)
  · intro α _ β _ hab
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun a : MultiIndex n l => (a.val i).val) hab
  · intro α _; exact Finset.mem_univ _
  · intro α _; exact le_rfl
  · intro α _ _; exact sq_nonneg _

 def family_restrictCoefficients {n : ℕ} {A B : LocalBall n} {cρ Cρ κ Λ : ℝ}
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
private lemma family_restrictCoefficients_smooth {n : ℕ} {A B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (hAB : A.carrier ⊆ B.carrier) (hclosed : Metric.closedBall A.center A.radius ⊆ B.carrier)
    (D : Coefficients B cρ Cρ κ Λ) : SmoothNearClosedBall (family_restrictCoefficients hAB D) := by
  exact ⟨B.carrier, Metric.isOpen_ball, hclosed, D.density_smooth, D.matrix_smooth⟩
private lemma family_weakEquation_restrict {n : ℕ} {A B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (hAB : A.carrier ⊆ B.carrier) (D : Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev B 1) (h : BallL2 B) (hw : WeakEquation D z u h) :
    WeakEquation (family_restrictCoefficients hAB D) z (restrictSobolev hAB u) (restrictBallL2 hAB h) := by
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
      z * (∫ x in A.carrier, (D.density x : ℂ) * value (restrictSobolev hAB u) x * star (φ x)) =
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

private theorem fixed_parameter_forcing_small {n : ℕ} (D : LineChart n)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (R : H →L[ℂ] BallL2 D.outer)
    (O : Set ℂ) (hO : IsOpen O) (a : ℂ → ℂ) (ha : ContinuousOn a O)
    (v : ℂ → H) (hv : ContinuousOn v O)
    (h : ℂ → Space n → ℂ) (hh : KPCutoffSource.ChartSmoothHolomorphicOn D.outer h O)
    (hweak : ∀ z ∈ O, ∃ u : IntegerSobolev D.outer 1,
      KPContLocalEnergy.Represents u (fun x => R (v z) x) ∧
      ∃ g : BallL2 D.outer,
        (h z =ᵐ[volume.restrict D.outer.carrier] (fun x => g x)) ∧
        KPContLocalEnergy.WeakEquation D.coefficients (a z) u g)
    (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) D.outer.carrier ∧
      (f z =ᵐ[volume.restrict D.outer.carrier] (fun x => R (v z) x)))
    (C : LocalBall n) (hCD : Metric.closedBall C.center C.radius ⊆ D.outer.carrier)
    (k : ℕ) (z₀ : ℂ) (hz₀ : z₀ ∈ O) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ O,
      dist z z₀ < δ → ∃ w : IntegerSobolev C k,
        KPContLocalEnergy.Represents w
          (fun x => h z x - h z₀ x + (a z - a z₀) * f z x) ∧
        w.sobolevNorm < η := by
  classical
  have hjcont := forcing_jet_continuity D.outer O h hh
  have hsmooth : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) D.outer.carrier :=
    hh.1
  obtain ⟨B, hBC, hrad, hBD⟩ := larger_ball C D.outer hCD
  have hsub : B.carrier ⊆ D.outer.carrier := Metric.ball_subset_closedBall.trans hBD
  have hCB : C.carrier ⊆ B.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hBC]
    exact Metric.ball_subset_ball hrad.le
  let DB := family_restrictCoefficients hsub D.coefficients
  have hDB : SmoothNearClosedBall DB :=
    family_restrictCoefficients_smooth hsub hBD D.coefficients
  obtain ⟨T, hT, hest, _, _⟩ := kp_cont_local_regularity_iterate_fixed_coefficients n C B
    hBC.symm hrad D.densityLower D.densityUpper D.ellipticityLower D.ellipticityUpper
    (‖a z₀‖ + 1) D.densityLower_pos D.ellipticityLower_pos (by positivity) DB hDB k
  let K := Metric.closedBall B.center B.radius
  have hK : IsCompact K := isCompact_closedBall B.center B.radius
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let j : CompactJets K k := KPLocalCubeSobolevJets.finiteCompactJet D.outer K hBD
    (h z₀) ((hsmooth z₀ hz₀).of_le (by simp))
  let P : ℝ := ‖j‖ + 1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨δh, hδh, hdh⟩ := hjcont z₀ hz₀ K hK hBD k 1 zero_lt_one
  obtain ⟨δa, hδa, hda⟩ := hilbert_difference_small O a ha hz₀ zero_lt_one
  obtain ⟨δv, hδv, hdv⟩ := hilbert_difference_small O v hv hz₀ zero_lt_one
  let δb := min δh (min δa δv)
  have hδb : 0 < δb := lt_min hδh (lt_min hδa hδv)
  let U := T * (‖R‖ * (‖v z₀‖ + 1) + normFactor B k * P) + 1
  have hFactorB := normFactor_pos B k
  have hU : 0 < U := by dsimp [U]; positivity
  have hbound : ∀ z ∈ O, dist z z₀ < δb → ∃ q : IntegerSobolev C k,
      Represents q (f z) ∧ q.sobolevNorm ≤ U := by
    intro z hz hdist
    have hzh := hdist.trans_le (min_le_left _ _)
    have hza := hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hzv := hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have haB : ‖a z‖ ≤ ‖a z₀‖ + 1 := by
      have ht := norm_sub_norm_le (a z) (a z₀)
      have ht' := hda z hz hza
      linarith
    have hvB : ‖v z‖ ≤ ‖v z₀‖ + 1 := by
      have ht := norm_sub_norm_le (v z) (v z₀)
      have ht' := hdv z hz hzv
      linarith
    have hjet : ∀ α : MultiIndex n k, ∀ x ∈ B.carrier,
        ‖coordinateDerivative α (h z) x‖ ≤ P := by
      intro α x hx
      have hxK : x ∈ K := Metric.ball_subset_closedBall hx
      have hsmall := hdh z hz hzh α ⟨x, hxK⟩
      rw [coordinateDerivative, finite_coordinate_derivative_sub D.outer (hsmooth z hz)
        (hsmooth z₀ hz₀) α.directions (hBD hxK), ← coordinateDerivative,
        ← coordinateDerivative] at hsmall
      have hbase : ‖coordinateDerivative α (h z₀) x‖ ≤ ‖j‖ :=
        (ContinuousMap.norm_coe_le_norm (j α) ⟨x, hxK⟩).trans (norm_le_pi_norm j α)
      have ht := norm_sub_norm_le (coordinateDerivative α (h z) x)
        (coordinateDerivative α (h z₀) x)
      dsimp [P]
      linarith
    obtain ⟨g, hg, hgnorm⟩ := smooth_bound D.outer B hBD k (h z) (hsmooth z hz) P hP hjet
    obtain ⟨u, hu, g₀, hg₀, heq⟩ := hweak z hz
    let uB := restrictSobolev hsub u
    have hgval : value g = restrictBallL2 hsub g₀ := by
      apply Lp.ext
      filter_upwards [hg, ae_restrict_of_ae_restrict_of_subset hsub hg₀,
        restrictBallL2_ae hsub g₀] with x hx hy hz'
      exact hx.trans (hy.trans hz'.symm)
    have heqB : WeakEquation DB (a z) uB (value g) := by
      rw [hgval]
      exact family_weakEquation_restrict hsub D.coefficients (a z) u g₀ heq
    obtain ⟨q, hq, hqnorm⟩ := hest (a z) haB uB g heqB
    refine ⟨lowSobolev (Nat.le_add_right k 2) q, ?_, ?_⟩
    · unfold Represents
      rw [low_value]
      filter_upwards [hq, ae_restrict_of_ae_restrict_of_subset hCB
        (restrictSobolev_represents hsub u),
        ae_restrict_of_ae_restrict_of_subset (hCB.trans hsub) hu,
        ae_restrict_of_ae_restrict_of_subset (hCB.trans hsub) (hf z hz).2] with x hx hy ht hf'
      exact hx.trans (hy.trans (ht.trans hf'.symm))
    · have hvalB : ‖value uB‖ ≤ ‖R‖ * (‖v z₀‖ + 1) := by
        have hvu : value u = R (v z) := Lp.ext hu
        change ‖restrictBallL2 hsub (value u)‖ ≤ _
        rw [hvu]
        exact (norm_restrictBallL2_le hsub _).trans
          ((R.le_opNorm _).trans (mul_le_mul_of_nonneg_left hvB (norm_nonneg _)))
      have hn := low_norm (Nat.le_add_right k 2) q
      have hm := mul_le_mul_of_nonneg_left (add_le_add hvalB hgnorm) hT.le
      dsimp [U]
      linarith
  intro η hη
  let ε := η / (8 * normFactor C k)
  have hε : 0 < ε := by dsimp [ε]; exact div_pos hη (mul_pos (by norm_num) (normFactor_pos C k))
  obtain ⟨δs, hδs, hds⟩ := hjcont z₀ hz₀ (Metric.closedBall C.center C.radius)
    (isCompact_closedBall C.center C.radius) hCD k ε hε
  obtain ⟨δc, hδc, hdc⟩ := hilbert_difference_small O a ha hz₀
    (div_pos hη (mul_pos (by norm_num : (8 : ℝ) > 0) hU))
  refine ⟨min δb (min δs δc), lt_min hδb (lt_min hδs hδc), ?_⟩
  intro z hz hdist
  obtain ⟨q, hq, hqnorm⟩ := hbound z hz (hdist.trans_le (min_le_left _ _))
  obtain ⟨g, hg, hgnorm⟩ := smooth_bound D.outer C hCD k
    (fun x => h z x - h z₀ x) ((hsmooth z hz).sub (hsmooth z₀ hz₀)) ε hε.le
    (fun α x hx => (hds z hz
      (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _))) α
        ⟨x, Metric.ball_subset_closedBall hx⟩).le)
  let w := addSobolev g (scaleSobolev (a z - a z₀) q)
  refine ⟨w, addSobolev_represents _ _ _ _ hg
    (scaleSobolev_represents _ q (f z) hq), ?_⟩
  have hw := addSobolev_norm_le g (scaleSobolev (a z - a z₀) q)
  rw [scaleSobolev_norm] at hw
  have hc := hdc z hz (hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hmul := mul_le_mul_of_nonneg_left hqnorm (norm_nonneg (a z - a z₀))
  have hc' : ‖a z - a z₀‖ * U < η / 8 := by
    have hc8 := (lt_div_iff₀ (mul_pos (by norm_num : (8 : ℝ) > 0) hU)).mp hc
    nlinarith
  have heps : normFactor C k * ε = η / 8 := by
    dsimp [ε]
    field_simp [(normFactor_pos C k).ne']
  dsimp [w]
  nlinarith

 def analyticChart {n : ℕ} (A : LocalBall n) {cρ Cρ κ Λ : ℝ}
    (D : Coefficients A cρ Cρ κ Λ) (hcρ : 0 < cρ) (hκ : 0 < κ)
    (hD : SmoothNearClosedBall D) : LineChart n := by
  let B : LocalBall n := ⟨A.dimension_pos, A.center, A.radius / 2,
    div_pos A.radius_pos (by norm_num)⟩
  let η : ContDiffBump A.center :=
    ⟨A.radius / 2, 3 * A.radius / 4, div_pos A.radius_pos (by norm_num),
      by linarith [A.radius_pos]⟩
  exact {
    stabilizer := Unit
    group := inferInstance
    finite := inferInstance
    action := 1
    lineAction := 1
    unitary := by intro g; simp
    inner := B
    outer := A
    concentric := rfl
    radii_lt := by dsimp [B]; linarith [A.radius_pos]
    fixes_center := by intro g; simp
    densityLower := cρ
    densityUpper := Cρ
    ellipticityLower := κ
    ellipticityUpper := Λ
    densityLower_pos := hcρ
    ellipticityLower_pos := hκ
    coefficients := D
    smooth_coefficients := hD
    density_invariant := by intro g x hx; simp
    cutoff := η
    cutoff_smooth := η.contDiff
    cutoff_compact := η.hasCompactSupport
    cutoff_support := by
      rw [η.tsupport_eq]
      exact Metric.closedBall_subset_ball (by change 3 * A.radius / 4 < A.radius; linarith [A.radius_pos])
    cutoff_one := by intro x hx; exact η.one_of_mem_closedBall hx
    cutoff_invariant := by intro g x; simp }

theorem weighted_solution_jet_continuity {n : ℕ} (A : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients A cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (hκ : 0 < κ)
    (hD : KPContLocalRegularity.SmoothNearClosedBall D)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (a : ℂ → ℂ) (ha : ContinuousOn a Ω)
    (v : ℂ → BallL2 A) (hv : ContinuousOn v Ω)
    (h : ℂ → Space n → ℂ)
    (hh : KPCutoffSource.ChartSmoothHolomorphicOn A h Ω)
    (hhS : ∀ B : LocalBall n, KPContLocalCubeEmbedding.closedCarrier B ⊆ A.carrier →
      KPCutoffSource.ChartSobolevHolomorphicOn B h Ω)
    (hweak : ∀ s ∈ Ω, ∃ w : IntegerSobolev A 1,
      value w = v s ∧ ∃ g : BallL2 A,
        (h s =ᵐ[volume.restrict A.carrier] (fun p => g p)) ∧
          WeakEquation D (a s) w g)
    (f : ℂ → Space n → ℂ)
    (hf : ∀ s ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (f s) A.carrier ∧
      (f s =ᵐ[volume.restrict A.carrier] (fun p => v s p))) :
    KPContLocalHolomorphyUpgrade.CauchyAssembly.Raw.JetContinuousOn A f Ω := by
  classical
  let D' := analyticChart A D hcρ hκ hD
  let R : BallL2 A →L[ℂ] BallL2 A := ContinuousLinearMap.id ℂ (BallL2 A)
  have hweak' : ∀ z ∈ Ω, ∃ w : IntegerSobolev A 1,
      Represents w (fun p => R (v z) p) ∧ ∃ g : BallL2 A,
        (h z =ᵐ[volume.restrict A.carrier] (fun p => g p)) ∧
          WeakEquation D (a z) w g := by
    intro z hz
    obtain ⟨w, hw, g, hg, heq⟩ := hweak z hz
    refine ⟨w, ?_, g, hg, heq⟩
    exact Filter.Eventually.of_forall (fun p => congrArg (fun q : BallL2 A => q p) hw)
  intro z₀ hz₀ K hK hKD m ε hε
  obtain ⟨C, hCD, T, hT, hest⟩ :=
    KPContSmoothPromotion.LocalSolutionEstimates.LocalFamily.chart_solution_difference_jet_estimate D' K hK hKD m (a z₀)
  have hη : 0 < ε / (2 * T) := div_pos hε (by positivity)
  obtain ⟨δ₁, hδ₁, hsmall⟩ :=
    fixed_parameter_forcing_small D' R Ω hΩ a ha
      v hv h hh hweak' f hf
      C hCD (m + n) z₀ hz₀ (ε / (2 * T)) hη
  obtain ⟨δ₂, hδ₂, hRsmall⟩ :=
    KPContLocalHolomorphyUpgrade.CauchyAssembly.hilbert_difference_small Ω
      (fun z => R (v z)) (R.continuous.comp_continuousOn hv) hz₀ hη
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro z hz hdist α x
  obtain ⟨w, hw, hwn⟩ := hsmall z hz (hdist.trans_le (min_le_left _ _))
  obtain ⟨u₁, hu₁, g₁, hg₁, heq₁⟩ := hweak' z hz
  obtain ⟨u₀, hu₀, g₀, hg₀, heq₀⟩ := hweak' z₀ hz₀
  have hu₁f : KPContLocalEnergy.Represents u₁ (f z) :=
    Filter.EventuallyEq.trans hu₁ (hf z hz).2.symm
  have hu₀f : KPContLocalEnergy.Represents u₀ (f z₀) :=
    Filter.EventuallyEq.trans hu₀ (hf z₀ hz₀).2.symm
  have hCB : C.carrier ⊆ D'.outer.carrier := Metric.ball_subset_closedBall.trans hCD
  have hgw : KPContLocalEnergy.Represents w
      (fun y => g₁ y - g₀ y + (a z - a z₀) * f z y) := by
    have hg₁C := ae_restrict_of_ae_restrict_of_subset hCB hg₁
    have hg₀C := ae_restrict_of_ae_restrict_of_subset hCB hg₀
    filter_upwards [hw, hg₁C, hg₀C] with y hwy h₁y h₀y
    simpa only [h₁y, h₀y] using hwy
  have hv₁ : KPContLocalEnergy.value u₁ = R (v z) := Lp.ext hu₁
  have hv₀ : KPContLocalEnergy.value u₀ = R (v z₀) := Lp.ext hu₀
  have hRn := hRsmall z hz (hdist.trans_le (min_le_right _ _))
  have hsum : ‖KPContLocalEnergy.value u₁ - KPContLocalEnergy.value u₀‖ +
      w.sobolevNorm < ε / T := by
    rw [hv₁, hv₀]
    have heq : ε / (2 * T) + ε / (2 * T) = ε / T := by ring
    rw [← heq]
    exact add_lt_add hRn hwn
  exact (hest (a z) u₁ u₀ g₁ g₀ (f z) (f z₀) heq₁ heq₀
    (hf z hz).1 (hf z₀ hz₀).1 hu₁f hu₀f w hgw α x).trans_lt
    (by
      have hm : T * (‖value u₁ - value u₀‖ + w.sobolevNorm) < ε := by
        calc
          _ < T * (ε / T) := mul_lt_mul_of_pos_left hsum hT
          _ = ε := mul_div_cancel₀ ε hT.ne'
      exact hm)

end DedekindZetaZeroFree.KPContActualLocalSolutionFamily.CoefficientRestriction

end
