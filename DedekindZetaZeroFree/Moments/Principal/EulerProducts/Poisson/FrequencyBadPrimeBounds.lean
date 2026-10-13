module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.BadPrimeBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawEulerBad31

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain

variable {F : Type} [Field F] [NumberField F]

section Generic

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private lemma Q_pos' (p : LocalFiniteSums.ExteriorPrime A) :
    0 < LocalFiniteSums.Q p := A.exteriorNorm_pos (LocalFiniteSums.primeIdeal p)

private abbrev tm (C : A.GeneralArithmeticContext σ η hS) (pr : LocalFiniteSums.ExteriorPrime A)
    (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1}) (p : Coordinates) (i : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  LocalFiniteSums.seriesTerm C pr j θ i.1 i.2.1 i.2.2.1 i.2.2.2 p.1 p.2.1 p.2.2

theorem badFactor_eq (C : A.GeneralArithmeticContext σ η hS) (pr : LocalFiniteSums.ExteriorPrime A)
    (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1}) (ξ w z : ℂ) :
    CorrectionFactors.badFactor C pr j θ ξ w z =
      (1 - CorrectionFactors.V pr z) * LocalFiniteSums.f C pr j θ ξ w z := rfl

private lemma norm_le_of_norm_one_sub_mul (V t : ℂ) (ρ w : ℝ) (hV : ‖V‖ ≤ ρ) (hρ : ρ < 1)
    (h : ‖(1 - V) * t‖ ≤ 2 * w) : ‖t‖ ≤ 2 / (1 - ρ) * w := by
  have hpos : 0 < 1 - ρ := by linarith
  have h1 : 1 - ρ ≤ ‖1 - V‖ := by
    have := norm_sub_norm_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  rw [norm_mul] at h
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (norm_nonneg t)]

open Filter Set Metric in
private theorem normal_holomorphic {ι : Type*} (g : ι → Coordinates → ℂ)
    (hg : ∀ i, Differentiable ℂ (g i)) (U : Set Coordinates) (hU : IsOpen U)
    (hM : ∀ K : Set Coordinates, K ⊆ U → IsCompact K →
      ∃ M : ι → ℝ, Summable M ∧ ∀ i x, x ∈ K → ‖g i x‖ ≤ M i) :
    DifferentiableOn ℂ (fun x => ∑' i, g i x) U := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨M, hMs, hMb⟩ := hM (closedBall x r) hsub (isCompact_closedBall x r)
  have hhalf : 0 < r / 2 := by positivity
  have hinside {y : Coordinates} (hy : y ∈ Metric.ball x (r / 2)) : y ∈ closedBall x r := by
    exact ball_subset_closedBall (ball_subset_ball (by linarith) hy)
  have hderiv : ∀ i y, y ∈ Metric.ball x (r / 2) → ‖fderiv ℂ (g i) y‖ ≤ (4 / r) * M i := by
    intro i y hy
    have hball : Metric.ball y (r / 2) ⊆ closedBall x r := by
      intro z hz
      apply mem_closedBall.mpr
      have := dist_triangle z y x
      have hz' := mem_ball.mp hz
      have hy' := mem_ball.mp hy
      linarith
    have hnorm := Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((hg i).differentiableOn : DifferentiableOn ℂ (g i) (Metric.ball y (r / 2)))
      (R₂ := 2 * M i) (by
        intro z hz
        apply mem_closedBall.mpr
        calc
          dist (g i z) (g i y) ≤ ‖g i z‖ + ‖g i y‖ := by
            simpa only [dist_eq_norm_sub] using norm_sub_le (g i z) (g i y)
          _ ≤ 2 * M i := by linarith [hMb i z (hball hz), hMb i y (hinside hy)]) hhalf
    convert hnorm using 1 <;> field_simp <;> ring
  have hs := hasFDerivAt_tsum_of_isPreconnected (hMs.mul_left (4 / r)) isOpen_ball
    (convex_ball x (r / 2)).isPreconnected
    (fun i y _ => (hg i y).hasFDerivAt) hderiv
    (mem_ball_self hhalf)
    (Summable.of_norm_bounded hMs (fun i => hMb i x (mem_closedBall_self hr.le)))
    (mem_ball_self hhalf)
  exact hs.differentiableAt.differentiableWithinAt

private theorem margin_data (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ δ₀ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < δ₀ ∧
      ∀ (C : A.GeneralArithmeticContext σ η hS) (pr : LocalFiniteSums.ExteriorPrime A)
        (j : Fin 6), j.val ≠ 0 → ∀ (θ : {θ : ℂ // ‖θ‖ = 1}), ∀ p ∈ OmegaStarMargin δ,
        ∀ i : Fin 2 × ℕ × ℕ × ℕ,
          ‖CorrectionFactors.V pr p.2.2‖ ≤ ρ ∧
          ‖(1 - CorrectionFactors.V pr p.2.2) * tm C pr j θ p i‖ ≤
            2 * BadPrimeShellSeries.weight ρ i ∧
          (0 < i.1.val + 3 * i.2.1 →
            ‖tm C pr j θ p i‖ ≤ LocalFiniteSums.Q pr ^ (-δ₀) * BadPrimeShellSeries.weight ρ i) := by
  obtain ⟨ρ, δ₀, hρ0, hρ1, hδ₀, -, h⟩ :=
    BadPrimeShellSeries.seriesTerm_majorant_margin (A := A) (σ := σ)
      (η := η) (hS := hS) δ hδ
  exact ⟨ρ, δ₀, hρ0, hρ1, hδ₀, fun C pr j hj θ p hp i => h C pr j hj θ p hp i⟩

private theorem sub_one_le_aux (C : A.GeneralArithmeticContext σ η hS)
    (pr : LocalFiniteSums.ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (p : Coordinates) (ρ q : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hq : 0 ≤ q)
    (hV : ‖CorrectionFactors.V pr p.2.2‖ ≤ ρ)
    (h2 : ∀ i : Fin 2 × ℕ × ℕ × ℕ,
      ‖(1 - CorrectionFactors.V pr p.2.2) * tm C pr j θ p i‖ ≤ 2 * BadPrimeShellSeries.weight ρ i)
    (h3 : ∀ i : Fin 2 × ℕ × ℕ × ℕ, 0 < i.1.val + 3 * i.2.1 →
      ‖tm C pr j θ p i‖ ≤ q * BadPrimeShellSeries.weight ρ i) :
    ‖CorrectionFactors.badFactor C pr j θ p.1 p.2.1 p.2.2 - 1‖ ≤
      2 * (∑' i, BadPrimeShellSeries.weight ρ i) * q := by
  have hws := BadPrimeShellSeries.weight_summable hρ0 hρ1
  have hts : Summable (tm C pr j θ p) :=
    Summable.of_norm_bounded (hws.mul_left (2 / (1 - ρ)))
      (fun i => norm_le_of_norm_one_sub_mul _ _ ρ _ hV hρ1 (h2 i))
  have hb : Summable (BadPrimeShellSeries.baseline pr p.2.2) :=
    Summable.of_norm_bounded hws (BadPrimeShellSeries.baseline_norm_le pr p.2.2 ρ hρ0 hV)
  have hV1 : ‖CorrectionFactors.V pr p.2.2‖ < 1 := lt_of_le_of_lt hV hρ1
  have hcancel := BadPrimeShellSeries.one_sub_V_mul_tsum_baseline pr p.2.2 hV1
  have hr : ∀ i : Fin 2 × ℕ × ℕ × ℕ,
      ‖tm C pr j θ p i - BadPrimeShellSeries.baseline pr p.2.2 i‖ ≤
        q * BadPrimeShellSeries.weight ρ i := by
    intro i
    by_cases hpos : 0 < i.1.val + 3 * i.2.1
    · have hb0 : BadPrimeShellSeries.baseline pr p.2.2 i = 0 := by
        unfold BadPrimeShellSeries.baseline
        rw [if_neg]
        rintro ⟨he, hl, -⟩
        simp [he, hl] at hpos
      rw [hb0, sub_zero]
      exact h3 i hpos
    · obtain ⟨e, l, k, m⟩ := i
      have hpos' : ¬ 0 < e.val + 3 * l := hpos
      have he : e = 0 := Fin.ext (by simp; omega)
      have hl : l = 0 := by omega
      subst he hl
      have hterm : tm C pr j θ p (0, 0, k, m) =
          if k = 0 then CorrectionFactors.V pr p.2.2 ^ m else 0 :=
        BadPrimeShellSeries.seriesTerm_leading C pr j hj θ k m p.1 p.2.1 p.2.2
      have hbase : BadPrimeShellSeries.baseline pr p.2.2 (0, 0, k, m) =
          if k = 0 then CorrectionFactors.V pr p.2.2 ^ m else 0 := by
        simp [BadPrimeShellSeries.baseline]
      rw [hterm, hbase, sub_self, norm_zero]
      exact mul_nonneg hq (BadPrimeShellSeries.weight_nonneg hρ0 _)
  have hrs := tsum_of_norm_bounded (hws.hasSum.mul_left q) hr
  have hid : CorrectionFactors.badFactor C pr j θ p.1 p.2.1 p.2.2 - 1 =
      (1 - CorrectionFactors.V pr p.2.2) *
        ∑' i, (tm C pr j θ p i - BadPrimeShellSeries.baseline pr p.2.2 i) := by
    rw [hts.tsum_sub hb, mul_sub, hcancel] <;> rfl
  have hV2 : ‖1 - CorrectionFactors.V pr p.2.2‖ ≤ 2 := by
    calc ‖1 - CorrectionFactors.V pr p.2.2‖
        ≤ ‖(1 : ℂ)‖ + ‖CorrectionFactors.V pr p.2.2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        simp only [norm_one]
        linarith
  rw [hid, norm_mul]
  calc ‖1 - CorrectionFactors.V pr p.2.2‖ *
        ‖∑' i, (tm C pr j θ p i - BadPrimeShellSeries.baseline pr p.2.2 i)‖
      ≤ 2 * (q * ∑' i, BadPrimeShellSeries.weight ρ i) :=
        mul_le_mul hV2 hrs (norm_nonneg _) (by norm_num)
    _ = 2 * (∑' i, BadPrimeShellSeries.weight ρ i) * q := by ring

theorem badFactor_differentiableOn (C : A.GeneralArithmeticContext σ η hS)
    (pr : LocalFiniteSums.ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) :
    DifferentiableOn ℂ
      (fun p : Coordinates => CorrectionFactors.badFactor C pr j θ p.1 p.2.1 p.2.2)
      OmegaStar := by
  have hg : ∀ i : Fin 2 × ℕ × ℕ × ℕ, Differentiable ℂ
      (fun x : Coordinates => (1 - CorrectionFactors.V pr x.2.2) * tm C pr j θ x i) := by
    intro i
    unfold CorrectionFactors.V tm LocalFiniteSums.seriesTerm LocalFiniteSums.qPower
    fun_prop
  have h := normal_holomorphic _ hg OmegaStar EulerGeometry.OmegaStar_isOpen (by
    intro K hKO hK
    obtain ⟨δ, hδ, hKδ⟩ := EulerBadPrime.exists_margin_of_compact K hK hKO
    obtain ⟨ρ, δ₀, hρ0, hρ1, hδ₀, hmaj⟩ := margin_data (A := A) (σ := σ) (η := η) (hS := hS) δ hδ
    refine ⟨fun i => 2 * BadPrimeShellSeries.weight ρ i,
      (BadPrimeShellSeries.weight_summable hρ0.le hρ1).mul_left 2, ?_⟩
    intro i x hx
    exact (hmaj C pr j hj θ x (hKδ hx) i).2.1)
  refine h.congr ?_
  intro x _
  simp only [CorrectionFactors.badFactor, LocalFiniteSums.f, tsum_mul_left]

theorem series_hasSumLocallyUniformlyOn (C : A.GeneralArithmeticContext σ η hS)
    (pr : LocalFiniteSums.ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) :
    HasSumLocallyUniformlyOn
      (fun (i : Fin 2 × ℕ × ℕ × ℕ) (p : Coordinates) =>
        LocalFiniteSums.seriesTerm C pr j θ i.1 i.2.1 i.2.2.1 i.2.2.2 p.1 p.2.1 p.2.2)
      (fun p : Coordinates => LocalFiniteSums.f C pr j θ p.1 p.2.1 p.2.2)
      OmegaStar := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact EulerGeometry.OmegaStar_isOpen]
  intro K hKO hK
  obtain ⟨δ, hδ, hKδ⟩ := EulerBadPrime.exists_margin_of_compact K hK hKO
  obtain ⟨ρ, δ₀, hρ0, hρ1, hδ₀, hmaj⟩ := margin_data (A := A) (σ := σ) (η := η) (hS := hS) δ hδ
  have hu : Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      2 / (1 - ρ) * BadPrimeShellSeries.weight ρ i) :=
    (BadPrimeShellSeries.weight_summable hρ0.le hρ1).mul_left _
  have h := HasSumUniformlyOn.of_norm_le_summable
    (f := fun (i : Fin 2 × ℕ × ℕ × ℕ) (p : Coordinates) => tm C pr j θ p i) hu (by
      intro i x hx
      obtain ⟨hV, h2, -⟩ := hmaj C pr j hj θ x (hKδ hx) i
      exact norm_le_of_norm_one_sub_mul _ _ ρ _ hV hρ1 h2)
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn] at h
  exact h

theorem badFactor_sub_one_le (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ Cc δ : ℝ, 0 < Cc ∧ 0 < δ ∧
      ∀ (C : A.GeneralArithmeticContext σ η hS) (pr : LocalFiniteSums.ExteriorPrime A)
        (j : Fin 6), j.val ≠ 0 → ∀ (θ : {θ : ℂ // ‖θ‖ = 1}), ∀ p ∈ OmegaStarMargin δ',
          ‖CorrectionFactors.badFactor C pr j θ p.1 p.2.1 p.2.2 - 1‖ ≤
            Cc * LocalFiniteSums.Q pr ^ (-δ) := by
  obtain ⟨ρ, δ₀, hρ0, hρ1, hδ₀, hmaj⟩ :=
    margin_data (A := A) (σ := σ) (η := η) (hS := hS) δ' hδ'
  have hS0 : 0 ≤ ∑' i, BadPrimeShellSeries.weight ρ i :=
    tsum_nonneg (BadPrimeShellSeries.weight_nonneg hρ0.le)
  refine ⟨2 * (∑' i, BadPrimeShellSeries.weight ρ i) + 1, δ₀, by linarith, hδ₀, ?_⟩
  intro C pr j hj θ p hp
  have hQ : 0 ≤ LocalFiniteSums.Q pr ^ (-δ₀) :=
    Real.rpow_nonneg (Q_pos' pr).le _
  have h := sub_one_le_aux C pr j hj θ p ρ _ hρ0.le hρ1 hQ
    (hmaj C pr j hj θ p hp (0, 0, 0, 0)).1
    (fun i => (hmaj C pr j hj θ p hp i).2.1) (fun i hi => (hmaj C pr j hj θ p hp i).2.2 hi)
  refine h.trans ?_
  nlinarith [mul_nonneg hS0 hQ]

theorem badFactor_sub_one_le_paddedBoxes :
    ∃ Cc : ℝ, 0 < Cc ∧
      ∀ (C : A.GeneralArithmeticContext σ η hS) (pr : LocalFiniteSums.ExteriorPrime A)
        (j : Fin 6), j.val ≠ 0 → ∀ (θ : {θ : ℂ // ‖θ‖ = 1}), ∀ p ∈ paddedBoxes,
          ‖CorrectionFactors.badFactor C pr j θ p.1 p.2.1 p.2.2 - 1‖ ≤
            Cc * LocalFiniteSums.Q pr ^ (-(1 / 20000 : ℝ)) := by
  have hmaj := BadPrimeShellSeries.seriesTerm_majorant_paddedBoxes (A := A)
    (σ := σ) (η := η) (hS := hS)
  have hρ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 8 : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hρ1 : (2 : ℝ) ^ (-(1 / 8 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hS0 : 0 ≤ ∑' i, BadPrimeShellSeries.weight ((2 : ℝ) ^ (-(1 / 8 : ℝ))) i :=
    tsum_nonneg (BadPrimeShellSeries.weight_nonneg hρ0)
  refine ⟨2 * (∑' i, BadPrimeShellSeries.weight ((2 : ℝ) ^ (-(1 / 8 : ℝ))) i) + 1,
    by linarith, ?_⟩
  intro C pr j hj θ p hp
  have hQ : 0 ≤ LocalFiniteSums.Q pr ^ (-(1 / 20000 : ℝ)) :=
    Real.rpow_nonneg (Q_pos' pr).le _
  have h := sub_one_le_aux C pr j hj θ p _ _ hρ0 hρ1 hQ
    (hmaj C pr j hj θ p hp (0, 0, 0, 0)).1
    (fun i => (hmaj C pr j hj θ p hp i).2.1)
    (fun i hi => (hmaj C pr j hj θ p hp i).2.2 hi)
  refine h.trans ?_
  nlinarith [mul_nonneg hS0 hQ]

end Generic

section Raw

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

open AllRowEuler.InitialSeparation

theorem theta_norm (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) :
    ‖(U.theta D.context pr).val‖ = 1 := (U.theta D.context pr).property

theorem localCorrection_bad_eq (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val ≠ 0) (ξ w z : ℂ) :
    AllRowEuler.InitialSeparation.localCorrection D.context U pr ξ w z =
      CorrectionFactors.badFactor D.context pr (U.j pr) (U.theta D.context pr) ξ w z := by
  unfold AllRowEuler.InitialSeparation.localCorrection
  rw [if_neg hj]

theorem localCorrection_bad_eq_mul (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val ≠ 0) (ξ w z : ℂ) :
    AllRowEuler.InitialSeparation.localCorrection D.context U pr ξ w z =
      (1 - CorrectionFactors.V pr z) *
        LocalFiniteSums.f D.context pr (U.j pr) (U.theta D.context pr) ξ w z := by
  rw [localCorrection_bad_eq D U pr hj]
  rfl

theorem localSeries_hasSumLocallyUniformlyOn (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val ≠ 0) :
    HasSumLocallyUniformlyOn
      (fun (i : Fin 2 × ℕ × ℕ × ℕ) (p : Coordinates) =>
        LocalFiniteSums.seriesTerm D.context pr (U.j pr) (U.theta D.context pr)
          i.1 i.2.1 i.2.2.1 i.2.2.2 p.1 p.2.1 p.2.2)
      (fun p : Coordinates =>
        LocalFiniteSums.f D.context pr (U.j pr) (U.theta D.context pr) p.1 p.2.1 p.2.2)
      OmegaStar :=
  series_hasSumLocallyUniformlyOn D.context pr (U.j pr) hj (U.theta D.context pr)

theorem localCorrection_bad_differentiableOn (U : RawFrequency D.recipe.A)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (U.j pr).val ≠ 0) :
    DifferentiableOn ℂ
      (fun p : Coordinates =>
        AllRowEuler.InitialSeparation.localCorrection D.context U pr p.1 p.2.1 p.2.2)
      OmegaStar := by
  refine (badFactor_differentiableOn D.context pr (U.j pr) hj (U.theta D.context pr)).congr ?_
  intro p _
  exact localCorrection_bad_eq D U pr hj _ _ _

theorem localCorrection_bad_sub_one_le (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (U : RawFrequency D.recipe.A) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (U.j pr).val ≠ 0 → ∀ p ∈ OmegaStarMargin δ',
          ‖AllRowEuler.InitialSeparation.localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-δ) := by
  obtain ⟨C, δ, hC, hδ, h⟩ := badFactor_sub_one_le (A := D.recipe.A) (σ := D.recipe.σ)
    (η := D.recipe.target) (hS := D.recipe.traceBad) δ' hδ'
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro U pr hj p hp
  rw [localCorrection_bad_eq D U pr hj]
  exact h D.context pr (U.j pr) hj (U.theta D.context pr) p hp

theorem localCorrection_bad_sub_one_le_paddedBoxes :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : RawFrequency D.recipe.A) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (U.j pr).val ≠ 0 → ∀ p ∈ paddedBoxes,
          ‖AllRowEuler.InitialSeparation.localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-(1 / 20000 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := badFactor_sub_one_le_paddedBoxes (A := D.recipe.A) (σ := D.recipe.σ)
    (η := D.recipe.target) (hS := D.recipe.traceBad)
  refine ⟨C, hC, ?_⟩
  intro U pr hj p hp
  rw [localCorrection_bad_eq D U pr hj]
  exact h D.context pr (U.j pr) hj (U.theta D.context pr) p hp

end Raw

end

end DedekindZetaZeroFree.Quantitative.RawEulerBad31
