module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.BadPrimeShellSeries
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.DomainGeometry

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.EulerBadPrime

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private def slack (p : Coordinates) : ℝ :=
  min p.1.re (min p.2.1.re (min p.2.2.re (min (6 * p.2.2.re + p.2.1.re - 1)
    (min (p.1.re + 6 * p.2.2.re - 1) (min (p.1.re + p.2.1.re - 1)
    (min (p.1.re + p.2.1.re + 6 * p.2.2.re - 2) (min (6 * p.1.re + 6 * p.2.2.re - 5)
    (min (p.1.re - 1 / 2) (min (3 * p.1.re - 2) (3 * p.1.re + p.2.1.re - 5 / 2))))))))))

private lemma le_slack_iff (δ : ℝ) (p : Coordinates) :
    δ ≤ slack p ↔ (δ ≤ p.1.re ∧ δ ≤ p.2.1.re ∧ δ ≤ p.2.2.re ∧
      δ ≤ 6 * p.2.2.re + p.2.1.re - 1 ∧ δ ≤ p.1.re + 6 * p.2.2.re - 1 ∧
      δ ≤ p.1.re + p.2.1.re - 1 ∧ δ ≤ p.1.re + p.2.1.re + 6 * p.2.2.re - 2 ∧
      δ ≤ 6 * p.1.re + 6 * p.2.2.re - 5 ∧ δ ≤ p.1.re - 1 / 2 ∧ δ ≤ 3 * p.1.re - 2 ∧
      δ ≤ 3 * p.1.re + p.2.1.re - 5 / 2) := by
  simp only [slack, le_min_iff]

private lemma slack_continuous : Continuous slack := by
  unfold slack
  first | fun_prop | continuity

theorem exists_margin_of_compact (K : Set Coordinates) (hK : IsCompact K)
    (hKO : K ⊆ OmegaStar) : ∃ δ : ℝ, 0 < δ ∧ K ⊆ OmegaStarMargin δ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, Set.empty_subset _⟩
  obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn hne slack_continuous.continuousOn
  have hpos : 0 < slack x := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hKO hxK
    simp only [slack, lt_min_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  refine ⟨slack x, hpos, ?_⟩
  intro p hp
  have hle : slack x ≤ slack p := isMinOn_iff.mp hx p hp
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := (le_slack_iff _ _).mp hle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private lemma Q_pos' {A : SArithmeticData F} (p : LocalFiniteSums.ExteriorPrime A) :
    0 < LocalFiniteSums.Q p := A.exteriorNorm_pos (LocalFiniteSums.primeIdeal p)

private abbrev tm (u : D.Row) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (p : Coordinates)
    (i : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  LocalFiniteSums.seriesTerm D.context pr (u.toFrequency.j pr) (u.toFrequency.theta pr)
    i.1 i.2.1 i.2.2.1 i.2.2.2 p.1 p.2.1 p.2.2

theorem localFactor_eq (u : D.Row) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A)
    (hj : (u.toFrequency.j pr).val ≠ 0) (ξ w z : ℂ) :
    CorrectionFactors.localFactor D.context u pr ξ w z =
      (1 - CorrectionFactors.V pr z) *
        LocalFiniteSums.f D.context pr (u.toFrequency.j pr) (u.toFrequency.theta pr) ξ w z := by
  rw [CorrectionFactors.localFactor, if_neg hj, CorrectionFactors.badFactor] <;> rfl

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
      ∀ (u : D.Row) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (u.toFrequency.j pr).val ≠ 0 → ∀ p ∈ OmegaStarMargin δ,
        ∀ i : Fin 2 × ℕ × ℕ × ℕ,
          ‖CorrectionFactors.V pr p.2.2‖ ≤ ρ ∧
          ‖(1 - CorrectionFactors.V pr p.2.2) * tm D u pr p i‖ ≤
            2 * BadPrimeShellSeries.weight ρ i ∧
          (0 < i.1.val + 3 * i.2.1 →
            ‖tm D u pr p i‖ ≤ LocalFiniteSums.Q pr ^ (-δ₀) * BadPrimeShellSeries.weight ρ i) := by
  obtain ⟨ρ, δ₀, hρ0, hρ1, hδ₀, -, h⟩ :=
    BadPrimeShellSeries.seriesTerm_majorant_margin (A := D.recipe.A) (σ := D.recipe.σ)
      (η := D.recipe.target) (hS := D.recipe.traceBad) δ hδ
  exact ⟨ρ, δ₀, hρ0, hρ1, hδ₀, fun u pr hj p hp i =>
    h D.context pr (u.toFrequency.j pr) hj (u.toFrequency.theta pr) p hp i⟩

private theorem sub_one_le_aux (u : D.Row) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A)
    (hj : (u.toFrequency.j pr).val ≠ 0) (p : Coordinates) (ρ q : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hq : 0 ≤ q)
    (hV : ‖CorrectionFactors.V pr p.2.2‖ ≤ ρ)
    (h2 : ∀ i : Fin 2 × ℕ × ℕ × ℕ,
      ‖(1 - CorrectionFactors.V pr p.2.2) * tm D u pr p i‖ ≤ 2 * BadPrimeShellSeries.weight ρ i)
    (h3 : ∀ i : Fin 2 × ℕ × ℕ × ℕ, 0 < i.1.val + 3 * i.2.1 →
      ‖tm D u pr p i‖ ≤ q * BadPrimeShellSeries.weight ρ i) :
    ‖CorrectionFactors.localFactor D.context u pr p.1 p.2.1 p.2.2 - 1‖ ≤
      2 * (∑' i, BadPrimeShellSeries.weight ρ i) * q := by
  have hws := BadPrimeShellSeries.weight_summable hρ0 hρ1
  have hts : Summable (tm D u pr p) :=
    Summable.of_norm_bounded (hws.mul_left (2 / (1 - ρ)))
      (fun i => norm_le_of_norm_one_sub_mul _ _ ρ _ hV hρ1 (h2 i))
  have hb : Summable (BadPrimeShellSeries.baseline pr p.2.2) :=
    Summable.of_norm_bounded hws (BadPrimeShellSeries.baseline_norm_le pr p.2.2 ρ hρ0 hV)
  have hV1 : ‖CorrectionFactors.V pr p.2.2‖ < 1 := lt_of_le_of_lt hV hρ1
  have hcancel := BadPrimeShellSeries.one_sub_V_mul_tsum_baseline pr p.2.2 hV1
  have hr : ∀ i : Fin 2 × ℕ × ℕ × ℕ,
      ‖tm D u pr p i - BadPrimeShellSeries.baseline pr p.2.2 i‖ ≤
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
      have hterm : tm D u pr p (0, 0, k, m) =
          if k = 0 then CorrectionFactors.V pr p.2.2 ^ m else 0 :=
        BadPrimeShellSeries.seriesTerm_leading D.context pr (u.toFrequency.j pr) hj
          (u.toFrequency.theta pr) k m p.1 p.2.1 p.2.2
      have hbase : BadPrimeShellSeries.baseline pr p.2.2 (0, 0, k, m) =
          if k = 0 then CorrectionFactors.V pr p.2.2 ^ m else 0 := by
        simp [BadPrimeShellSeries.baseline]
      rw [hterm, hbase, sub_self, norm_zero]
      exact mul_nonneg hq (BadPrimeShellSeries.weight_nonneg hρ0 _)
  have hrs := tsum_of_norm_bounded (hws.hasSum.mul_left q) hr
  have hid : CorrectionFactors.localFactor D.context u pr p.1 p.2.1 p.2.2 - 1 =
      (1 - CorrectionFactors.V pr p.2.2) *
        ∑' i, (tm D u pr p i - BadPrimeShellSeries.baseline pr p.2.2 i) := by
    rw [hts.tsum_sub hb, mul_sub, hcancel, localFactor_eq D u pr hj] <;> rfl
  have hV2 : ‖1 - CorrectionFactors.V pr p.2.2‖ ≤ 2 := by
    calc ‖1 - CorrectionFactors.V pr p.2.2‖
        ≤ ‖(1 : ℂ)‖ + ‖CorrectionFactors.V pr p.2.2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        simp only [norm_one]
        linarith
  rw [hid, norm_mul]
  calc ‖1 - CorrectionFactors.V pr p.2.2‖ *
        ‖∑' i, (tm D u pr p i - BadPrimeShellSeries.baseline pr p.2.2 i)‖
      ≤ 2 * (q * ∑' i, BadPrimeShellSeries.weight ρ i) :=
        mul_le_mul hV2 hrs (norm_nonneg _) (by norm_num)
    _ = 2 * (∑' i, BadPrimeShellSeries.weight ρ i) * q := by ring

theorem localFactor_differentiableOn (u : D.Row)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (u.toFrequency.j pr).val ≠ 0) :
    DifferentiableOn ℂ
      (fun p : Coordinates => CorrectionFactors.localFactor D.context u pr p.1 p.2.1 p.2.2)
      OmegaStar := by
  have hg : ∀ i : Fin 2 × ℕ × ℕ × ℕ, Differentiable ℂ
      (fun x : Coordinates => (1 - CorrectionFactors.V pr x.2.2) * tm D u pr x i) := by
    intro i
    unfold CorrectionFactors.V tm LocalFiniteSums.seriesTerm LocalFiniteSums.qPower
    fun_prop
  have h := normal_holomorphic _ hg OmegaStar EulerGeometry.OmegaStar_isOpen (by
    intro K hKO hK
    obtain ⟨δ, hδ, hKδ⟩ := exists_margin_of_compact K hK hKO
    obtain ⟨ρ, δ₀, hρ0, hρ1, hδ₀, hmaj⟩ := margin_data D δ hδ
    refine ⟨fun i => 2 * BadPrimeShellSeries.weight ρ i,
      (BadPrimeShellSeries.weight_summable hρ0.le hρ1).mul_left 2, ?_⟩
    intro i x hx
    exact (hmaj u pr hj x (hKδ hx) i).2.1)
  refine h.congr ?_
  intro x _
  rw [localFactor_eq D u pr hj]
  simp only [LocalFiniteSums.f, tsum_mul_left]

theorem localSeries_hasSumLocallyUniformlyOn (u : D.Row)
    (pr : LocalFiniteSums.ExteriorPrime D.recipe.A) (hj : (u.toFrequency.j pr).val ≠ 0) :
    HasSumLocallyUniformlyOn
      (fun (i : Fin 2 × ℕ × ℕ × ℕ) (p : Coordinates) =>
        LocalFiniteSums.seriesTerm D.context pr (u.toFrequency.j pr) (u.toFrequency.theta pr)
          i.1 i.2.1 i.2.2.1 i.2.2.2 p.1 p.2.1 p.2.2)
      (fun p : Coordinates =>
        LocalFiniteSums.f D.context pr (u.toFrequency.j pr) (u.toFrequency.theta pr) p.1 p.2.1 p.2.2)
      OmegaStar := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact EulerGeometry.OmegaStar_isOpen]
  intro K hKO hK
  obtain ⟨δ, hδ, hKδ⟩ := exists_margin_of_compact K hK hKO
  obtain ⟨ρ, δ₀, hρ0, hρ1, hδ₀, hmaj⟩ := margin_data D δ hδ
  have hu : Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      2 / (1 - ρ) * BadPrimeShellSeries.weight ρ i) :=
    (BadPrimeShellSeries.weight_summable hρ0.le hρ1).mul_left _
  have h := HasSumUniformlyOn.of_norm_le_summable
    (f := fun (i : Fin 2 × ℕ × ℕ × ℕ) (p : Coordinates) => tm D u pr p i) hu (by
      intro i x hx
      obtain ⟨hV, h2, -⟩ := hmaj u pr hj x (hKδ hx) i
      exact norm_le_of_norm_one_sub_mul _ _ ρ _ hV hρ1 h2)
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn] at h
  exact h

theorem localFactor_sub_one_le (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (u : D.Row) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (u.toFrequency.j pr).val ≠ 0 → ∀ p ∈ OmegaStarMargin δ',
          ‖CorrectionFactors.localFactor D.context u pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-δ) := by
  obtain ⟨ρ, δ₀, hρ0, hρ1, hδ₀, hmaj⟩ := margin_data D δ' hδ'
  have hS : 0 ≤ ∑' i, BadPrimeShellSeries.weight ρ i :=
    tsum_nonneg (BadPrimeShellSeries.weight_nonneg hρ0.le)
  refine ⟨2 * (∑' i, BadPrimeShellSeries.weight ρ i) + 1, δ₀, by linarith, hδ₀, ?_⟩
  intro u pr hj p hp
  have hQ : 0 ≤ LocalFiniteSums.Q pr ^ (-δ₀) :=
    Real.rpow_nonneg (Q_pos' pr).le _
  have h := sub_one_le_aux D u pr hj p ρ _ hρ0.le hρ1 hQ
    (hmaj u pr hj p hp (0, 0, 0, 0)).1
    (fun i => (hmaj u pr hj p hp i).2.1) (fun i hi => (hmaj u pr hj p hp i).2.2 hi)
  refine h.trans ?_
  nlinarith [mul_nonneg hS hQ]

theorem localFactor_sub_one_le_paddedBoxes :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : D.Row) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (u.toFrequency.j pr).val ≠ 0 → ∀ p ∈ paddedBoxes,
          ‖CorrectionFactors.localFactor D.context u pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-(1 / 20000 : ℝ)) := by
  have hmaj := BadPrimeShellSeries.seriesTerm_majorant_paddedBoxes (A := D.recipe.A)
    (σ := D.recipe.σ) (η := D.recipe.target) (hS := D.recipe.traceBad)
  have hρ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 8 : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hρ1 : (2 : ℝ) ^ (-(1 / 8 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hS : 0 ≤ ∑' i, BadPrimeShellSeries.weight ((2 : ℝ) ^ (-(1 / 8 : ℝ))) i :=
    tsum_nonneg (BadPrimeShellSeries.weight_nonneg hρ0)
  refine ⟨2 * (∑' i, BadPrimeShellSeries.weight ((2 : ℝ) ^ (-(1 / 8 : ℝ))) i) + 1,
    by linarith, ?_⟩
  intro u pr hj p hp
  have hQ : 0 ≤ LocalFiniteSums.Q pr ^ (-(1 / 20000 : ℝ)) :=
    Real.rpow_nonneg (Q_pos' pr).le _
  have h := sub_one_le_aux D u pr hj p _ _ hρ0 hρ1 hQ
    (hmaj D.context pr (u.toFrequency.j pr) hj (u.toFrequency.theta pr) p hp (0, 0, 0, 0)).1
    (fun i => (hmaj D.context pr (u.toFrequency.j pr) hj (u.toFrequency.theta pr) p hp i).2.1)
    (fun i hi => (hmaj D.context pr (u.toFrequency.j pr) hj (u.toFrequency.theta pr) p hp i).2.2 hi)
  refine h.trans ?_
  nlinarith [mul_nonneg hS hQ]

end

end DedekindZetaZeroFree.Quantitative.EulerBadPrime
