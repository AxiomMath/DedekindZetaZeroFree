module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.CompactCasimirTransfer

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartDerivativeBounds

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped Matrix.Norms.Elementwise Pointwise ContDiff

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

private lemma matrixFunction_coe (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Mat) = f g := by
  unfold matrixFunction
  have hd : (g : Mat).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [dif_pos hd]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

private lemma slice_iteratedFDeriv_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E × F → ℂ) (U : Set (E × F)) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (n : ℕ) (p : E × F) (hp : p ∈ U) :
    iteratedFDeriv ℝ n (fun z => Φ (z, p.2)) p.1 =
      (iteratedFDeriv ℝ n Φ p).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E F) := by
  let c : E × F := (0, p.2)
  let s : Set (E × F) := {q | q + c ∈ U}
  let t : Set E := (ContinuousLinearMap.inl ℝ E F) ⁻¹' s
  have hs : IsOpen s := hU.preimage (continuous_id.add continuous_const)
  have ht : IsOpen t := hs.preimage (ContinuousLinearMap.inl ℝ E F).continuous
  have hc : c +ᵥ s = U := by
    ext u
    rw [Set.mem_vadd_set]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hq' : q + c ∈ U := hq
      simpa [vadd_eq_add, add_comm] using hq'
    · intro hu
      refine ⟨u - c, ?_, ?_⟩
      · simp only [s, Set.mem_setOf_eq]; simpa using hu
      · simp [vadd_eq_add]
  have hψ : ContDiffOn ℝ ∞ (fun q : E × F => Φ (q + c)) s := by
    refine hΦ.comp ((contDiff_id.add contDiff_const).contDiffOn) ?_
    intro q hq
    exact hq
  have hcomp : (fun z : E => Φ (z, p.2)) =
      (fun q : E × F => Φ (q + c)) ∘ (ContinuousLinearMap.inl ℝ E F) := by
    funext z
    simp [c, ContinuousLinearMap.inl]
  have hx : (ContinuousLinearMap.inl ℝ E F) p.1 ∈ s := by
    simp only [s, Set.mem_setOf_eq, ContinuousLinearMap.inl, c]
    simpa using hp
  have hkey := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (𝕜 := ℝ) (f := fun q : E × F => Φ (q + c)) (s := s) (i := n)
    (ContinuousLinearMap.inl ℝ E F) hψ hs.uniqueDiffOn ht.uniqueDiffOn hx
    (by simp : (n : ℕ∞ω) ≤ ∞)
  have hleft : iteratedFDerivWithin ℝ n ((fun q : E × F => Φ (q + c)) ∘
      (ContinuousLinearMap.inl ℝ E F)) t p.1 =
      iteratedFDeriv ℝ n (fun z => Φ (z, p.2)) p.1 := by
    rw [← hcomp]
    exact (iteratedFDerivWithin_of_isOpen n ht)
      (by simp only [t, Set.mem_preimage]; simpa using hx)
  have hright : iteratedFDerivWithin ℝ n (fun q : E × F => Φ (q + c)) s
      ((ContinuousLinearMap.inl ℝ E F) p.1) = iteratedFDeriv ℝ n Φ p := by
    rw [iteratedFDerivWithin_comp_add_right]
    rw [hc]
    have hp' : (ContinuousLinearMap.inl ℝ E F) p.1 + c = p := by
      simp [c, ContinuousLinearMap.inl]
    rw [hp']
    exact (iteratedFDerivWithin_of_isOpen n hU) hp
  rw [← hleft, hkey, hright]

private lemma continuousOn_slice_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E × F → ℂ) (U : Set (E × F)) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (n : ℕ) :
    ContinuousOn (fun p : E × F => iteratedFDeriv ℝ n (fun z => Φ (z, p.2)) p.1) U := by
  have hcont : ContinuousOn (fun p : E × F => iteratedFDeriv ℝ n Φ p) U :=
    (hΦ.continuousOn_iteratedFDerivWithin (by simp) hU.uniqueDiffOn).congr
      (fun p hp => (iteratedFDerivWithin_of_isOpen n hU hp).symm)
  have hcont2 : ContinuousOn (fun p : E × F =>
      (iteratedFDeriv ℝ n Φ p).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E F)) U :=
    (ContinuousMultilinearMap.continuous_precomp
      (fun _ : Fin n => ContinuousLinearMap.inl ℝ E F)).comp_continuousOn hcont
  exact hcont2.congr (fun p hp => slice_iteratedFDeriv_eq Φ U hU hΦ n p hp)

theorem translated_chart_smooth_jets (s : ℝ) (f : PrincipalSeries s)
    (g : ℂ → ComplexGL2)
    (hg : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => (g z : Matrix (Fin 2) (Fin 2) ℂ))) :
    (∀ k : ComplexSU2, ContDiff ℝ (⊤ : ℕ∞)
      (fun z => f (g z * complexSU2Embedding k))) ∧
    (∀ n : ℕ, Continuous (fun p : ComplexSU2 × ℂ =>
      iteratedFDeriv ℝ n (fun z => f (g z * complexSU2Embedding p.1)) p.2)) := by
  have hf := ((principalSeries_mem_iff s (f : ComplexGL2 → ℂ)).mp f.property).2
  have hgm : ContDiff ℝ ∞ (fun p : ℂ × Mat => (g p.1 : Mat)) := hg.comp contDiff_fst
  have hmul : ContDiff ℝ ∞ (fun p : ℂ × Mat => (g p.1 : Mat) * p.2) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply]
    apply ContDiff.sum
    intro l hl
    exact (contDiff_pi.mp (contDiff_pi.mp hgm i) l).mul
      (contDiff_pi.mp (contDiff_pi.mp contDiff_snd l) j)
  refine ⟨?_, ?_⟩
  · intro k
    have hk : ContDiff ℝ ∞ (fun z : ℂ =>
        (g z : Mat) * ((complexSU2Embedding k : ComplexGL2) : Mat)) :=
      hmul.comp (contDiff_id.prodMk contDiff_const)
    have hmap : ∀ z : ℂ,
        ((g z : Mat) * ((complexSU2Embedding k : ComplexGL2) : Mat)).det ≠ 0 := by
      intro z
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.GeneralLinearGroup.det (g z)).ne_zero
        (Matrix.GeneralLinearGroup.det (complexSU2Embedding k)).ne_zero
    have h := hf.comp_contDiff hk hmap
    have he : (fun z : ℂ => matrixFunction (f : ComplexGL2 → ℂ)
        ((g z : Mat) * ((complexSU2Embedding k : ComplexGL2) : Mat))) =
        (fun z : ℂ => f (g z * complexSU2Embedding k)) := by
      funext z
      rw [← Matrix.GeneralLinearGroup.coe_mul]
      exact matrixFunction_coe (f : ComplexGL2 → ℂ) (g z * complexSU2Embedding k)
    rw [← he]
    exact h
  · intro n
    let Φ : ℂ × Mat → ℂ := fun p => matrixFunction (f : ComplexGL2 → ℂ) ((g p.1 : Mat) * p.2)
    let U : Set (ℂ × Mat) := {p | p.2.det ≠ 0}
    have hU : IsOpen U := isOpen_ne.preimage (by
      simp_rw [Matrix.det_fin_two]; fun_prop)
    have hΦ : ContDiffOn ℝ ∞ Φ U := by
      refine hf.comp hmul.contDiffOn ?_
      intro p hp
      change ((g p.1 : Mat) * p.2).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.GeneralLinearGroup.det (g p.1)).ne_zero hp
    have hcont := continuousOn_slice_iteratedFDeriv Φ U hU hΦ n
    have hψ : Continuous (fun p : ComplexSU2 × ℂ => (p.2, (p.1 : Mat))) :=
      continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
    have hmaps : ∀ p : ComplexSU2 × ℂ, (p.2, (p.1 : Mat)) ∈ U := by
      intro p
      simp only [U, Set.mem_setOf_eq]
      rw [(Matrix.mem_specialUnitaryGroup_iff.mp p.1.property).2]
      exact one_ne_zero
    have hcont2 := hcont.comp_continuous hψ hmaps
    have he : (fun p : ComplexSU2 × ℂ =>
        iteratedFDeriv ℝ n (fun z => Φ (z, (p.1 : Mat))) p.2) =
        (fun p : ComplexSU2 × ℂ =>
        iteratedFDeriv ℝ n (fun z => f (g z * complexSU2Embedding p.1)) p.2) := by
      funext p
      congr 1
      funext z
      simp only [Φ]
      change matrixFunction (f : ComplexGL2 → ℂ)
        ((g z * complexSU2Embedding p.1 : ComplexGL2) : Mat) =
        f (g z * complexSU2Embedding p.1)
      exact matrixFunction_coe (f : ComplexGL2 → ℂ) (g z * complexSU2Embedding p.1)
    rw [← he]
    exact hcont2

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartDerivativeBounds

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartDerivativeBounds

open MeasureTheory

theorem compact_weighted_integral_jet_bound
    {Q : Type*} [TopologicalSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) (hprob : IsProbabilityMeasure μ)
    (F : ℂ → Q → ℂ)
    (hsmooth : ∀ q, ContDiff ℝ (⊤ : ℕ∞) (fun z => F z q))
    (hjets : ∀ j : ℕ, Continuous (fun p : Q × ℂ =>
      iteratedFDeriv ℝ j (fun z => F z p.1) p.2))
    (S : Set ℂ) (hS : IsCompact S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Q → ℂ) (A : ℝ),
      Continuous a → 0 ≤ A → (∀ q, ‖a q‖ ≤ A) →
      ContDiff ℝ (⊤ : ℕ∞) (fun w => ∫ q, a q * F w q ∂μ) ∧
      ∀ z ∈ S, ‖iteratedFDeriv ℝ n
        (fun w => ∫ q, a q * F w q ∂μ) z‖ ≤ C * A := by
  obtain ⟨K, hK⟩ := (isCompact_univ.prod hS).exists_bound_of_continuousOn
    ((hjets n).continuousOn.mono (Set.subset_univ _))
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro a A ha hA hAa

  have hsmul : ∀ (m : ℕ) (q : Q) (u : ℂ),
      iteratedFDeriv ℝ m (fun v => a q * F v q) u =
        a q • iteratedFDeriv ℝ m (fun v => F v q) u := by
    intro m q u
    have h := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := m)
      (a := a q) (f := fun v => F v q) (x := u) ((hsmooth q).contDiffAt.of_le (by simp))
    simpa only [smul_eq_mul] using h
  have hsmooth' : ∀ q : Q, ContDiff ℝ (⊤ : ℕ∞) (fun u => a q * F u q) :=
    fun q => contDiff_const.mul (hsmooth q)

  have hmeas : ∀ m : ℕ, ∀ u : ℂ,
      AEStronglyMeasurable (fun q => iteratedFDeriv ℝ m (fun v => a q * F v q) u) μ := by
    intro m u
    apply Continuous.aestronglyMeasurable_of_compactSpace
    have hcont : Continuous (fun q => iteratedFDeriv ℝ m (fun v => F v q) u) :=
      (hjets m).comp (continuous_id.prodMk continuous_const)
    convert (ha.smul hcont) using 1
    funext q
    exact hsmul m q u

  have hbound : ∀ m : ℕ, ∀ u : ℂ, ∃ (s : Set ℂ) (b : Q → ℝ),
      s ∈ nhds u ∧ Integrable b μ ∧
        ∀ᵐ q ∂μ, ∀ v ∈ s, ‖iteratedFDeriv ℝ m (fun w => a q * F w q) v‖ ≤ b q := by
    intro m u
    obtain ⟨K', hK'⟩ := (isCompact_univ.prod (isCompact_closedBall u 1)).exists_bound_of_continuousOn
      ((hjets m).continuousOn.mono (Set.subset_univ _))
    refine ⟨Metric.ball u 1, fun _ => A * max K' 0, Metric.ball_mem_nhds u zero_lt_one,
      integrable_const _, ?_⟩
    filter_upwards with q v hv
    rw [hsmul m q v, norm_smul]
    calc ‖a q‖ * ‖iteratedFDeriv ℝ m (fun v => F v q) v‖
        ≤ A * K' := by
          apply mul_le_mul (hAa q) _ (norm_nonneg _) hA
          exact hK' (q, v) ⟨Set.mem_univ _, Metric.ball_subset_closedBall hv⟩
      _ ≤ A * max K' 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hA
  obtain ⟨hcd, hformula⟩ :=
    KPCplxHarmonicIntertwinerSpectrum.integral_contDiff_of_locally_dominated_jets
      μ (fun u q => a q * F u q) hsmooth' hmeas hbound
  refine ⟨hcd, ?_⟩
  intro z hz
  rw [hformula n z]
  calc ‖∫ q, iteratedFDeriv ℝ n (fun v => a q * F v q) z ∂μ‖
      ≤ (max K 0) * A * μ.real Set.univ := by
        apply norm_integral_le_of_norm_le_const
        filter_upwards with q
        rw [hsmul n q z, norm_smul]
        calc ‖a q‖ * ‖iteratedFDeriv ℝ n (fun v => F v q) z‖
            ≤ A * K := by
              apply mul_le_mul (hAa q) _ (norm_nonneg _) hA
              exact hK (q, z) ⟨Set.mem_univ _, hz⟩
          _ ≤ (max K 0) * A := by
              rw [mul_comm (max K 0) A]
              exact mul_le_mul_of_nonneg_left (le_max_left _ _) hA
    _ = (max K 0) * A := by simp

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartDerivativeBounds

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open ChartDerivativeBounds
open scoped Matrix.Norms.Elementwise

private theorem chart_average_bound (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (f : PrincipalSeries s) (n : ℕ)
    (g : ℂ → ComplexGL2)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun z => (g z : Matrix (Fin 2) (Fin 2) ℂ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ n (fun w => characterAverage s μ ℓ f (g w)) z‖ ≤
        C * ((2 * ℓ + 1 : ℕ) : ℝ) ^ 2 := by
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  obtain ⟨hsmooth, hjets⟩ := translated_chart_smooth_jets s f g hg
  obtain ⟨C, hC, hbound⟩ := compact_weighted_integral_jet_bound μ hprob
    (fun z k => f (g z * complexSU2Embedding k)) hsmooth hjets
    (Metric.closedBall (0 : ℂ) 1) (isCompact_closedBall 0 1) n
  refine ⟨C, hC, ?_⟩
  intro ℓ z hz
  obtain ⟨hc, hn⟩ := su2_character_continuous_norm_bound ℓ
  obtain ⟨hI, hIb⟩ := hbound (fun k => star (su2HarmonicCharacter ℓ k))
    ((2 * ℓ + 1 : ℕ) : ℝ) hc.star (by positivity)
    (fun k => by simpa only [norm_star] using hn k)
  have heq : (fun w => characterAverage s μ ℓ f (g w)) =
      (((2 * ℓ + 1 : ℕ) : ℂ) • (fun w => ∫ k : ComplexSU2,
        star (su2HarmonicCharacter ℓ k) * f (g w * complexSU2Embedding k) ∂μ)) := by
    funext w
    exact characterAverage_formula s μ ℓ f (g w)
  rw [heq, iteratedFDeriv_const_smul_apply (hI.contDiffAt.of_le (by simp)), norm_smul]
  have hdim : ‖((2 * ℓ + 1 : ℕ) : ℂ)‖ = ((2 * ℓ + 1 : ℕ) : ℝ) := by
    rw [← Complex.norm_natCast]
  rw [hdim]
  calc
    _ ≤ ((2 * ℓ + 1 : ℕ) : ℝ) * (C * ((2 * ℓ + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hIb z hz) (by positivity)
    _ = _ := by ring

theorem characterAverage_disc_derivative_quadratic_bound
    (s : ℝ) (μ : Measure ComplexSU2) (hprob : IsProbabilityMeasure μ)
    (f : PrincipalSeries s) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      (∀ x ∈ Metric.closedBall (0 : ℂ) 1,
        ‖iteratedFDeriv ℝ n (openCoordinate (characterAverage s μ ℓ f)) x‖ ≤
          C * (ℓ + 1 : ℝ) ^ 2) ∧
      (∀ u ∈ Metric.closedBall (0 : ℂ) 1,
        ‖iteratedFDeriv ℝ n (infinityCoordinate (characterAverage s μ ℓ f)) u‖ ≤
          C * (ℓ + 1 : ℝ) ^ 2) := by
  have hgo : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      (weyl * upperUnipotent z : Matrix (Fin 2) (Fin 2) ℂ)) := by
    unfold upperUnipotent
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      (weyl : Matrix (Fin 2) (Fin 2) ℂ) * !![1, z; 0, 1])
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  have hgi : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      (lowerUnipotent z : Matrix (Fin 2) (Fin 2) ℂ)) := by
    unfold lowerUnipotent
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => !![1, 0; z, 1])
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  obtain ⟨A, hA, ho⟩ := chart_average_bound s μ hprob f n
    (fun z => weyl * upperUnipotent z) hgo
  obtain ⟨B, hB, hi⟩ := chart_average_bound s μ hprob f n lowerUnipotent hgi
  refine ⟨4 * max A B, by positivity, ?_⟩
  intro ℓ
  have hd : ((2 * ℓ + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (ℓ + 1 : ℝ) ^ 2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hb (D : ℝ) (hD : 0 ≤ D) (hDM : D ≤ max A B) :
      D * ((2 * ℓ + 1 : ℕ) : ℝ) ^ 2 ≤ (4 * max A B) * (ℓ + 1 : ℝ) ^ 2 := by
    calc
      _ ≤ D * (4 * (ℓ + 1 : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hd hD
      _ ≤ max A B * (4 * (ℓ + 1 : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hDM (by positivity)
      _ = _ := by ring
  constructor
  · intro x hx
    exact (ho ℓ x hx).trans (hb A hA (le_max_left A B))
  · intro u hu
    exact (hi ℓ u hu).trans (hb B hB (le_max_right A B))

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartRemainder

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory

theorem chartSeminorm_le_of_disc_derivative_bound (s : ℝ) (n : ℕ)
    (f : PrincipalSeries s) (B : ℝ)
    (hopen : ∀ x ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ n (openCoordinate f) x‖ ≤ B)
    (hinfty : ∀ u ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ n (infinityCoordinate f) u‖ ≤ B) :
    chartSeminorm s n f ≤ B := by
  change max _ _ ≤ B
  apply max_le
  · apply csSup_le
    · exact ⟨_, ⟨0, by simp, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hopen x hx
  · apply csSup_le
    · exact ⟨_, ⟨0, by simp, rfl⟩⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact hinfty u hu

theorem chartSeminorm_summable_of_inverseSquare_bound (s : ℝ) (n : ℕ)
    (a : ℕ → PrincipalSeries s) (C : ℝ)
    (hbound : ∀ ℓ, chartSeminorm s n (a ℓ) ≤ C / (ℓ + 1 : ℝ) ^ 2) :
    Summable (fun ℓ => chartSeminorm s n (a ℓ)) := by
  have hp : Summable (fun ℓ : ℕ => 1 / (ℓ : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun ℓ : ℕ => 1 / (ℓ + 1 : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hp
  have hC : Summable (fun ℓ : ℕ => C / (ℓ + 1 : ℝ) ^ 2) := by
    simpa only [mul_one_div] using hs.mul_left C
  exact hC.of_nonneg_of_le
    (fun ℓ => apply_nonneg (chartSeminorm s n) (a ℓ)) hbound

theorem chartSeminorm_summable_of_shiftedCasimirSquare (s : ℝ) (n : ℕ)
    (a b : ℕ → PrincipalSeries s) (C : ℝ)
    (hb : ∀ ℓ, chartSeminorm s n (b ℓ) ≤ C * (ℓ + 1 : ℝ) ^ 2)
    (he : ∀ ℓ, b ℓ = (((1 + (ℓ : ℝ) * (ℓ + 1)) ^ 2 : ℝ) : ℂ) • a ℓ) :
    Summable (fun ℓ => chartSeminorm s n (a ℓ)) := by
  have hC : 0 ≤ C := by
    simpa using (apply_nonneg (chartSeminorm s n) (b 0)).trans (hb 0)
  apply chartSeminorm_summable_of_inverseSquare_bound s n a (4 * C)
  intro ℓ
  let t : ℝ := ℓ + 1
  let q : ℝ := 1 + (ℓ : ℝ) * (ℓ + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have htq : t ^ 2 ≤ 2 * q := by
    dsimp [t, q]
    nlinarith [sq_nonneg ((ℓ : ℝ) - 1)]
  have hsq : t ^ 2 * t ^ 2 ≤ 4 * q ^ 2 := by
    nlinarith [sq_nonneg (t ^ 2 - 2 * q)]
  have hb' : q ^ 2 * chartSeminorm s n (a ℓ) ≤ C * t ^ 2 := by
    have h := hb ℓ
    rw [he ℓ, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at h
    exact h
  have hfirst : chartSeminorm s n (a ℓ) ≤ C * t ^ 2 / q ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by simpa [mul_comm] using hb')
  apply hfirst.trans
  change C * t ^ 2 / q ^ 2 ≤ 4 * C / t ^ 2
  apply (div_le_div_iff₀ (sq_pos_of_pos hq) (sq_pos_of_pos ht)).mpr
  calc
    C * t ^ 2 * t ^ 2 = C * (t ^ 2 * t ^ 2) := by ring
    _ ≤ C * (4 * q ^ 2) := mul_le_mul_of_nonneg_left hsq hC
    _ = 4 * C * q ^ 2 := by ring

theorem characterAverage_chartSeminorm_summable_of_shiftedCasimirSquare
    (s : ℝ) (μ : Measure ComplexSU2) (f w : PrincipalSeries s)
    (a b : ℕ → PrincipalSeries s)
    (ha : ∀ ℓ g, a ℓ g = characterAverage s μ ℓ f g)
    (hb : ∀ ℓ g, b ℓ g = characterAverage s μ ℓ w g)
    (htransfer : ∀ ℓ g, characterAverage s μ ℓ w g =
      ((((1 + (ℓ : ℝ) * (ℓ + 1)) ^ 2 : ℝ) : ℂ) * characterAverage s μ ℓ f g))
    (hbound : ∀ n : ℕ, ∃ C : ℝ, ∀ ℓ : ℕ,
      chartSeminorm s n (b ℓ) ≤ C * (ℓ + 1 : ℝ) ^ 2) :
    ∀ n : ℕ, Summable (fun ℓ => chartSeminorm s n (a ℓ)) := by
  intro n
  obtain ⟨C, hC⟩ := hbound n
  apply chartSeminorm_summable_of_shiftedCasimirSquare s n a b C hC
  intro ℓ
  apply Subtype.ext
  funext g
  change b ℓ g = _ * a ℓ g
  rw [hb ℓ g, ha ℓ g]
  exact htransfer ℓ g

theorem characterAverage_chartSeminorm_summable (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : PrincipalSeries s) (a : ℕ → PrincipalSeries s)
    (ha : ∀ ℓ g, a ℓ g = characterAverage s μ ℓ f g) :
    ∀ n : ℕ, Summable (fun ℓ => chartSeminorm s n (a ℓ)) := by
  obtain ⟨v, hv⟩ := CasimirTransfer.exists_shiftedCasimir_transfer_section s f
  obtain ⟨w, hw⟩ := CasimirTransfer.exists_shiftedCasimir_transfer_section s v
  let b : ℕ → PrincipalSeries s := fun ℓ =>
    ((((1 + (ℓ : ℝ) * (ℓ + 1)) ^ 2 : ℝ) : ℂ) • a ℓ)
  have hb : ∀ ℓ g, b ℓ g = characterAverage s μ ℓ w g := by
    intro ℓ g
    change ((((1 + (ℓ : ℝ) * (ℓ + 1)) ^ 2 : ℝ) : ℂ) * a ℓ g) = _
    rw [ha ℓ g, hw μ hhaar hprob ℓ g, hv μ hhaar hprob ℓ g]
    push_cast
    ring
  apply characterAverage_chartSeminorm_summable_of_shiftedCasimirSquare
    s μ f w a b ha hb
  · intro ℓ g
    rw [hw μ hhaar hprob ℓ g, hv μ hhaar hprob ℓ g]
    push_cast
    ring
  · intro n
    obtain ⟨C, _, hC⟩ :=
      CasimirTransfer.characterAverage_disc_derivative_quadratic_bound
        s μ hprob w n
    refine ⟨C, fun ℓ => ?_⟩
    apply chartSeminorm_le_of_disc_derivative_bound
    · have he : openCoordinate (b ℓ) = openCoordinate (characterAverage s μ ℓ w) :=
        congrArg openCoordinate (funext (hb ℓ))
      rw [he]
      exact (hC ℓ).1
    · have he : infinityCoordinate (b ℓ) = infinityCoordinate (characterAverage s μ ℓ w) :=
        congrArg infinityCoordinate (funext (hb ℓ))
      rw [he]
      exact (hC ℓ).2

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartRemainder

end
