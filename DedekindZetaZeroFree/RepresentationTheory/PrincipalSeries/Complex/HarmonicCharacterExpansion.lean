module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicExhaustion
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.CompactPolynomialApproximation
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.CharacterAverageJetBounds

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartRemainder

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped BigOperators Topology

private lemma infinityChart_lowerUnipotent_zero_eq_one : lowerUnipotent 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

private lemma principalSeries_identityEvaluation_norm_le_chartSeminorm_zero (s : ℝ) (f : PrincipalSeries s) :
    ‖f 1‖ ≤ chartSeminorm s 0 f := by
  have hc : Continuous (fun u : ℂ => ‖infinityCoordinate f u‖) :=
    f.property.2.2.continuous.norm
  have hb := (isCompact_closedBall (0 : ℂ) 1).image hc
  have hh : ‖infinityCoordinate f 0‖ ≤
      sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1) := by
    apply le_csSup hb.bddAbove
    exact ⟨0, by simp, rfl⟩
  change ‖f 1‖ ≤ chartSeminormValue s 0 f
  simpa only [chartSeminormValue, norm_iteratedFDeriv_zero, infinityCoordinate,
    infinityChart_lowerUnipotent_zero_eq_one] using hh.trans (le_max_right
      (sSup ((fun x : ℂ => ‖openCoordinate f x‖) '' Metric.closedBall 0 1))
      (sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1)))

private lemma principalSeries_scalarEvaluation_continuous_of_chartSeminorms (s : ℝ) (g : ComplexGL2) :
    Continuous (fun f : PrincipalSeries s => f g) := by
  let e : PrincipalSeries s →ₗ[ℂ] ℂ :=
    { toFun := fun f => f 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hc : Continuous e := by
    apply WithSeminorms.continuous_normedSpace_rng ℂ
      (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩) e
    refine ⟨{0}, 1, ?_⟩
    intro f
    simpa [e] using principalSeries_identityEvaluation_norm_le_chartSeminorm_zero s f
  have h := hc.comp ((pi_continuous s).comp
    (continuous_const.prodMk continuous_id : Continuous (fun f : PrincipalSeries s =>
      (Matrix.ProjGenLinGroup.mk g, f))))
  have he : (fun f : PrincipalSeries s => e (pi s (Matrix.ProjGenLinGroup.mk g) f)) =
      (fun f : PrincipalSeries s => f g) := by
    funext f
    change f (1 * g) = f g
    rw [one_mul]
  exact he ▸ h

theorem chart_remainder_of_summable_of_compact_tendsto (s : ℝ)
    (f : PrincipalSeries s) (a : ℕ → PrincipalSeries s)
    (hsum : ∀ n : ℕ, Summable (fun ℓ => chartSeminorm s n (a ℓ)))
    (hcompact : ∀ k : ComplexSU2,
      Filter.Tendsto (fun N => (∑ ℓ ∈ Finset.range N, a ℓ) (complexSU2Embedding k))
        Filter.atTop (nhds (f (complexSU2Embedding k)))) (n : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in Filter.atTop,
      chartSeminorm s n ((∑ ℓ ∈ Finset.range N, a ℓ) - f) < ε := by
  classical
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (PrincipalSeries s) := principalSeries_complete s
  have hp : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  have hsum_le (i : ℕ) (t : Finset ℕ) :
      chartSeminorm s i (∑ j ∈ t, a j) ≤ ∑ j ∈ t, chartSeminorm s i (a j) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ht =>
        simp only [Finset.sum_insert hj]
        exact (map_add_le_add (chartSeminorm s i) (a j) (∑ k ∈ t, a k)).trans
          (add_le_add le_rfl ht)
  have ha : Summable a := by
    apply summable_iff_cauchySeq_finset.mpr
    apply cauchySeq_finset_iff_sum_vanishing.mpr
    intro e he
    obtain ⟨⟨I, ε⟩, hε, hIe⟩ := hp.hasBasis_zero_ball.mem_iff.mp he
    have htail : ∀ i : ℕ, ∃ S : Finset ℕ, ∀ t : Finset ℕ, Disjoint t S →
        ‖∑ j ∈ t, chartSeminorm s i (a j)‖ < ε :=
      fun i => summable_iff_vanishing_norm.mp (hsum i) ε hε
    choose S hS using htail
    refine ⟨I.biUnion S, fun t ht => hIe ?_⟩
    rw [Seminorm.mem_ball_zero]
    apply Seminorm.finset_sup_apply_lt hε
    intro i hi
    exact (hsum_le i t).trans_lt ((le_abs_self _).trans_lt
      (hS i t ((Finset.disjoint_biUnion_right t I S).mp ht i hi)))
  have ht := ha.hasSum.tendsto_sum_nat
  have heq : (∑' j, a j) = f := by
    apply KPCplxIntertwinerEigenvalues.compactRestriction_injective s
    funext k
    exact tendsto_nhds_unique
      ((principalSeries_scalarEvaluation_continuous_of_chartSeminorms s (complexSU2Embedding k)).tendsto _ |>.comp ht)
      (hcompact k)
  rw [heq] at ht
  exact (hp.tendsto_nhds _ _).mp ht n

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartRemainder

end

section

namespace DedekindZetaZeroFree.KPCplxInverseTopology

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped BigOperators

open KPCplxCharacterHaar KPCplxHarmonicExtraction MeasureTheory
open scoped Topology Matrix.Norms.Elementwise

theorem raw_average_section (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (ℓ : ℕ) (f : PrincipalSeries s) :
    characterAverage s μ ℓ f ∈ principalSeriesSubmodule s := by
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro a d b g
    unfold characterAverage
    simp_rw [mul_assoc]
    have hcov : ∀ k : ComplexSU2,
        f (upperTriangular a d b * (g * complexSU2Embedding k)) =
          (inductionWeight s a d : ℂ) * f (g * complexSU2Embedding k) :=
      fun k => f.property.1 a d b _
    simp_rw [hcov]
    rw [show (fun k : ComplexSU2 => star (su2HarmonicCharacter ℓ k) *
        ((inductionWeight s a d : ℂ) * f (g * complexSU2Embedding k))) =
        (fun k => (inductionWeight s a d : ℂ) *
          (star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k))) by
      funext k; ring, integral_const_mul]
    ring
  all_goals
    have hsmooth (g : ℂ → ComplexGL2)
        (hg : ContDiff ℝ (⊤ : ℕ∞) (fun z => (g z : Matrix (Fin 2) (Fin 2) ℂ))) :
        ContDiff ℝ (⊤ : ℕ∞) (fun z => characterAverage s μ ℓ f (g z)) := by
      obtain ⟨hs, hj⟩ := ChartDerivativeBounds.translated_chart_smooth_jets s f g hg
      obtain ⟨C, hC, hb⟩ := ChartDerivativeBounds.compact_weighted_integral_jet_bound
        μ hprob (fun z k => f (g z * complexSU2Embedding k)) hs hj
        (Metric.closedBall 0 1) (isCompact_closedBall 0 1) 0
      obtain ⟨hc, hn⟩ := ChartDerivativeBounds.su2_character_continuous_norm_bound ℓ
      have hi := (hb (fun k => star (su2HarmonicCharacter ℓ k))
        ((2 * ℓ + 1 : ℕ) : ℝ) hc.star (by positivity)
        (fun k => by simpa only [norm_star] using hn k)).1
      exact contDiff_const.mul hi
  · apply hsmooth (fun z => weyl * upperUnipotent z)
    unfold upperUnipotent
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      (weyl : Matrix (Fin 2) (Fin 2) ℂ) * !![1, z; 0, 1])
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  · apply hsmooth lowerUnipotent
    unfold lowerUnipotent
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      (!![1, 0; z, 1] : Matrix (Fin 2) (Fin 2) ℂ))
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

noncomputable def averageSection (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (ℓ : ℕ) (f : PrincipalSeries s) : PrincipalSeries s :=
  ⟨characterAverage s μ ℓ f, raw_average_section s μ hprob ℓ f⟩

private theorem average_summable (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ) (f : PrincipalSeries s) :
    Summable (fun ℓ => averageSection s μ hprob ℓ f) := by
  classical
  let a := fun ℓ => averageSection s μ hprob ℓ f
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (PrincipalSeries s) := principalSeries_complete s
  have hp : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  have hsum := ChartRemainder.characterAverage_chartSeminorm_summable
    s μ hhaar hprob f a (fun _ _ => rfl)
  have hsum_le (i : ℕ) (t : Finset ℕ) :
      chartSeminorm s i (∑ j ∈ t, a j) ≤ ∑ j ∈ t, chartSeminorm s i (a j) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ht =>
      simp only [Finset.sum_insert hj]
      exact (map_add_le_add (chartSeminorm s i) _ _).trans (add_le_add le_rfl ht)
  apply summable_iff_cauchySeq_finset.mpr
  apply cauchySeq_finset_iff_sum_vanishing.mpr
  intro e he
  obtain ⟨⟨I, ε⟩, hε, hIe⟩ := hp.hasBasis_zero_ball.mem_iff.mp he
  have htail : ∀ i : ℕ, ∃ S : Finset ℕ, ∀ t : Finset ℕ, Disjoint t S →
      ‖∑ j ∈ t, chartSeminorm s i (a j)‖ < ε :=
    fun i => summable_iff_vanishing_norm.mp (hsum i) ε hε
  choose S hS using htail
  refine ⟨I.biUnion S, fun t ht => hIe ?_⟩
  rw [Seminorm.mem_ball_zero]
  apply Seminorm.finset_sup_apply_lt hε
  intro i hi
  exact (hsum_le i t).trans_lt ((le_abs_self _).trans_lt
    (hS i t ((Finset.disjoint_biUnion_right t I S).mp ht i hi)))

noncomputable def evalOne (s : ℝ) : PrincipalSeries s →L[ℂ] ℂ := by
  let e : PrincipalSeries s →ₗ[ℂ] ℂ :=
    { toFun := fun f => f 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨e, ?_⟩
  apply WithSeminorms.continuous_normedSpace_rng ℂ
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩) e
  refine ⟨{0}, 1, ?_⟩
  intro f
  have hc : Continuous (fun u : ℂ => ‖infinityCoordinate f u‖) :=
    f.property.2.2.continuous.norm
  have hh : ‖infinityCoordinate f 0‖ ≤
      sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1) := by
    apply le_csSup ((isCompact_closedBall (0 : ℂ) 1).image hc).bddAbove
    exact ⟨0, by simp, rfl⟩
  have hz : lowerUnipotent 0 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]
  simp only [Finset.sup_singleton, one_smul]
  change ‖f 1‖ ≤ chartSeminormValue s 0 f
  simpa only [chartSeminormValue,
    norm_iteratedFDeriv_zero, infinityCoordinate, hz] using
    hh.trans (le_max_right
      (sSup ((fun x : ℂ => ‖openCoordinate f x‖) '' Metric.closedBall 0 1))
      (sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1)))

theorem embedding_continuous : Continuous complexSU2Embedding := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · have he (k : ComplexSU2) :
        (↑(complexSU2Embedding k)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) =
          star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← map_inv]
      rfl
    simp_rw [he]
    exact continuous_subtype_val.star

theorem eval_continuous (s : ℝ) (g : ComplexGL2) :
    Continuous (fun f : PrincipalSeries s => f g) := by
  have hc := (evalOne s).continuous.comp ((pi_continuous s).comp
    (continuous_const.prodMk continuous_id : Continuous (fun f : PrincipalSeries s =>
      (Matrix.ProjGenLinGroup.mk g, f))))
  convert hc using 1
  funext f
  dsimp only [Function.comp_def, evalOne]
  change f g = f (1 * g)
  rw [one_mul]

theorem average_eval_continuous (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (ℓ : ℕ) (g : ComplexGL2) :
    Continuous (fun f : PrincipalSeries s => characterAverage s μ ℓ f g) := by
  letI : IsProbabilityMeasure μ := hprob
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  have hj : Continuous (fun p : PrincipalSeries s × ComplexSU2 =>
      p.1 (g * complexSU2Embedding p.2)) := by
    have hproj : Continuous (Matrix.ProjGenLinGroup.mk : ComplexGL2 → ComplexPGL2) :=
      continuous_coinduced_rng
    have h := (evalOne s).continuous.comp ((pi_continuous s).comp
      ((hproj.comp ((continuous_const : Continuous (fun _ : PrincipalSeries s × ComplexSU2 => g)).mul
        (embedding_continuous.comp continuous_snd))).prodMk continuous_fst))
    convert h using 1
    funext p
    dsimp only [Function.comp_def, evalOne]
    change p.1 (g * complexSU2Embedding p.2) = p.1 (1 * (g * complexSU2Embedding p.2))
    rw [one_mul]
  obtain ⟨hc, _⟩ := ChartDerivativeBounds.su2_character_continuous_norm_bound ℓ
  have hi : Continuous (fun f : PrincipalSeries s => ∫ k : ComplexSU2,
      star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k) ∂μ) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
    · exact ((hc.comp continuous_snd).star.mul hj).continuousOn
    · intro p x hp hx
      exact (hx (Set.mem_univ x)).elim
  exact continuous_const.mul hi

noncomputable def averageEval (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (ℓ : ℕ) (g : ComplexGL2) :
    PrincipalSeries s →L[ℂ] ℂ := by
  letI : IsProbabilityMeasure μ := hprob
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  let L : PrincipalSeries s →ₗ[ℂ] ℂ :=
    { toFun := fun f => characterAverage s μ ℓ f g
      map_add' := by
        intro f h
        unfold characterAverage
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        rw [integral_add]
        · ring
        all_goals
          apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
          obtain ⟨hc, _⟩ := ChartDerivativeBounds.su2_character_continuous_norm_bound ℓ
          apply hc.star.mul
          have horbit (v : PrincipalSeries s) : Continuous (fun k : ComplexSU2 =>
              v (g * complexSU2Embedding k)) := by
            have h := (pi_continuous s).comp
              (((continuous_coinduced_rng : Continuous (Matrix.ProjGenLinGroup.mk :
                ComplexGL2 → ComplexPGL2)).comp
                ((continuous_const : Continuous (fun _ : ComplexSU2 => g)).mul embedding_continuous)).prodMk
                (continuous_const : Continuous (fun _ : ComplexSU2 => v)))
            have hi := (evalOne s).continuous.comp h
            convert hi using 1
            funext k
            dsimp only [Function.comp_def, evalOne]
            change v (g * complexSU2Embedding k) = v (1 * (g * complexSU2Embedding k))
            rw [one_mul]
          exact horbit _
      map_smul' := by
        intro c f
        unfold characterAverage
        simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        simp_rw [show ∀ k : ComplexSU2, star (su2HarmonicCharacter ℓ k) *
          (c * f (g * complexSU2Embedding k)) = c *
            (star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k)) by
          intro k; ring]
        rw [integral_const_mul]
        ring }
  exact ⟨L, average_eval_continuous s μ hprob ℓ g⟩

noncomputable def evaluation (s : ℝ) (g : ComplexGL2) :
    PrincipalSeries s →L[ℂ] ℂ :=
  ⟨{ toFun := fun f => f g, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }, eval_continuous s g⟩

private theorem average_on_harmonic (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (j : ℕ) (f : PrincipalSeries s) (hf : f ∈ harmonicKType s j)
    (ℓ : ℕ) (k : ComplexSU2) :
    characterAverage s μ ℓ f (complexSU2Embedding k) =
      if ℓ = j then f (complexSU2Embedding k) else 0 := by
  obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp hf
  have hv (t : ComplexSU2) : f (complexSU2Embedding t) = polynomialCompactRestriction p t :=
    (congrFun he t).symm
  unfold characterAverage
  simp_rw [← map_mul, hv]
  by_cases hℓ : ℓ = j
  · subst ℓ
    rw [if_pos rfl]
    exact CompactPolynomial.harmonic_character_projection_diagonal μ hhaar hprob j p hp k
  · rw [if_neg hℓ]
    rw [CompactPolynomial.harmonic_character_projection_off_diagonal
      μ hhaar hprob ℓ j (Ne.symm hℓ) p hp k, mul_zero]

private theorem average_tsum_eq (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ) (f : PrincipalSeries s) :
    (∑' ℓ, averageSection s μ hprob ℓ f) = f := by
  classical
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI := principalSeries_metrizable s
  letI := principalSeries_complete s
  letI : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  letI : BarrelledSpace ℂ (PrincipalSeries s) := by
    letI := IsUniformAddGroup.uniformity_countably_generated (α := PrincipalSeries s)
    infer_instance
  apply compactRestriction_injective s
  funext k
  let P : ℕ → PrincipalSeries s →L[ℂ] ℂ :=
    fun N => ∑ ℓ ∈ Finset.range N, averageEval s μ hprob ℓ (complexSU2Embedding k)
  let F : PrincipalSeries s → ℂ :=
    fun v => (∑' ℓ, averageSection s μ hprob ℓ v) (complexSU2Embedding k)
  have hlim : Filter.Tendsto (fun N v => P N v) Filter.atTop (nhds F) := by
    apply tendsto_pi_nhds.mpr
    intro v
    have h := ((evaluation s (complexSU2Embedding k)).continuous.tendsto _).comp
      ((average_summable s μ hhaar hprob v).hasSum.tendsto_sum_nat)
    have he (N : ℕ) : P N v =
        (∑ ℓ ∈ Finset.range N, averageSection s μ hprob ℓ v) (complexSU2Embedding k) := by
      simp only [P, ContinuousLinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      rfl
    simp only [he]
    exact h
  let T : PrincipalSeries s →L[ℂ] ℂ := continuousLinearMapOfTendsto P hlim
  have hT (v : PrincipalSeries s) : T v = F v := rfl
  let E := evaluation s (complexSU2Embedding k)
  let U := (T - E).ker
  have hclosed : IsClosed (U : Set (PrincipalSeries s)) := (T - E).isClosed_ker
  have hall : ∀ j, harmonicKType s j ≤ U := by
    intro j v hv
    have hevent : (fun N => P N v) =ᶠ[Filter.atTop] (fun _ => v (complexSU2Embedding k)) := by
      filter_upwards [Filter.eventually_gt_atTop j] with N hN
      dsimp only [P]
      simp only [ContinuousLinearMap.sum_apply]
      change (∑ ℓ ∈ Finset.range N, characterAverage s μ ℓ v (complexSU2Embedding k)) = _
      simp_rw [average_on_harmonic s μ hhaar hprob j v hv]
      simp [Finset.mem_range, hN]
    have heq : F v = v (complexSU2Embedding k) :=
      tendsto_nhds_unique ((tendsto_pi_nhds.mp hlim) v)
        (tendsto_const_nhds.congr' hevent.symm)
    change (T - E) v = 0
    rw [ContinuousLinearMap.sub_apply, hT, heq]
    exact sub_self _
  have htop := KPCplxActualImageProof.closed_harmonic_exhaustion s U hclosed hall
  have hmem : f ∈ U := by rw [htop]; trivial
  have hTf : T f = E f := sub_eq_zero.mp hmem
  exact (hT f).symm.trans hTf

theorem harmonic_finiteSum_approximation (s : ℝ) (f : PrincipalSeries s) :
    ∃ a : ℕ → PrincipalSeries s,
      (∀ ℓ, a ℓ ∈ harmonicKType s ℓ) ∧
      Filter.Tendsto (fun N => ∑ ℓ ∈ Finset.range N, a ℓ)
        Filter.atTop (nhds f) := by
  classical
  obtain ⟨μ, hhaar, hprob⟩ := exists_su2_probability_haar
  refine ⟨fun ℓ => averageSection s μ hprob ℓ f, ?_, ?_⟩
  · intro ℓ
    obtain ⟨p, hp, he⟩ := characterAverage_compact_polynomial s μ hhaar hprob ℓ f
    exact Submodule.mem_map.mpr ⟨p, hp, funext he⟩
  · have h := (average_summable s μ hhaar hprob f).hasSum.tendsto_sum_nat
    rw [average_tsum_eq s μ hhaar hprob f] at h
    exact h

end DedekindZetaZeroFree.KPCplxInverseTopology

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartRemainder
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues MeasureTheory
open scoped BigOperators Topology

private lemma lowerUnipotent_zero_eq_identity : lowerUnipotent 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

private lemma principalSeries_identity_eval_norm_le_chartSeminorm_zero (s : ℝ) (f : PrincipalSeries s) :
    ‖f 1‖ ≤ chartSeminorm s 0 f := by
  have hc : Continuous (fun u : ℂ => ‖infinityCoordinate f u‖) :=
    f.property.2.2.continuous.norm
  have hb := (isCompact_closedBall (0 : ℂ) 1).image hc
  have hh : ‖infinityCoordinate f 0‖ ≤
      sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1) := by
    apply le_csSup hb.bddAbove
    exact ⟨0, by simp, rfl⟩
  change ‖f 1‖ ≤ chartSeminormValue s 0 f
  simpa only [chartSeminormValue, norm_iteratedFDeriv_zero, infinityCoordinate,
    lowerUnipotent_zero_eq_identity] using hh.trans (le_max_right
      (sSup ((fun x : ℂ => ‖openCoordinate f x‖) '' Metric.closedBall 0 1))
      (sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1)))

private lemma eval_one_continuous (s : ℝ) :
    Continuous (fun f : PrincipalSeries s => f 1) := by
  let e : PrincipalSeries s →ₗ[ℂ] ℂ :=
    { toFun := fun f => f 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply WithSeminorms.continuous_normedSpace_rng ℂ
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩) e
  refine ⟨{0}, 1, ?_⟩
  intro f
  simpa [e] using principalSeries_identity_eval_norm_le_chartSeminorm_zero s f

private lemma principalSeries_complexGL2_evaluation_continuous (s : ℝ) (g : ComplexGL2) :
    Continuous (fun f : PrincipalSeries s => f g) := by
  have h := (eval_one_continuous s).comp ((pi_continuous s).comp
    (continuous_const.prodMk continuous_id : Continuous (fun f : PrincipalSeries s =>
      (Matrix.ProjGenLinGroup.mk g, f))))
  have he : (fun f : PrincipalSeries s => pi s (Matrix.ProjGenLinGroup.mk g) f 1) =
      (fun f : PrincipalSeries s => f g) := by
    funext f
    change f (1 * g) = f g
    rw [one_mul]
  exact he ▸ h

private lemma embedding_continuous : Continuous complexSU2Embedding := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · have he (k : ComplexSU2) :
        (↑(complexSU2Embedding k)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) =
          star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← map_inv]
      rfl
    simp_rw [he]
    exact continuous_subtype_val.star

private lemma character_continuous (ℓ : ℕ) : Continuous (su2HarmonicCharacter ℓ) := by
  have htrace : ∀ n : ℕ, Continuous (fun k : ComplexSU2 =>
      KPCompactHarmonic.symmetricPowerTrace n
        ⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
          (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simpa [KPCompactHarmonic.symmetricPowerTrace] using
        (continuous_const : Continuous (fun _ : ComplexSU2 => (1 : ℂ)))
    | one => simp only [KPCompactHarmonic.symmetricPowerTrace]; fun_prop
    | more n hn hn1 =>
        simp only [KPCompactHarmonic.symmetricPowerTrace]
        exact ((by fun_prop : Continuous (fun k : ComplexSU2 =>
            Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℂ))).mul hn1).sub
          ((by fun_prop : Continuous (fun k : ComplexSU2 =>
            Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ))).mul hn)
  unfold su2HarmonicCharacter KPCompactHarmonic.rankOneCharacter
  simp only [(Matrix.mem_specialUnitaryGroup_iff.mp (Subtype.prop _)).2, one_pow, div_one]
  exact htrace (2 * ℓ)

private lemma average_continuous (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (ℓ : ℕ) (g : ComplexGL2) :
    Continuous (fun f : PrincipalSeries s => characterAverage s μ ℓ f g) := by
  letI : IsProbabilityMeasure μ := hprob
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  have hj : Continuous (fun p : PrincipalSeries s × ComplexSU2 =>
      p.1 (g * complexSU2Embedding p.2)) := by
    have hproj : Continuous (Matrix.ProjGenLinGroup.mk : ComplexGL2 → ComplexPGL2) :=
      continuous_coinduced_rng
    have h := (eval_one_continuous s).comp ((pi_continuous s).comp
      ((hproj.comp ((continuous_const : Continuous (fun _ : PrincipalSeries s × ComplexSU2 => g)).mul
          (embedding_continuous.comp continuous_snd))).prodMk
        continuous_fst))
    have he : (fun p : PrincipalSeries s × ComplexSU2 =>
        pi s (Matrix.ProjGenLinGroup.mk (g * complexSU2Embedding p.2)) p.1 1) =
        (fun p : PrincipalSeries s × ComplexSU2 => p.1 (g * complexSU2Embedding p.2)) := by
      funext p
      change p.1 (1 * (g * complexSU2Embedding p.2)) = _
      rw [one_mul]
    exact he ▸ h
  have hi : Continuous (fun f : PrincipalSeries s => ∫ t : ComplexSU2,
      star (su2HarmonicCharacter ℓ t) * f (g * complexSU2Embedding t) ∂μ) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
    · exact (((character_continuous ℓ).comp continuous_snd).star.mul hj).continuousOn
    · intro p x hp hx
      exact (hx (Set.mem_univ x)).elim
  exact continuous_const.mul hi

private lemma average_partialSum_harmonic (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (b : ℕ → PrincipalSeries s) (hb : ∀ ℓ, b ℓ ∈ harmonicKType s ℓ)
    (ℓ N : ℕ) (k : ComplexSU2) :
    characterAverage s μ ℓ (∑ j ∈ Finset.range N, b j) (complexSU2Embedding k) =
      if ℓ < N then b ℓ (complexSU2Embedding k) else 0 := by
  classical
  have hpol : ∀ j, ∃ p : MvPolynomial (Fin 3) ℂ,
      p ∈ harmonicPolynomials j ∧ polynomialCompactRestriction p = compactRestriction s (b j) := by
    intro j
    exact Submodule.mem_map.mp (hb j)
  choose p hp heq using hpol
  have hv (j : ℕ) (t : ComplexSU2) :
      b j (complexSU2Embedding t) = polynomialCompactRestriction (p j) t :=
    (congrFun (heq j) t).symm
  unfold characterAverage
  simp only [Submodule.coe_sum, Finset.sum_apply]
  simp_rw [← map_mul, hv]
  rw [CompactPolynomial.harmonic_character_projection μ hhaar hprob ℓ
    (Finset.range N) p (fun j _ => hp j) k]
  simp only [Finset.mem_range, ← hv]

theorem characterAverage_compact_partialSums_tendsto (s : ℝ)
    (μ : Measure ComplexSU2) (hhaar : μ.IsHaarMeasure)
    (hprob : IsProbabilityMeasure μ) (f : PrincipalSeries s)
    (a : ℕ → PrincipalSeries s)
    (ha : ∀ ℓ g, a ℓ g = characterAverage s μ ℓ f g) :
    ∀ k : ComplexSU2,
      Filter.Tendsto (fun N => (∑ ℓ ∈ Finset.range N, a ℓ) (complexSU2Embedding k))
        Filter.atTop (nhds (f (complexSU2Embedding k))) := by
  classical
  obtain ⟨b, hb, hlim⟩ := KPCplxInverseTopology.harmonic_finiteSum_approximation s f
  have hcoef (ℓ : ℕ) (k : ComplexSU2) :
      characterAverage s μ ℓ f (complexSU2Embedding k) = b ℓ (complexSU2Embedding k) := by
    have ht := ((average_continuous s μ hprob ℓ (complexSU2Embedding k)).tendsto f).comp hlim
    have hevent : (fun N => characterAverage s μ ℓ (∑ j ∈ Finset.range N, b j)
        (complexSU2Embedding k)) =ᶠ[Filter.atTop] (fun _ => b ℓ (complexSU2Embedding k)) := by
      filter_upwards [Filter.eventually_gt_atTop ℓ] with N hN
      rw [average_partialSum_harmonic s μ hhaar hprob b hb ℓ N k, if_pos hN]
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hevent.symm)
  have hab : a = b := by
    funext ℓ
    apply compactRestriction_injective s
    funext k
    exact (ha ℓ _).trans (hcoef ℓ k)
  rw [hab]
  intro k
  exact ((principalSeries_complexGL2_evaluation_continuous s (complexSU2Embedding k)).tendsto f).comp hlim

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.ChartRemainder

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open MeasureTheory
open scoped BigOperators Topology

theorem characterAverage_chart_remainder (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : PrincipalSeries s) (a : ℕ → PrincipalSeries s)
    (ha : ∀ ℓ g, a ℓ g = characterAverage s μ ℓ f g) (n : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in Filter.atTop,
      chartSeminorm s n ((∑ ℓ ∈ Finset.range N, a ℓ) - f) < ε := by
  exact ChartRemainder.chart_remainder_of_summable_of_compact_tendsto s f a
    (ChartRemainder.characterAverage_chartSeminorm_summable s μ hhaar hprob f a ha)
    (ChartRemainder.characterAverage_compact_partialSums_tendsto s μ hhaar hprob f a ha) n

end DedekindZetaZeroFree.KPCplxHarmonicExtraction

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open MeasureTheory Set
open scoped BigOperators Topology Matrix.Norms.Elementwise

theorem su2HarmonicCharacter_continuous (ℓ : ℕ) : Continuous (su2HarmonicCharacter ℓ) := by
  have htrace : ∀ n : ℕ, Continuous (fun k : ComplexSU2 =>
      KPCompactHarmonic.symmetricPowerTrace n
        ⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
          (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simpa [KPCompactHarmonic.symmetricPowerTrace] using
        (continuous_const : Continuous (fun _ : ComplexSU2 => (1 : ℂ)))
    | one => simp only [KPCompactHarmonic.symmetricPowerTrace]; fun_prop
    | more n hn hn1 =>
        simp only [KPCompactHarmonic.symmetricPowerTrace]
        exact ((by fun_prop : Continuous (fun k : ComplexSU2 => Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℂ))).mul hn1).sub
          ((by fun_prop : Continuous (fun k : ComplexSU2 => Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ))).mul hn)
  unfold su2HarmonicCharacter KPCompactHarmonic.rankOneCharacter
  simp only [(Matrix.mem_specialUnitaryGroup_iff.mp (Subtype.prop _)).2, one_pow, div_one]
  exact htrace (2 * ℓ)
private theorem matrixFunction_eval (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Matrix (Fin 2) (Fin 2) ℂ) = f g := by
  rw [matrixFunction, dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  apply Units.ext
  rfl

theorem principalSeries_su2_orbit_continuous (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2) :
    Continuous (fun k : ComplexSU2 => f (g * complexSU2Embedding k)) := by
  have hf := ((principalSeries_mem_iff s f).mp f.property).2.continuousOn
  have hm : Continuous (fun k : ComplexSU2 =>
      ((g * complexSU2Embedding k : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    change Continuous (fun k : ComplexSU2 =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))
    fun_prop
  have hc := hf.comp_continuous hm (fun k =>
    Matrix.GeneralLinearGroup.det_ne_zero (g * complexSU2Embedding k))
  simpa only [Function.comp_def, matrixFunction_eval] using hc

theorem characterAverage_integrable (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (ℓ : ℕ) (f : PrincipalSeries s) (g : ComplexGL2) :
    Integrable (fun k : ComplexSU2 =>
      star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k)) μ := by
  letI : IsProbabilityMeasure μ := hprob
  have hcompact : IsCompact (ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    have heq : Set.range (fun k : ComplexSU2 => (k : Matrix (Fin 2) (Fin 2) ℂ)) =
        (ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := Subtype.range_coe
    rw [← heq]
    exact complexSU2_isCompact
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp hcompact
  exact ((su2HarmonicCharacter_continuous ℓ).star.mul (principalSeries_su2_orbit_continuous s f g)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private lemma lower_zero : lowerUnipotent 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

private lemma eval_one_bound (s : ℝ) (f : PrincipalSeries s) : ‖f 1‖ ≤ chartSeminorm s 0 f := by
  have hc : Continuous (fun u : ℂ => ‖infinityCoordinate f u‖) := f.property.2.2.continuous.norm
  have hb := (isCompact_closedBall (0 : ℂ) 1).image hc
  have hh : ‖infinityCoordinate f 0‖ ≤ sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1) := by
    apply le_csSup hb.bddAbove
    exact ⟨0, by simp, rfl⟩
  change ‖f 1‖ ≤ chartSeminormValue s 0 f
  simpa only [chartSeminormValue, norm_iteratedFDeriv_zero, infinityCoordinate, lower_zero] using hh.trans (le_max_right
    (sSup ((fun x : ℂ => ‖openCoordinate f x‖) '' Metric.closedBall 0 1))
    (sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1)))

private lemma eval_one_cont (s : ℝ) : Continuous (fun f : PrincipalSeries s => f 1) := by
  let e : PrincipalSeries s →ₗ[ℂ] ℂ :=
    { toFun := fun f => f 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  apply WithSeminorms.continuous_normedSpace_rng ℂ (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩) e
  refine ⟨{0}, 1, ?_⟩
  intro f
  simpa [e] using eval_one_bound s f

theorem principalSeries_evaluation_continuous (s : ℝ) (g : ComplexGL2) :
    Continuous (fun f : PrincipalSeries s => f g) := by
  have h := (eval_one_cont s).comp ((pi_continuous s).comp
    (continuous_const.prodMk continuous_id : Continuous (fun f : PrincipalSeries s => (Matrix.ProjGenLinGroup.mk g, f))))
  have he : (fun f : PrincipalSeries s =>
      pi s (Matrix.ProjGenLinGroup.mk g) f 1) = (fun f : PrincipalSeries s => f g) := by
    funext f
    change f (1 * g) = f g
    rw [one_mul]
  exact he ▸ h

private lemma su2_embed_cont : Continuous complexSU2Embedding := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · have he (k : ComplexSU2) : (↑(complexSU2Embedding k)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
      have hk : complexSU2Embedding k⁻¹ = (complexSU2Embedding k)⁻¹ := map_inv _ _
      rw [← hk]
      rfl
    simp_rw [he]
    exact continuous_subtype_val.star

theorem principalSeries_su2_section_orbit_continuous (s : ℝ) (f : PrincipalSeries s) :
    Continuous (fun k : ComplexSU2 => rightTranslate s (complexSU2Embedding k) f) := by
  have hproj : Continuous (Matrix.ProjGenLinGroup.mk : ComplexGL2 → ComplexPGL2) :=
    continuous_coinduced_rng
  exact (pi_continuous s).comp ((hproj.comp su2_embed_cont).prodMk continuous_const)

theorem principalSeries_compact_barycenter_exists (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (F : ComplexSU2 → PrincipalSeries s)
    (hc : Continuous F) (hint : ∀ g, Integrable (fun k => F k g) μ) :
    ∃ v : PrincipalSeries s, v ∈ closure (convexHull ℝ (Set.range F)) ∧
      ∀ g, v g = ∫ k, F k g ∂μ := by
  classical
  letI : IsProbabilityMeasure μ := hprob
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI : T2Space (PrincipalSeries s) := principalSeries_t2 s
  letI : CompleteSpace (PrincipalSeries s) := principalSeries_complete s
  letI : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  letI : ContinuousSMul ℝ (PrincipalSeries s) := ⟨by
    have h := (continuous_smul : Continuous (fun p : ℂ × PrincipalSeries s => p.1 • p.2)).comp
      ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd)
    exact h⟩
  letI : LocallyConvexSpace ℝ (PrincipalSeries s) := principalSeries_locallyConvex s
  let C := closure (convexHull ℝ (Set.range F))
  have hCc : IsCompact C := ((isCompact_range hc).totallyBounded.convexHull.closure).isCompact_of_isComplete isClosed_closure.isComplete
  have hCv : Convex ℝ C := (convex_convexHull ℝ (Set.range F)).closure
  have hCF (k : ComplexSU2) : F k ∈ C := subset_closure (subset_convexHull ℝ _ ⟨k, rfl⟩)
  have hfin (u : Finset ComplexGL2) :
      (C ∩ ⋂ g ∈ u, {w : PrincipalSeries s | w g = ∫ k, F k g ∂μ}).Nonempty := by
    let E : PrincipalSeries s →ₗ[ℝ] (u → ℂ) :=
      { toFun := fun w g => w g.val
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hec : Continuous E := continuous_pi fun g => principalSeries_evaluation_continuous s g.val
    have hei : Integrable (fun k => E (F k)) μ := integrable_pi_iff.mpr (fun g => hint g.val)
    have hex : (∫ k, E (F k) ∂μ) ∈ E '' C :=
      (hCv.linear_image E).integral_mem (hCc.image hec).isClosed
        (Filter.Eventually.of_forall fun k => ⟨F k, hCF k, rfl⟩) hei
    obtain ⟨w, hwC, hw⟩ := hex
    refine ⟨w, hwC, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro g hg
    have hg' := congrFun hw ⟨g, hg⟩
    have hi := (ContinuousLinearMap.proj (R := ℝ) (i := (⟨g, hg⟩ : u))).integral_comp_comm hei
    change w g = (∫ k, E (F k) ∂μ) ⟨g, hg⟩ at hg'
    exact hg'.trans hi.symm
  obtain ⟨w, hwC, hw⟩ := hCc.inter_iInter_nonempty
    (fun g => {w : PrincipalSeries s | w g = ∫ k, F k g ∂μ})
    (fun g => isClosed_eq (principalSeries_evaluation_continuous s g) continuous_const) hfin
  exact ⟨w, hwC, fun g => Set.mem_iInter.mp hw g⟩

theorem characterAverage_section_exists (s : ℝ) (μ : Measure ComplexSU2)
    (hprob : IsProbabilityMeasure μ) (ℓ : ℕ) (f : PrincipalSeries s) :
    ∃ v : PrincipalSeries s, ∀ g, v g = characterAverage s μ ℓ f g := by
  let D : ℂ := ((2 * ℓ + 1 : ℕ) : ℂ)
  let F : ComplexSU2 → PrincipalSeries s := fun k =>
    (D * star (su2HarmonicCharacter ℓ k)) • rightTranslate s (complexSU2Embedding k) f
  letI : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  have hc : Continuous F :=
    (continuous_const.mul (su2HarmonicCharacter_continuous ℓ).star).smul
      (principalSeries_su2_section_orbit_continuous s f)
  have hF (k : ComplexSU2) (g : ComplexGL2) :
      F k g = D * (star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k)) := by
    change (D * star (su2HarmonicCharacter ℓ k)) * f (g * complexSU2Embedding k) = _
    exact mul_assoc _ _ _
  have hint : ∀ g, Integrable (fun k => F k g) μ := by
    intro g
    simp_rw [hF]
    exact (characterAverage_integrable s μ hprob ℓ f g).const_mul D
  obtain ⟨v, _, hv⟩ := principalSeries_compact_barycenter_exists s μ hprob F hc hint
  refine ⟨v, fun g => ?_⟩
  rw [hv g]
  simp_rw [hF]
  exact integral_const_mul D _

theorem character_average_harmonic_expansion (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : PrincipalSeries s) :
    ∃ a : ℕ → PrincipalSeries s,
      (∀ ℓ g, Integrable (fun k : ComplexSU2 =>
        star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k)) μ) ∧
      (∀ ℓ g, a ℓ g = characterAverage s μ ℓ f g) ∧
      (∀ ℓ, a ℓ ∈ harmonicKType s ℓ) ∧
      Filter.Tendsto (fun N => ∑ ℓ ∈ Finset.range N, a ℓ)
        Filter.atTop (nhds f) := by
  classical
  choose a ha using fun ℓ => characterAverage_section_exists s μ hprob ℓ f
  refine ⟨a, fun ℓ g => characterAverage_integrable s μ hprob ℓ f g,
    ha, ?_, ?_⟩
  · intro ℓ
    obtain ⟨p, hp, hpk⟩ := characterAverage_compact_polynomial s μ hhaar hprob ℓ f
    change compactRestriction s (a ℓ) ∈
      (harmonicPolynomials ℓ).map polynomialCompactRestriction
    refine ⟨p, hp, ?_⟩
    ext k
    exact (hpk k).trans ((ha ℓ (complexSU2Embedding k)).symm)
  · apply (WithSeminorms.tendsto_nhds
      (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩)
      (fun N => ∑ ℓ ∈ Finset.range N, a ℓ) f).mpr
    intro n ε hε
    exact characterAverage_chart_remainder s μ hhaar hprob f a ha n ε hε

end DedekindZetaZeroFree.KPCplxHarmonicExtraction

end
