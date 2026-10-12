module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Complex.ProjectiveChartSeminormBounds

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped ContDiff Matrix.Norms.Elementwise

open Set

namespace SourceJets

noncomputable def actedRow {n : ℕ} (k : (Fin n → ℝ) → ComplexGL2)
    (p : (Fin 2 → ℂ) × (Fin n → ℝ)) (i : Fin 2) : ℂ :=
  ∑ a : Fin 2, p.1 a * (k p.2 : Matrix (Fin 2) (Fin 2) ℂ) a i

lemma actedRow_contDiffOn {n : ℕ} (U : Set (Fin n → ℝ))
    (k : (Fin n → ℝ) → ComplexGL2)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (k u : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (i : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => actedRow k p i) (univ ×ˢ U) := by
  unfold actedRow
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.mul
  · exact ((contDiff_apply ℝ ℂ a).comp contDiff_fst).contDiffOn
  · have he : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun u => (k u : Matrix (Fin 2) (Fin 2) ℂ) a i) U :=
      ((contDiff_apply ℝ ℂ i).contDiffOn.comp
        ((contDiff_apply ℝ (Fin 2 → ℂ) a).contDiffOn.comp hk (mapsTo_univ _ _))
        (mapsTo_univ _ _))
    exact he.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)

lemma rowRatio_contDiffOn {n : ℕ} (U : Set (Fin n → ℝ))
    (k : (Fin n → ℝ) → ComplexGL2)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (k u : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (a b : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p => actedRow k p a / actedRow k p b)
      ((univ ×ˢ U) ∩ {p | actedRow k p b ≠ 0}) := by
  simp only [div_eq_mul_inv]
  apply ((actedRow_contDiffOn U k hk a).mono inter_subset_left).mul
  exact (contDiffOn_inv ℝ).comp
    ((actedRow_contDiffOn U k hk b).mono inter_subset_left)
    (fun _ hp => by simpa using hp.2)

lemma compact_rowRatio_power_bound {n : ℕ} (j : ℕ)
    (U K : Set (Fin n → ℝ)) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (k : (Fin n → ℝ) → ComplexGL2)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (k u : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (T : Set (Fin 2 → ℂ)) (hT : IsCompact T) (δ : ℝ) (hδ : 0 < δ)
    (a b : Fin 2) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ j →
      ∀ p ∈ (T ×ˢ K) ∩ {p | δ ≤ ‖actedRow k p b‖},
        ‖iteratedFDeriv ℝ i (fun p => actedRow k p a / actedRow k p b) p‖ ≤ D ^ i := by
  have hcont : ContinuousOn (fun p => ‖actedRow k p b‖) (T ×ˢ K) :=
    ((actedRow_contDiffOn U k hk b).continuousOn.mono
      (prod_mono (subset_univ T) hKU)).norm
  have hclosed : IsClosed ((T ×ˢ K) ∩ {p | δ ≤ ‖actedRow k p b‖}) :=
    hcont.preimage_isClosed_of_isClosed (hT.prod hK).isClosed isClosed_Ici
  have hcompact : IsCompact ((T ×ˢ K) ∩ {p | δ ≤ ‖actedRow k p b‖}) :=
    (hT.prod hK).of_isClosed_subset hclosed inter_subset_left
  have hopen : IsOpen ((univ ×ˢ U) ∩ {p | actedRow k p b ≠ 0}) :=
    (actedRow_contDiffOn U k hk b).continuousOn.isOpen_inter_preimage
      (isOpen_univ.prod hU) isOpen_ne
  apply compact_iteratedFDeriv_power_bound j _ _ hopen hcompact _ _
    (rowRatio_contDiffOn U k hk a b)
  intro p hp
  refine ⟨⟨mem_univ _, hKU hp.1.2⟩, ?_⟩
  intro he
  have : δ ≤ ‖actedRow k p b‖ := hp.2
  rw [he, norm_zero] at this
  exact (not_le_of_gt hδ) this

private lemma slice_derivative_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (V : Set (E × F)) (hV : IsOpen V) (f : E × F → G)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (r : E) (u : F)
    (hu : (r, u) ∈ V) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun v => f (r, v)) u‖ ≤
      ‖iteratedFDeriv ℝ i f (r, u)‖ := by
  let L : F →L[ℝ] E × F := ContinuousLinearMap.inr ℝ E F
  let a : E × F := (r, 0)
  let W : Set (E × F) := (fun p => p + a) ⁻¹' V
  have hW : IsOpen W := hV.preimage (continuous_id.add continuous_const)
  have hf' : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => f (p + a)) W :=
    hf.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hp => hp)
  have hLu : L u ∈ W := by simpa [L, W, a] using hu
  have he := L.iteratedFDerivWithin_comp_right hf' hW.uniqueDiffOn
    (hW.preimage L.continuous).uniqueDiffOn hLu (i := i) (by simp)
  have hleft : iteratedFDerivWithin ℝ i ((fun p => f (p + a)) ∘ L) (L ⁻¹' W) u =
      iteratedFDeriv ℝ i (fun v => f (r, v)) u := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv
      (hW.preimage L.continuous).uniqueDiffOn
      (((hf'.comp_continuousLinearMap L).contDiffAt
        ((hW.preimage L.continuous).mem_nhds hLu)).of_le (by simp)) hLu]
    congr 1
    funext v
    simp [L, a]
  have hright : iteratedFDerivWithin ℝ i (fun p => f (p + a)) W (L u) =
      iteratedFDeriv ℝ i f (r, u) := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
      ((hf'.contDiffAt (hW.mem_nhds hLu)).of_le (by simp)) hLu,
      iteratedFDeriv_comp_add_right]
    simp [L, a]
  rw [hleft, hright] at he
  rw [he]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏ b : Fin i, ‖L‖) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro b _; exact norm_nonneg _
    · intro b _; exact ContinuousLinearMap.norm_inr_le_one ℝ E F
  simpa using mul_le_mul_of_nonneg_left hp
    (norm_nonneg (iteratedFDeriv ℝ i f (r, u)))

private lemma line_row_form (x : ℂ) (k : ComplexGL2) :
    line (weyl * upperUnipotent x * k) =
      if (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + x * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
      then projectiveInfinity 0
      else projectiveOpen (((k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 +
        x * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) /
        ((k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + x * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
  simp [line, weyl, upperUnipotent, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two]

 noncomputable def rowLine {n : ℕ} (k : (Fin n → ℝ) → ComplexGL2)
    (r : Fin 2 → ℂ) (u : Fin n → ℝ) : ComplexProjectiveLine :=
  if actedRow k (r, u) 0 = 0 then projectiveInfinity 0
  else projectiveOpen (actedRow k (r, u) 1 / actedRow k (r, u) 0)

private lemma rowLine_infinity {n : ℕ} (k : (Fin n → ℝ) → ComplexGL2)
    (r : Fin 2 → ℂ) (u : Fin n → ℝ) (h : actedRow k (r, u) 1 ≠ 0) :
    rowLine k r u = projectiveInfinity (actedRow k (r, u) 0 / actedRow k (r, u) 1) := by
  unfold rowLine
  split_ifs with h0
  · simp [h0]
  · rw [projective_chart_transition _ (div_ne_zero h0 h), inv_div]

private lemma normalized_line {n : ℕ} (k : (Fin n → ℝ) → ComplexGL2)
    (x : ℂ) (hx : x ≠ 0) (u : Fin n → ℝ) :
    line (weyl * upperUnipotent x * k u) =
      rowLine k ![x⁻¹, 1] u := by
  rw [line_row_form]
  have he (i : Fin 2) : (k u : Matrix (Fin 2) (Fin 2) ℂ) 0 i +
      x * (k u : Matrix (Fin 2) (Fin 2) ℂ) 1 i = x * actedRow k (![x⁻¹, 1], u) i := by
    simp [actedRow, Fin.sum_univ_two]
    field_simp
  rw [he 0, he 1]
  simp [rowLine, hx, mul_div_mul_left]

private lemma unnormalized_line {n : ℕ} (k : (Fin n → ℝ) → ComplexGL2)
    (x : ℂ) (u : Fin n → ℝ) :
    line (weyl * upperUnipotent x * k u) =
      rowLine k ![1, x] u := by
  rw [line_row_form]
  simp [rowLine, actedRow, Fin.sum_univ_two]

private lemma rowRatio_slice_bound {n : ℕ} (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (k : (Fin n → ℝ) → ComplexGL2)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (k u : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (r : Fin 2 → ℂ) (u : Fin n → ℝ) (hu : u ∈ U) (a b : Fin 2)
    (hb : actedRow k (r, u) b ≠ 0) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun v => actedRow k (r, v) a / actedRow k (r, v) b) u‖ ≤
      ‖iteratedFDeriv ℝ i (fun p => actedRow k p a / actedRow k p b) (r, u)‖ := by
  apply slice_derivative_le ((univ ×ˢ U) ∩ {p | actedRow k p b ≠ 0}) _ _
    (rowRatio_contDiffOn U k hk a b) r u ⟨⟨mem_univ _, hu⟩, hb⟩ i
  exact (actedRow_contDiffOn U k hk b).continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod hU) isOpen_ne

private lemma rowLine_derivative_bound {n : ℕ} (j q : ℕ) (hq : q ≤ j)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (k : (Fin n → ℝ) → ComplexGL2)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (k u : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (φ : ComplexProjectiveLine → ℂ)
    (hop : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity))
    (r : Fin 2 → ℂ) (u : Fin n → ℝ) (hu : u ∈ U)
    (δ : ℝ) (hδ : 0 < δ)
    (hr : δ ≤ ‖actedRow k (r, u) 0‖ ∨ δ ≤ ‖actedRow k (r, u) 1‖) (D : ℝ)
    (hD : ∀ a b : Fin 2, δ ≤ ‖actedRow k (r, u) b‖ →
      ∀ i : ℕ, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i (fun p => actedRow k p a / actedRow k p b) (r, u)‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ q (fun v => φ (rowLine k r v)) u‖ ≤
      q.factorial * seminorm j φ * D ^ q := by
  have hchart (a b : Fin 2) (hb : δ ≤ ‖actedRow k (r, u) b‖)
      (hab : ‖actedRow k (r, u) a‖ ≤ ‖actedRow k (r, u) b‖) :
      ∃ V : Set (Fin n → ℝ), IsOpen V ∧ u ∈ V ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun v => actedRow k (r, v) a / actedRow k (r, v) b) V ∧
        (actedRow k (r, u) a / actedRow k (r, u) b) ∈ Metric.closedBall 0 1 ∧
        (∀ i : ℕ, 1 ≤ i → i ≤ q →
          ‖iteratedFDeriv ℝ i (fun v => actedRow k (r, v) a / actedRow k (r, v) b) u‖ ≤ D ^ i) ∧
        V ⊆ {v | actedRow k (r, v) b ≠ 0} := by
    have hbn : actedRow k (r, u) b ≠ 0 := by
      intro he; rw [he, norm_zero] at hb; exact (not_le_of_gt hδ) hb
    let V := U ∩ {v | actedRow k (r, v) b ≠ 0}
    have hvcont : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => actedRow k (r, v) b) U :=
      (actedRow_contDiffOn U k hk b).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun v hv => ⟨mem_univ _, hv⟩)
    have hvopen : IsOpen V := hvcont.continuousOn.isOpen_inter_preimage hU isOpen_ne
    have hz : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun v => actedRow k (r, v) a / actedRow k (r, v) b) V :=
      (rowRatio_contDiffOn U k hk a b).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun v hv => ⟨⟨mem_univ _, hv.1⟩, hv.2⟩)
    refine ⟨V, hvopen, ⟨hu, hbn⟩, hz, ?_, ?_, inter_subset_right⟩
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_div]
      exact (div_le_one (norm_pos_iff.mpr hbn)).mpr hab
    · intro i hi hiq
      exact (rowRatio_slice_bound U hU k hk r u hu a b hbn i).trans (hD a b hb i hi hiq)
  by_cases h01 : ‖actedRow k (r, u) 1‖ ≤ ‖actedRow k (r, u) 0‖
  · have hb : δ ≤ ‖actedRow k (r, u) 0‖ := by
      rcases hr with hr | hr
      · exact hr
      · exact hr.trans h01
    obtain ⟨V, hV, huV, hz, hzu, hDz, hVb⟩ := hchart 1 0 hb h01
    have he : (fun v => φ (rowLine k r v)) =ᶠ[nhds u]
        ((φ ∘ projectiveOpen) ∘ (fun v => actedRow k (r, v) 1 / actedRow k (r, v) 0)) := by
      filter_upwards [hV.mem_nhds huV] with v hv
      have hvb : actedRow k (r, v) 0 ≠ 0 := hVb hv
      simp [rowLine, hvb, Function.comp_def]
    rw [(he.iteratedFDeriv ℝ q).self_of_nhds]
    exact (norm_local_chart_composition_le j q hq φ hop hinf V hV u huV _ hz hzu D hDz).1
  · have h10 : ‖actedRow k (r, u) 0‖ ≤ ‖actedRow k (r, u) 1‖ := le_of_lt (lt_of_not_ge h01)
    have hb : δ ≤ ‖actedRow k (r, u) 1‖ := by
      rcases hr with hr | hr
      · exact hr.trans h10
      · exact hr
    obtain ⟨V, hV, huV, hz, hzu, hDz, hVb⟩ := hchart 0 1 hb h10
    have he : (fun v => φ (rowLine k r v)) =ᶠ[nhds u]
        ((φ ∘ projectiveInfinity) ∘ (fun v => actedRow k (r, v) 0 / actedRow k (r, v) 1)) := by
      filter_upwards [hV.mem_nhds huV] with v hv
      simp only [Function.comp_apply, rowLine_infinity k r v (hVb hv)]
    rw [(he.iteratedFDeriv ℝ q).self_of_nhds]
    exact (norm_local_chart_composition_le j q hq φ hop hinf V hV u huV _ hz hzu D hDz).2

private lemma actedRow_ne_zero {n : ℕ} (k : (Fin n → ℝ) → ComplexGL2)
    (r : Fin 2 → ℂ) (u : Fin n → ℝ) (hr : r ≠ 0) : actedRow k (r,u) ≠ 0 := by
  intro he
  have hvec : Matrix.vecMul r (k u : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.vecMul 0 (k u : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i
    have hi := congrFun he i
    simpa [Matrix.vecMul, dotProduct, actedRow] using hi
  exact hr (Matrix.vecMul_injective_of_isUnit (Units.isUnit (k u)) hvec)

private lemma rowLine_smooth {n : ℕ}
    (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (k : (Fin n → ℝ) → ComplexGL2)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => (k u : Matrix (Fin 2) (Fin 2) ℂ)) U)
    (φ : ComplexProjectiveLine → ℂ)
    (hop : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity))
    (r : Fin 2 → ℂ) (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun u => φ (rowLine k r u)) U := by
  intro u hu
  have hchart (a b : Fin 2) (hb : actedRow k (r,u) b ≠ 0) :
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v => actedRow k (r,v) a / actedRow k (r,v) b) u ∧
      ∀ᶠ v in nhds u, actedRow k (r,v) b ≠ 0 := by
    let V := U ∩ {v | actedRow k (r,v) b ≠ 0}
    have hvcont : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => actedRow k (r,v) b) U :=
      (actedRow_contDiffOn U k hk b).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun v hv => ⟨mem_univ _, hv⟩)
    have hV : IsOpen V := hvcont.continuousOn.isOpen_inter_preimage hU isOpen_ne
    have hz : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun v => actedRow k (r,v) a / actedRow k (r,v) b) V :=
      (rowRatio_contDiffOn U k hk a b).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun v hv => ⟨⟨mem_univ _, hv.1⟩, hv.2⟩)
    refine ⟨hz.contDiffAt (hV.mem_nhds ⟨hu, hb⟩), ?_⟩
    filter_upwards [hV.mem_nhds ⟨hu,hb⟩] with v hv
    exact hv.2
  by_cases h0 : actedRow k (r,u) 0 = 0
  · have h1 : actedRow k (r,u) 1 ≠ 0 := by
      intro h1
      apply actedRow_ne_zero k r u hr
      ext i; fin_cases i <;> simp [h0,h1]
    obtain ⟨hz, he⟩ := hchart 0 1 h1
    apply ((hinf.contDiffAt.comp u hz).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [he] with v hv
    simp only [Function.comp_apply, rowLine_infinity k r v hv]
  · obtain ⟨hz, he⟩ := hchart 1 0 h0
    apply ((hop.contDiffAt.comp u hz).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [he] with v hv
    simp [rowLine, hv, Function.comp_def]

end SourceJets

theorem compact_projective_source_jets (n j : ℕ)
    (U K : Set (Fin n → ℝ)) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g : (Fin n → ℝ) → ComplexGL2)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v => (g v : Matrix (Fin 2) (Fin 2) ℂ)) U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (φ : ComplexProjectiveLine → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen) →
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity) →
      ∀ x : ℂ,
        ContDiffOn ℝ (⊤ : ℕ∞) (fun v => φ (line (weyl * upperUnipotent x * g v))) U ∧
        ∀ q ≤ j, ∀ u ∈ K,
          ‖iteratedFDeriv ℝ q (fun v => φ (line (weyl * upperUnipotent x * g v))) u‖ ≤
            B * seminorm j φ := by
  classical
  let T : Set (Fin 2 → ℂ) := Metric.closedBall 0 1 ∩ {r | 1 ≤ ‖r‖}
  have hT : IsCompact T := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hcont : ContinuousOn
      (fun p => max ‖SourceJets.actedRow g p 0‖ ‖SourceJets.actedRow g p 1‖) (T ×ˢ K) :=
    fun p hp => (((SourceJets.actedRow_contDiffOn U g hg 0).continuousOn.mono
      (prod_mono (subset_univ T) hKU)).norm p hp).max
      (((SourceJets.actedRow_contDiffOn U g hg 1).continuousOn.mono
      (prod_mono (subset_univ T) hKU)).norm p hp)
  obtain ⟨δ, hδ, hδb⟩ := (hT.prod hK).exists_forall_le' hcont (a := 0) (by
    intro p hp
    have hr : p.1 ≠ 0 := by
      intro he
      have hh := hp.1.2
      have hh' : (1 : ℝ) ≤ 0 := by simpa [he, T] using hh
      norm_num at hh'
    have hn := SourceJets.actedRow_ne_zero g p.1 p.2 hr
    by_contra hm
    have h0 : SourceJets.actedRow g p 0 = 0 := norm_eq_zero.mp
      (le_antisymm ((le_max_left _ _).trans (le_of_not_gt hm)) (norm_nonneg _))
    have h1 : SourceJets.actedRow g p 1 = 0 := norm_eq_zero.mp
      (le_antisymm ((le_max_right _ _).trans (le_of_not_gt hm)) (norm_nonneg _))
    apply hn
    ext i; fin_cases i <;> simp [h0,h1])
  have hex : ∀ a b : Fin 2, ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ j →
      ∀ p ∈ (T ×ˢ K) ∩ {p | δ ≤ ‖SourceJets.actedRow g p b‖},
        ‖iteratedFDeriv ℝ i (fun p => SourceJets.actedRow g p a / SourceJets.actedRow g p b) p‖ ≤ D ^ i := by
    intro a b
    exact SourceJets.compact_rowRatio_power_bound j U K hU hK hKU g hg T hT δ hδ a b
  choose Ds hDs hDsb using hex
  let D : ℝ := max 1 (∑ a : Fin 2, ∑ b : Fin 2, Ds a b)
  have hD : 1 ≤ D := le_max_left _ _
  have hDsD : ∀ a b, Ds a b ≤ D := by
    intro a b
    apply le_trans _ (le_max_right _ _)
    apply le_trans (Finset.single_le_sum (fun b _ => (by linarith [hDs a b])) (Finset.mem_univ b))
    exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => by linarith [hDs a b]))
      (Finset.mem_univ a)
  refine ⟨(j.factorial : ℝ) * D ^ j, by positivity, ?_⟩
  intro φ hop hinf x
  have hsem : 0 ≤ seminorm j φ := seminorm_nonneg j φ hop hinf
  have hrow (r : Fin 2 → ℂ) (hrT : r ∈ T) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun v => φ (SourceJets.rowLine g r v)) U ∧
      ∀ q ≤ j, ∀ u ∈ K,
        ‖iteratedFDeriv ℝ q (fun v => φ (SourceJets.rowLine g r v)) u‖ ≤
          ((j.factorial : ℝ) * D ^ j) * seminorm j φ := by
    have hr : r ≠ 0 := by
      intro he
      have hh := hrT.2
      have hh' : (1 : ℝ) ≤ 0 := by simpa [he, T] using hh
      norm_num at hh'
    refine ⟨SourceJets.rowLine_smooth U hU g hg φ hop hinf r hr, ?_⟩
    intro q hq u hu
    apply (SourceJets.rowLine_derivative_bound j q hq U hU g hg φ hop hinf r u
      (hKU hu) δ hδ (le_max_iff.mp (hδb (r,u) ⟨hrT,hu⟩)) D ?_).trans
    · have hf : (q.factorial : ℝ) ≤ j.factorial := by
        exact_mod_cast Nat.factorial_le hq
      have hp : D ^ q ≤ D ^ j := pow_le_pow_right₀ hD hq
      calc
        (q.factorial : ℝ) * seminorm j φ * D ^ q ≤
            (j.factorial : ℝ) * seminorm j φ * D ^ j := by gcongr
        _ = ((j.factorial : ℝ) * D ^ j) * seminorm j φ := by ring
    · intro a b hb i hi hiq
      exact (hDsb a b i hi (hiq.trans hq) (r,u) ⟨⟨hrT,hu⟩,hb⟩).trans
        (pow_le_pow_left₀ (by linarith [hDs a b]) (hDsD a b) i)
  by_cases hx : ‖x‖ ≤ 1
  · have hrT : (![1,x] : Fin 2 → ℂ) ∈ T := by
      constructor
      · simp only [Metric.mem_closedBall, dist_zero_right]
        apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
        intro i; fin_cases i <;> simp [hx]
      · simpa using (norm_le_pi_norm (![1,x] : Fin 2 → ℂ) 0)
    simpa only [SourceJets.unnormalized_line] using hrow ![1,x] hrT
  · have hxn : x ≠ 0 := by intro he; simp [he] at hx
    have hxi : ‖x⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hx))
    have hrT : (![x⁻¹,1] : Fin 2 → ℂ) ∈ T := by
      constructor
      · simp only [Metric.mem_closedBall, dist_zero_right]
        apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
        intro i; fin_cases i
        · simpa using hxi
        · simp
      · simpa using (norm_le_pi_norm (![x⁻¹,1] : Fin 2 → ℂ) 1)
    simpa only [SourceJets.normalized_line g x hxn] using hrow ![x⁻¹,1] hrT

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant.MatrixWeighted
