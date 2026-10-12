module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Complex.ParameterMajorantData

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts Set
open scoped ContDiff Matrix.Norms.Elementwise

lemma seminorm_bddAbove (j : ℕ) (φ : ComplexProjectiveLine → ℂ)
    (hop : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity)) :
    BddAbove ({0} ∪ {r : ℝ | ∃ q : ℕ, q ≤ j ∧ ∃ z : ℂ,
      z ∈ Metric.closedBall (0 : ℂ) 1 ∧
        (r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ∨
         r = ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖)}) := by
  have hb : ∀ q : ℕ, BddAbove
      ((fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖) '' Metric.closedBall 0 1 ∪
       (fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖) '' Metric.closedBall 0 1) := by
    intro q
    apply BddAbove.union
    · exact (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
        (hop.continuous_iteratedFDeriv (by simp)).norm.continuousOn
    · exact (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
        (hinf.continuous_iteratedFDeriv (by simp)).norm.continuousOn
  have hfin : BddAbove (⋃ q ∈ Finset.range (j + 1),
      ((fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖) '' Metric.closedBall 0 1 ∪
       (fun z : ℂ => ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖) '' Metric.closedBall 0 1)) := by
    exact (Finset.finite_toSet _).bddAbove_biUnion.mpr (fun q _ => hb q)
  apply BddAbove.union bddAbove_singleton
  apply hfin.mono
  rintro r ⟨q, hq, z, hz, hr⟩
  apply mem_iUnion₂.mpr
  refine ⟨q, Finset.mem_range.mpr (by omega), ?_⟩
  rcases hr with rfl | rfl
  · exact Or.inl ⟨z, hz, rfl⟩
  · exact Or.inr ⟨z, hz, rfl⟩

lemma seminorm_nonneg (j : ℕ) (φ : ComplexProjectiveLine → ℂ)
    (hop : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity)) :
    0 ≤ seminorm j φ := by
  unfold seminorm
  exact le_csSup (seminorm_bddAbove j φ hop hinf) (Or.inl (mem_singleton 0))

lemma norm_iteratedFDeriv_chart_le_seminorm (j q : ℕ) (hq : q ≤ j)
    (φ : ComplexProjectiveLine → ℂ)
    (hop : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity))
    (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) :
    ‖iteratedFDeriv ℝ q (φ ∘ projectiveOpen) z‖ ≤ seminorm j φ ∧
    ‖iteratedFDeriv ℝ q (φ ∘ projectiveInfinity) z‖ ≤ seminorm j φ := by
  constructor
  · exact le_csSup (seminorm_bddAbove j φ hop hinf) (Or.inr ⟨q, hq, z, hz, Or.inl rfl⟩)
  · exact le_csSup (seminorm_bddAbove j φ hop hinf) (Or.inr ⟨q, hq, z, hz, Or.inr rfl⟩)

lemma norm_operatorApply_le {n j : ℕ}
    (c : (q : Fin (j + 1)) → (Fin q.val → Fin n) → (Fin n → ℝ) → ℂ)
    (f : (Fin n → ℝ) → ℂ) (u : Fin n → ℝ) (B : ℝ)
    (hB : ∀ q : Fin (j + 1), ‖iteratedFDeriv ℝ q.val f u‖ ≤ B) :
    ‖operatorApply c f u‖ ≤ (∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n, ‖c q a u‖) * B := by
  classical
  unfold operatorApply
  calc
    ‖∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n,
        c q a u * iteratedFDeriv ℝ q.val f u (fun i => Pi.single (a i) (1 : ℝ))‖
      ≤ ∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n,
          ‖c q a u‖ * B := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro q _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro a _
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa using (iteratedFDeriv ℝ q.val f u).le_mul_prod_of_opNorm_le_of_le (hB q)
          (show ∀ i : Fin q.val, ‖Pi.single (a i) (1 : ℝ)‖ ≤ (1 : ℝ) by
            intro i; simp [Pi.norm_single])
    _ = (∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n, ‖c q a u‖) * B := by
      simp only [Finset.sum_mul]

lemma compact_coefficient_sum_bound {n j : ℕ}
    (U K : Set (Fin n → ℝ)) (hK : IsCompact K) (hKU : K ⊆ U)
    (c : (q : Fin (j + 1)) → (Fin q.val → Fin n) → (Fin n → ℝ) → ℂ)
    (hc : ∀ q a, ContDiffOn ℝ (⊤ : ℕ∞) (c q a) U) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ K,
      (∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n, ‖c q a u‖) ≤ A := by
  classical
  have hcont : ContinuousOn
      (fun u => ∑ q : Fin (j + 1), ∑ a : Fin q.val → Fin n, ‖c q a u‖) K := by
    apply continuousOn_finset_sum
    intro q _
    apply continuousOn_finset_sum
    intro a _
    exact ((hc q a).continuousOn.mono hKU).norm
  obtain ⟨A, hA⟩ := hK.bddAbove_image hcont
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro u hu
  exact (hA ⟨u, hu, rfl⟩).trans (le_max_left _ _)

lemma norm_local_chart_composition_le {n : ℕ} (j q : ℕ) (hq : q ≤ j)
    (φ : ComplexProjectiveLine → ℂ)
    (hop : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveOpen))
    (hinf : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ projectiveInfinity))
    (V : Set (Fin n → ℝ)) (hV : IsOpen V) (u : Fin n → ℝ) (hu : u ∈ V)
    (z : (Fin n → ℝ) → ℂ) (hz : ContDiffOn ℝ (⊤ : ℕ∞) z V)
    (hzu : z u ∈ Metric.closedBall 0 1) (D : ℝ)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ q → ‖iteratedFDeriv ℝ i z u‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ q ((φ ∘ projectiveOpen) ∘ z) u‖ ≤
      q.factorial * seminorm j φ * D ^ q ∧
    ‖iteratedFDeriv ℝ q ((φ ∘ projectiveInfinity) ∘ z) u‖ ≤
      q.factorial * seminorm j φ * D ^ q := by
  have hzat : ContDiffAt ℝ (⊤ : ℕ∞) z u := hz.contDiffAt (hV.mem_nhds hu)
  have hwithin : ∀ i : ℕ, iteratedFDerivWithin ℝ i z V u = iteratedFDeriv ℝ i z u := by
    intro i
    exact iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn
      (hzat.of_le (by simp)) hu
  have hbound (g : ℂ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgi : ∀ i ≤ q, ‖iteratedFDeriv ℝ i g (z u)‖ ≤ seminorm j φ) :
      ‖iteratedFDeriv ℝ q (g ∘ z) u‖ ≤ q.factorial * seminorm j φ * D ^ q := by
    have he : iteratedFDerivWithin ℝ q (g ∘ z) V u = iteratedFDeriv ℝ q (g ∘ z) u :=
      iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn
        ((hg.contDiffAt.comp u hzat).of_le (by simp)) hu
    rw [← he]
    apply norm_iteratedFDerivWithin_comp_le hg.contDiffOn hz (by simp)
      uniqueDiffOn_univ hV.uniqueDiffOn (mapsTo_univ _ _) hu
    · simpa only [iteratedFDerivWithin_univ] using hgi
    · intro i hi hiq
      rw [hwithin]
      exact hD i hi hiq
  constructor
  · apply hbound _ hop
    intro i hi
    exact (norm_iteratedFDeriv_chart_le_seminorm j i (hi.trans hq) φ hop hinf (z u) hzu).1
  · apply hbound _ hinf
    intro i hi
    exact (norm_iteratedFDeriv_chart_le_seminorm j i (hi.trans hq) φ hop hinf (z u) hzu).2

lemma compact_iteratedFDeriv_power_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : E → F) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ j →
      ∀ u ∈ K, ‖iteratedFDeriv ℝ i f u‖ ≤ D ^ i := by
  have hcont : ∀ i : ℕ, ContinuousOn (fun u => ‖iteratedFDeriv ℝ i f u‖) K := by
    intro i
    have heq : EqOn (iteratedFDerivWithin ℝ i f U) (iteratedFDeriv ℝ i f) U := by
      intro u hu
      exact iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        ((hf.contDiffAt (hU.mem_nhds hu)).of_le (by simp)) hu
    exact (((hf.continuousOn_iteratedFDerivWithin (by simp) hU.uniqueDiffOn).congr
      (fun u hu => (heq hu).symm)).mono hKU).norm
  have hb : BddAbove (⋃ i ∈ Finset.range (j + 1),
      (fun u => ‖iteratedFDeriv ℝ i f u‖) '' K) :=
    (Finset.finite_toSet _).bddAbove_biUnion.mpr (fun i _ => hK.bddAbove_image (hcont i))
  obtain ⟨A, hA⟩ := hb
  refine ⟨max A 1, le_max_right _ _, ?_⟩
  intro i hi hij u hu
  have hAi : ‖iteratedFDeriv ℝ i f u‖ ≤ A :=
    hA (mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr (by omega), ⟨u, hu, rfl⟩⟩)
  apply hAi.trans
  apply (le_max_left A 1).trans
  exact le_self_pow₀ (le_max_right A 1) (by omega)

end DedekindZetaZeroFree.RepresentationTheory.KPComplexIntertwinerParameterMajorant
