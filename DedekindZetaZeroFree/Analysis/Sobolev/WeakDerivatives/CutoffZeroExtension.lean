module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.MultiIndexLeibnizRule

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior

open MeasureTheory KPContLocalNorm TopologicalSpace

structure GlobalWeakSobolev (n k : ℕ) where
  derivatives : MultiIndex n k → Lp ℂ 2 (volume : Measure (Space n))
  weak_derivatives : ∀ (α : MultiIndex n k)
    (φ : TestFunction (⊤ : Opens (Space n)) ℂ ⊤),
    (∫ x, derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x *
      coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree * (∫ x, derivatives α x * φ x)

open WeakJets.Raw Filter
open scoped Topology

private theorem list_smooth {n : ℕ} (l : List (Fin n)) {a : Space n → ℂ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l a) := by
  induction l with
  | nil => exact ha
  | cons i l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem list_support {n : ℕ} (l : List (Fin n)) (a : Space n → ℂ) :
    tsupport (coordinateDerivativeList l a) ⊆ tsupport a := by
  induction l with
  | nil => exact Set.Subset.rfl
  | cons i l ih => exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

private theorem list_congr {n : ℕ} (l : List (Fin n)) {a b : Space n → ℂ}
    {x : Space n} (hab : a =ᶠ[𝓝 x] b) :
    coordinateDerivativeList l a =ᶠ[𝓝 x] coordinateDerivativeList l b := by
  induction l with
  | nil => exact hab
  | cons i l ih =>
    exact (ih.fderiv (𝕜 := ℝ)).mono fun _ h =>
      congrArg (fun f : Space n →L[ℝ] ℂ => f (EuclideanSpace.single i 1)) h

private theorem jet_norm_le {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (γ : Counts n) : ‖jet u γ‖ ≤ u.sobolevNorm := by
  unfold jet
  split_ifs with hγ
  · apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (fun α _ => sq_nonneg ‖u.derivatives α‖) (Finset.mem_univ _)
  · simp only [norm_zero]
    exact Real.sqrt_nonneg _

 def extendedExpansion {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (l : List (Fin n)) (a : Space n → ℂ) (γ : Counts n) :
    Space n → ℂ := B.carrier.indicator (productExpansion u l a γ)

private theorem expansion_zero_off {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (l : List (Fin n)) (a : Space n → ℂ) (γ : Counts n)
    {x : Space n} (hx : x ∉ tsupport a) : productExpansion u l a γ x = 0 := by
  induction l generalizing a γ with
  | nil => simp [productExpansion, image_eq_zero_of_notMem_tsupport hx]
  | cons i l ih =>
    simp only [productExpansion, ih _ _ hx, ih _ _ (fun h => hx (list_support [i] a h)), add_zero]

private theorem expansion_bound {n : ℕ} (B : LocalBall n) (l : List (Fin n))
    (a : Space n → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hs : HasCompactSupport a) :
    ∃ C : ℝ, 0 < C ∧ ∀ k (u : IntegerSobolev B k) (γ : Counts n),
      ∃ h : MemLp (extendedExpansion u l a γ) 2 volume,
        ‖h.toLp (extendedExpansion u l a γ)‖ ≤ C * u.sobolevNorm := by
  induction l generalizing a with
  | nil =>
    obtain ⟨C, hC⟩ := ha.continuous.bounded_above_of_compact_support hs
    refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro k u γ
    let z := B.carrier.indicator (fun x => jet u γ x)
    have hz : MemLp z 2 volume :=
      (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet).2 (Lp.memLp _)
    have he : extendedExpansion u [] a γ = fun x => a x * z x := by
      funext x
      by_cases hx : x ∈ B.carrier <;> simp [extendedExpansion, productExpansion, z, hx]
    have hm : AEStronglyMeasurable (extendedExpansion u [] a γ) volume := by
      rw [he]
      exact ha.continuous.aestronglyMeasurable.mul hz.aestronglyMeasurable
    have hb : ∀ᵐ x ∂volume, ‖extendedExpansion u [] a γ x‖ ≤ max C 1 * ‖z x‖ := by
      filter_upwards [] with x
      rw [he, norm_mul]
      exact mul_le_mul_of_nonneg_right ((hC x).trans (le_max_left _ _)) (norm_nonneg _)
    let h := hz.of_le_mul hm hb
    refine ⟨h, ?_⟩
    have hnz : ‖hz.toLp z‖ = ‖jet u γ‖ := by
      rw [Lp.norm_toLp, Lp.norm_def]
      exact congrArg ENNReal.toReal (eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet)
    have hn := Lp.norm_le_mul_norm_of_ae_le_mul
      (f := h.toLp _) (g := hz.toLp z) (c := max C 1) (by
        filter_upwards [h.coeFn_toLp, hz.coeFn_toLp, hb] with x hx hy hb
        simpa only [hx, hy] using hb)
    rw [hnz] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left (jet_norm_le u γ) (le_max_of_le_right zero_le_one))
  | cons i l ih =>
    obtain ⟨C, hC, HC⟩ := ih (coordinateDerivativeList [i] a) (list_smooth [i] ha)
      (hs.of_isClosed_subset (isClosed_tsupport _) (list_support [i] a))
    obtain ⟨D, hD, HD⟩ := ih a ha hs
    refine ⟨C + D, add_pos hC hD, ?_⟩
    intro k u γ
    obtain ⟨h₁, H₁⟩ := HC k u γ
    obtain ⟨h₂, H₂⟩ := HD k u (γ + unitCount i)
    have he : extendedExpansion u (i :: l) a γ =
        extendedExpansion u l (coordinateDerivativeList [i] a) γ +
          extendedExpansion u l a (γ + unitCount i) := by
      funext x
      by_cases hx : x ∈ B.carrier <;> simp [extendedExpansion, productExpansion, hx]
    have h : MemLp (extendedExpansion u (i :: l) a γ) 2 volume := by
      rw [he]
      exact h₁.add h₂
    refine ⟨h, ?_⟩
    have heLp : h.toLp _ = h₁.toLp _ + h₂.toLp _ := by
      apply Lp.ext
      filter_upwards [h.coeFn_toLp, h₁.coeFn_toLp, h₂.coeFn_toLp, Lp.coeFn_add (h₁.toLp _) (h₂.toLp _)] with x hx h₁x h₂x hax
      rw [hx, hax]
      change _ = h₁.toLp _ x + h₂.toLp _ x
      rw [h₁x, h₂x, he]
      rfl
    rw [heLp]
    calc
      _ ≤ ‖h₁.toLp _‖ + ‖h₂.toLp _‖ := norm_add_le _ _
      _ ≤ C * u.sobolevNorm + D * u.sobolevNorm := add_le_add H₁ H₂
      _ = _ := (add_mul _ _ _).symm

private theorem localize_test {n : ℕ} (B : LocalBall n) (K : Set (Space n))
    (hK : IsClosed K) (hKB : K ⊆ B.carrier)
    (φ : TestFunction (⊤ : Opens (Space n)) ℂ ⊤) :
    ∃ ψ : TestFunction B.toOpens ℂ ⊤, ∀ x ∈ K,
      (fun y => ψ y) =ᶠ[𝓝 x] (fun y => φ y) := by
  obtain ⟨r, ⟨hr, hrB⟩, hKr⟩ := exists_pos_lt_subset_ball B.radius_pos hK hKB
  let η : ContDiffBump B.center :=
    ⟨r, (r + B.radius) / 2, hr, by linarith⟩
  let ψ : TestFunction B.toOpens ℂ ⊤ :=
    ⟨fun x => (η x : ℂ) * φ x,
      (Complex.ofRealCLM.contDiff.comp η.contDiff).mul φ.contDiff,
      φ.hasCompactSupport.mul_left, by
        apply (tsupport_mul_subset_left).trans
        have he : tsupport (fun x => (η x : ℂ)) = tsupport (fun x => η x) := by
          unfold tsupport
          congr 1
          ext x
          simp
        rw [he, η.tsupport_eq]
        exact Metric.closedBall_subset_ball (by change (r + B.radius) / 2 < B.radius; linarith)⟩
  refine ⟨ψ, ?_⟩
  intro x hx
  have hη := η.eventuallyEq_one_of_mem_ball (hKr hx)
  filter_upwards [hη] with y hy
  change (η y : ℂ) * φ y = φ y
  simp [hy]

private theorem extended_weak_rule {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (α : MultiIndex n k)
    (a : Space n → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hsub : tsupport a ⊆ B.carrier)
    (φ : TestFunction (⊤ : Opens (Space n)) ℂ ⊤) :
    (∫ x, extendedExpansion u [] a 0 x * coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree * (∫ x, extendedExpansion u α.directions a 0 x * φ x) := by
  obtain ⟨ψ, hψ⟩ := localize_test B (tsupport a) (isClosed_tsupport _) hsub φ
  have hleft : (fun x => extendedExpansion u [] a 0 x * coordinateDerivative α (fun y => φ y) x) =
      B.carrier.indicator (fun x => a x * jet u 0 x * coordinateDerivative α (fun y => ψ y) x) := by
    funext x
    by_cases hxB : x ∈ B.carrier
    · simp only [extendedExpansion, Set.indicator_of_mem hxB, productExpansion]
      by_cases hx : x ∈ tsupport a
      · exact congrArg (fun z => a x * jet u 0 x * z)
          ((list_congr α.directions (hψ x hx)).self_of_nhds).symm
      · simp [image_eq_zero_of_notMem_tsupport hx]
    · simp [extendedExpansion, hxB]
  have hright : (fun x => extendedExpansion u α.directions a 0 x * φ x) =
      B.carrier.indicator (fun x => productExpansion u α.directions a 0 x * ψ x) := by
    funext x
    by_cases hxB : x ∈ B.carrier
    · simp only [extendedExpansion, Set.indicator_of_mem hxB]
      by_cases hx : x ∈ tsupport a
      · exact congrArg (fun z => productExpansion u α.directions a 0 x * z)
          ((hψ x hx).self_of_nhds).symm
      · rw [expansion_zero_off u α.directions a 0 hx, zero_mul, zero_mul]
    · simp [extendedExpansion, hxB]
  rw [hleft, hright]
  simp only [integral_indicator (show MeasurableSet B.carrier from Metric.isOpen_ball.measurableSet)]
  exact weak_product_rule_uncollected u 0 α (by simpa [counts] using α.property) ha.contDiffOn ψ

theorem cutoff_global_weak_sobolev {n : ℕ} (B : LocalBall n) (k : ℕ)
    (χ : Space n → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hs : HasCompactSupport χ) (hsub : tsupport χ ⊆ B.carrier) :
    ∃ L : ℝ, 0 < L ∧ ∀ u : IntegerSobolev B k,
      ∃ g : GlobalWeakSobolev n k,
        ((fun x => g.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
          =ᵐ[volume] B.carrier.indicator
            (fun x => χ x • u.derivatives
              (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)) ∧
        (∀ α : MultiIndex n k, ∀ᵐ x ∂volume,
          x ∉ tsupport χ → g.derivatives α x = 0) ∧
        Real.sqrt (∑ α : MultiIndex n k, ‖g.derivatives α‖ ^ 2) ≤
          L * u.sobolevNorm := by
  classical
  let a : Space n → ℂ := fun x => (χ x : ℂ)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := Complex.ofRealCLM.contDiff.comp hχ
  have hsa : tsupport a = tsupport χ := by
    unfold tsupport
    congr 1
    ext x
    simp [a]
  have hca : HasCompactSupport a := by
    change IsCompact (tsupport a)
    rw [hsa]
    exact hs
  have hba : tsupport a ⊆ B.carrier := hsa ▸ hsub
  have hC : ∀ α : MultiIndex n k, ∃ C : ℝ, 0 < C ∧
      ∀ u : IntegerSobolev B k, ∃ h : MemLp (extendedExpansion u α.directions a 0) 2 volume,
        ‖h.toLp (extendedExpansion u α.directions a 0)‖ ≤ C * u.sobolevNorm := by
    intro α
    obtain ⟨C, hC, HC⟩ := expansion_bound B α.directions a ha hca
    exact ⟨C, hC, fun u => HC k u 0⟩
  choose C hC HC using hC
  let L : ℝ := 1 + ∑ α, C α
  have hsumC : 0 ≤ ∑ α, C α := Finset.sum_nonneg fun α _ => (hC α).le
  refine ⟨L, by dsimp [L]; linarith, ?_⟩
  intro u
  have HU := fun α => HC α u
  choose hm hnorm using HU
  let d : MultiIndex n k → Lp ℂ 2 (volume : Measure (Space n)) :=
    fun α => (hm α).toLp (extendedExpansion u α.directions a 0)
  have hd : ∀ α : MultiIndex n k,
      (fun x => d α x) =ᵐ[volume] extendedExpansion u α.directions a 0 :=
    fun α => (hm α).coeFn_toLp
  let z : MultiIndex n k := ⟨fun _ => 0, by simp⟩
  have hz : z.directions = [] := by simp [z, MultiIndex.directions]
  have hd0 : (fun x => d z x) =ᵐ[volume] extendedExpansion u [] a 0 := by
    simpa only [hz] using hd z
  let g : GlobalWeakSobolev n k :=
    ⟨d, by
      intro α φ
      have hl : (∫ x, d z x * coordinateDerivative α (fun y => φ y) x) =
          ∫ x, extendedExpansion u [] a 0 x * coordinateDerivative α (fun y => φ y) x := by
        apply integral_congr_ae
        filter_upwards [hd0] with x hx
        rw [hx]
      have hr : (∫ x, d α x * φ x) = ∫ x, extendedExpansion u α.directions a 0 x * φ x := by
        apply integral_congr_ae
        filter_upwards [hd α] with x hx
        rw [hx]
      exact hl.trans ((extended_weak_rule u α a ha hba φ).trans
        (congrArg (fun w => (-1 : ℂ) ^ α.degree * w) hr.symm))⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · change (fun x => d z x) =ᵐ[volume] _
    have he : extendedExpansion u [] a 0 = B.carrier.indicator
        (fun x => χ x • u.derivatives z x) := by
      funext x
      simp only [extendedExpansion, productExpansion, jet_zero]
      by_cases hx : x ∈ B.carrier
      · simp only [Set.indicator_of_mem hx]
        rfl
      · simp [hx]
    exact hd0.trans (ae_of_all _ (congrFun he))
  · intro α
    filter_upwards [hd α] with x hx hχx
    change d α x = 0
    rw [hx]
    have hax : x ∉ tsupport a := hsa ▸ hχx
    by_cases hxB : x ∈ B.carrier
    · simp only [extendedExpansion, Set.indicator_of_mem hxB]
      exact expansion_zero_off u α.directions a 0 hax
    · simp [extendedExpansion, hxB]
  · change Real.sqrt (∑ α, ‖d α‖ ^ 2) ≤ L * u.sobolevNorm
    have hn : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
    have hsum : (∑ α, ‖d α‖) ≤ (∑ α, C α) * u.sobolevNorm := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun α _ => hnorm α
    calc
      Real.sqrt (∑ α, ‖d α‖ ^ 2) ≤ ∑ α, ‖d α‖ :=
        Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun α _ => norm_nonneg _),
          Finset.sum_sq_le_sq_sum_of_nonneg (fun α _ => norm_nonneg _)⟩
      _ ≤ (∑ α, C α) * u.sobolevNorm := hsum
      _ ≤ L * u.sobolevNorm := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hn

end DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior

end
