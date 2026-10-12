module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation

open KPCplxPrincipalSeriesCharts
open scoped ContDiff
open Filter Topology Asymptotics

private theorem cutoff_open_zero (χ : ℂ → ℂ)
    (hχ : ∀ u : ℂ, (1/2 : ℝ) ≤ ‖u‖ → χ u = 0)
    (f : ℂ → ℂ) (x : ℂ) (hx : ‖x‖ < 2) :
    (if x = 0 then 0 else χ x⁻¹ * f x) = 0 := by
  split_ifs with h
  · rfl
  · rw [hχ x⁻¹, zero_mul]
    rw [norm_inv]
    have hp : 0 < ‖x‖ := norm_pos_iff.mpr h
    have : (2 : ℝ)⁻¹ ≤ ‖x‖⁻¹ := (inv_le_inv₀ (by norm_num) hp).2 hx.le
    norm_num at this ⊢
    exact this

theorem cutoff_section_exists (s : ℝ) (f : PrincipalSeries s) (χ : ℂ → ℂ)
    (hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ : ∀ u : ℂ, (1/2 : ℝ) ≤ ‖u‖ → χ u = 0) :
    ∃ h : PrincipalSeries s,
      infinityCoordinate h = (fun u => χ u * infinityCoordinate f u) ∧
      (∀ x : ℂ, ‖x‖ < 2 → openCoordinate h x = 0) := by
  let A : ℂ → ℂ := fun x => if x = 0 then 0 else χ x⁻¹ * openCoordinate f x
  have hA0 : ∀ x : ℂ, ‖x‖ < 2 → A x = 0 :=
    cutoff_open_zero χ hχ (openCoordinate f)
  have hAsmooth : ContDiff ℝ (⊤ : ℕ∞) A := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 2)] with x hx
      exact hA0 x (by simpa using hx)
    · have heq : A =ᶠ[𝓝 x] (fun x => χ x⁻¹ * openCoordinate f x) := by
        filter_upwards [eventually_ne_nhds hx] with y hy
        simp [A, hy]
      apply ((hχsmooth.contDiffAt.comp x (contDiffAt_inv ℝ hx)).mul
        f.property.2.1.contDiffAt).congr_of_eventuallyEq heq
  have hHsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun u => χ u * infinityCoordinate f u) :=
    hχsmooth.mul f.property.2.2
  have hext : ExtendsSmoothly s A := by
    refine ⟨hAsmooth, (fun u => χ u * infinityCoordinate f u), hHsmooth, ?_⟩
    intro u hu
    simp only [A, inv_eq_zero, hu, ↓reduceIte, inv_inv]
    rw [coordinate_transition s f u hu]
    ring
  obtain ⟨h, hh⟩ := (openCoordinate_range s A).2 hext
  refine ⟨h, ?_, ?_⟩
  · apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
      h.property.2.2.continuous hHsmooth.continuous
    intro u hu
    have hu' : u ≠ 0 := hu
    rw [coordinate_transition s h u hu', hh]
    simp only [A, inv_eq_zero, hu', ↓reduceIte, inv_inv]
    rw [coordinate_transition s f u hu']
    ring
  · intro x hx
    rw [hh]
    exact hA0 x hx

noncomputable def infinityCutoff (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℂ) :=
  ⟨r / 2, r, by positivity, by linarith⟩

theorem canonical_cutoff_approximant (s : ℝ) (f : PrincipalSeries s)
    (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1/2) :
    ∃ g : PrincipalSeries s,
      (∀ u : ℂ, ‖u‖ < r / 2 → infinityCoordinate g u = 0) ∧
      infinityCoordinate (f - g) =
        (fun u => ((infinityCutoff r hr u : ℝ) : ℂ) * infinityCoordinate f u) ∧
      (∀ x : ℂ, ‖x‖ < 2 → openCoordinate (f - g) x = 0) := by
  let b := infinityCutoff r hr
  let χ : ℂ → ℂ := fun u => (b u : ℂ)
  have hc : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hz : ∀ u : ℂ, (1/2 : ℝ) ≤ ‖u‖ → χ u = 0 := by
    intro u hu
    have hb : b u = 0 := b.zero_of_le_dist (by simpa [b, infinityCutoff] using hrsmall.trans hu)
    simp [χ, hb]
  obtain ⟨h, hinf, hop⟩ := cutoff_section_exists s f χ hc hz
  refine ⟨f - h, ?_, ?_, ?_⟩
  · intro u hu
    change infinityCoordinate f u - infinityCoordinate h u = 0
    rw [hinf]
    have hb : b u = 1 := b.one_of_mem_closedBall (by
      simpa [b, infinityCutoff] using hu.le)
    simp [χ, hb]
  · simpa using hinf
  · simpa using hop

theorem openCoordinate_derivatives_zero (s : ℝ) (h : PrincipalSeries s)
    (hop : ∀ x : ℂ, ‖x‖ < 2 → openCoordinate h x = 0)
    (n : ℕ) (x : ℂ) (hx : ‖x‖ ≤ 1) :
    iteratedFDeriv ℝ n (openCoordinate h) x = 0 := by
  have heq : openCoordinate h =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    have hn : ∀ᶠ y in 𝓝 x, ‖y‖ < 2 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖x‖ < (2 : ℝ) by linarith)
    filter_upwards [hn] with y hy using hop y hy
  simpa using (heq.iteratedFDeriv ℝ n).eq_of_nhds

theorem cutoff_chartSeminorm_eq (s : ℝ) (h : PrincipalSeries s)
    (hop : ∀ x : ℂ, ‖x‖ < 2 → openCoordinate h x = 0) (n : ℕ) :
    chartSeminorm s n h =
      sSup ((fun u : ℂ => ‖iteratedFDeriv ℝ n (infinityCoordinate h) u‖) ''
        Metric.closedBall (0 : ℂ) 1) := by
  have hopen : (fun x : ℂ => ‖iteratedFDeriv ℝ n (openCoordinate h) x‖) ''
      Metric.closedBall (0 : ℂ) 1 = {0} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_singleton_iff]
      rw [openCoordinate_derivatives_zero s h hop n x (by simpa using hx), norm_zero]
    · rintro y rfl
      exact ⟨0, by simp, by simp [openCoordinate_derivatives_zero s h hop n 0 (by simp)]⟩
  have hb : BddAbove ((fun u : ℂ => ‖iteratedFDeriv ℝ n (infinityCoordinate h) u‖) ''
      Metric.closedBall (0 : ℂ) 1) := by
    apply (isCompact_closedBall (0 : ℂ) 1).bddAbove_image
    exact (h.property.2.2.continuous_iteratedFDeriv (by simp)).norm.continuousOn
  have hnn : 0 ≤ sSup ((fun u : ℂ => ‖iteratedFDeriv ℝ n (infinityCoordinate h) u‖) ''
      Metric.closedBall (0 : ℂ) 1) :=
    le_csSup_of_le hb (Set.mem_image_of_mem _ (by simp : (0 : ℂ) ∈ Metric.closedBall 0 1))
      (norm_nonneg _)
  change max _ _ = _
  rw [hopen, csSup_singleton, max_eq_right hnn]

theorem jet_flat_bigO (H : ℂ → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (n : ℕ) (hflat : ∀ k ≤ n, iteratedFDeriv ℝ k H 0 = 0)
    (k p : ℕ) (hkp : k + p ≤ n + 1) :
    (iteratedFDeriv ℝ k H) =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ p) := by
  induction p generalizing k with
  | zero =>
    simpa using (hH.continuous_iteratedFDeriv (m := k) (by simp)).continuousAt.tendsto.isBigO_one ℝ
  | succ p ih =>
    have hk : k ≤ n := by omega
    have hd := ih (k+1) (by omega)
    have hd' : fderiv ℝ (iteratedFDeriv ℝ k H) =O[𝓝 (0 : ℂ)]
        (fun u : ℂ => ‖u‖ ^ (p : ℝ)) := by
      rw [Asymptotics.isBigO_iff] at hd ⊢
      obtain ⟨C, hC⟩ := hd
      refine ⟨C, ?_⟩
      simpa only [norm_fderiv_iteratedFDeriv, Real.rpow_natCast] using hC
    have result := isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero
      (f := iteratedFDeriv ℝ k H) (a := (0 : ℂ)) (r := (p : ℝ))
      (by positivity) (Filter.Eventually.of_forall (fun u =>
        (hH.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast ENat.coe_lt_top k)).differentiableAt))
      (by simpa using hd') (hflat k hk)
    simpa only [sub_zero, ← Nat.cast_add_one, Real.rpow_natCast] using result

private theorem infinityCutoff_scale (r : ℝ) (hr : 0 < r) :
    (infinityCutoff r hr : ℂ → ℝ) =
      (fun u => infinityCutoff 1 (by norm_num) (r⁻¹ • u)) := by
  funext u
  simp only [ContDiffBump.apply, infinityCutoff, sub_zero, smul_smul]
  have hratio : r / (r / 2) = 1 / (1 / 2 : ℝ) := by field_simp
  have hscale : (r / 2)⁻¹ = (1 / (1 / 2 : ℝ)) * r⁻¹ := by field_simp
  rw [hratio, hscale]
  norm_num

theorem infinityCutoff_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r) (u : ℂ),
      ‖iteratedFDeriv ℝ j (infinityCutoff r hr) u‖ ≤ C * (r⁻¹)^j := by
  let b := infinityCutoff 1 (by norm_num)
  have hc : Continuous (iteratedFDeriv ℝ j (b : ℂ → ℝ)) :=
    b.contDiff.continuous_iteratedFDeriv (by simp : (j : ℕ∞ω) ≤ (⊤ : ℕ∞))
  have hs := b.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) j
  have hb := (hs.isCompact_range hc).isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr u
  rw [infinityCutoff_scale r hr, iteratedFDeriv_comp_const_smul r⁻¹
    (b.contDiff (n := (j : ℕ∞)))]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (r⁻¹)^j * max C 0 := mul_le_mul_of_nonneg_left
      ((hC _ (Set.mem_range_self (r⁻¹ • u))).trans (le_max_left _ _)) (by positivity)
    _ = _ := mul_comm _ _

private theorem finite_uniform_bound {ι : Type*} (I : Finset ι) (a b : ι → ℂ → ℝ)
    (hb : ∀ i u, 0 ≤ b i u)
    (h : ∀ i ∈ I, ∃ C : ℝ, ∀ᶠ u in 𝓝 (0 : ℂ), a i u ≤ C * b i u) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u in 𝓝 (0 : ℂ), ∀ i ∈ I, a i u ≤ C * b i u := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨C, hC, hCI⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨D, hD⟩ := h i (by simp)
    refine ⟨max C D, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    filter_upwards [hCI, hD] with u hu hdu
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hdu.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hb j u))
    · exact (hu j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hb j u))

theorem jet_flat_uniform_bound (H : ℂ → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (n : ℕ) (hflat : ∀ k ≤ n, iteratedFDeriv ℝ k H 0 = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (k : ℕ), k ≤ n → ∀ u : ℂ,
      ‖u‖ < δ → ‖iteratedFDeriv ℝ k H u‖ ≤ C * ‖u‖^(n+1-k) := by
  obtain ⟨C, hC, hb⟩ := finite_uniform_bound (Finset.range (n+1))
    (fun k u => ‖iteratedFDeriv ℝ k H u‖) (fun k u => ‖u‖^(n+1-k))
    (by intros; positivity) (by
      intro k hk
      have hk' : k ≤ n := by simpa using hk
      have hO := jet_flat_bigO H hH n hflat k (n+1-k) (by omega)
      rw [Asymptotics.isBigO_iff] at hO
      obtain ⟨D, hD⟩ := hO
      refine ⟨D, ?_⟩
      filter_upwards [hD] with u hu
      simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ ‖u‖^(n+1-k))] using hu)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro k hk u hu
  exact hd (by simpa using hu) k (by simpa using hk)

theorem canonical_cutoff_derivative_decay (H : ℂ → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (j : ℕ)
    (hflat : ∀ k ≤ j, iteratedFDeriv ℝ k H 0 = 0) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ r : ℝ, ∀ hr : 0 < r, r < δ → ∀ u : ℂ,
      ‖iteratedFDeriv ℝ j (fun v => ((infinityCutoff r hr v : ℝ) : ℂ) * H v) u‖
        ≤ A * r := by
  classical
  obtain ⟨C, δ, hC, hδ, hjet⟩ := jet_flat_uniform_bound H hH j hflat
  choose D hD using infinityCutoff_derivative_bound
  let A : ℝ := ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * D i * C
  have hA : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hD i).1) hC.le
  refine ⟨A+1, δ, by linarith, hδ, ?_⟩
  intro r hr hrδ u
  let b := infinityCutoff r hr
  let χ : ℂ → ℂ := fun v => (b v : ℂ)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  by_cases hu : ‖u‖ ≤ r
  · have hb : ∀ i : ℕ, ‖iteratedFDeriv ℝ i χ u‖ ≤ D i * r⁻¹^i := by
      intro i
      have heq : ‖iteratedFDeriv ℝ i χ u‖ = ‖iteratedFDeriv ℝ i (b : ℂ → ℝ) u‖ := by
        exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left
          (b.contDiff (n := (i : ℕ∞))).contDiffAt le_rfl
      rw [heq]
      exact (hD i).2 r hr u
    have hprod := norm_iteratedFDeriv_mul_le hχ hH u (n := j) (by simp)
    apply le_trans hprod
    calc
      _ ≤ ∑ i ∈ Finset.range (j+1), ((j.choose i : ℝ) * D i * C) * r := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := by simpa using hi
        have hp := hjet (j-i) (by omega) u (lt_of_le_of_lt hu hrδ)
        have hexp : j+1-(j-i) = i+1 := by omega
        rw [hexp] at hp
        have hp' : ‖iteratedFDeriv ℝ (j-i) H u‖ ≤ C * r^(i+1) :=
          hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) hu _) hC.le)
        calc
          _ ≤ (j.choose i : ℝ) * (D i * r⁻¹^i) * (C * r^(i+1)) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (hb i) (Nat.cast_nonneg _))
              hp' (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (hD i).1 (by positivity)))
          _ = ((j.choose i : ℝ) * D i * C) * r := by
            have hpow : r⁻¹^i * r^(i+1) = r := by
              rw [pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]
            calc
              _ = ((j.choose i : ℝ) * D i * C) * (r⁻¹^i * r^(i+1)) := by ring
              _ = _ := by rw [hpow]
      _ = A * r := by rw [← Finset.sum_mul]
      _ ≤ (A+1)*r := by nlinarith
  · have hz : (fun v => χ v * H v) =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
      have hevent : ∀ᶠ v in 𝓝 u, r < ‖v‖ :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds (lt_of_not_ge hu)
      filter_upwards [hevent] with v hv
      have hb : b v = 0 := b.zero_of_le_dist (by simpa [b, infinityCutoff] using hv.le)
      simp [χ, hb]
    have heq := (hz.iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ j (fun v => χ v * H v) u‖ ≤ (A+1)*r
    rw [heq]
    simpa using (show (0 : ℝ) ≤ (A+1)*r by positivity)

theorem cutoff_chartSeminorm_le (s : ℝ) (h : PrincipalSeries s)
    (hop : ∀ x : ℂ, ‖x‖ < 2 → openCoordinate h x = 0) (j : ℕ) (B : ℝ)
    (hB : ∀ u : ℂ, ‖iteratedFDeriv ℝ j (infinityCoordinate h) u‖ ≤ B) :
    chartSeminorm s j h ≤ B := by
  rw [cutoff_chartSeminorm_eq s h hop j]
  apply csSup_le
  · exact ⟨_, Set.mem_image_of_mem _ (by simp : (0 : ℂ) ∈ Metric.closedBall 0 1)⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hB u

theorem finite_seminorm_cutoff_approximation (s : ℝ) (F : Finset ℕ) :
    ∃ n : ℕ, ∀ f : PrincipalSeries s,
      (∀ k ≤ n, iteratedFDeriv ℝ k (infinityCoordinate f) 0 = 0) →
      ∀ ε : ℝ, 0 < ε → ∃ g : PrincipalSeries s,
        (∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → infinityCoordinate g u = 0) ∧
        (F.sup (chartSeminorm s)) (f - g) < ε := by
  classical
  refine ⟨F.sup id, ?_⟩
  intro f hf ε hε
  have hj : ∀ j ∈ F, ∀ᶠ r : ℝ in 𝓝 0, ∀ hr : 0 < r, ∀ u : ℂ,
      ‖iteratedFDeriv ℝ j (fun v => ((infinityCutoff r hr v : ℝ) : ℂ) * infinityCoordinate f v) u‖ ≤ ε/2 := by
    intro j hj
    obtain ⟨A, δ, hA, hδ, hb⟩ := canonical_cutoff_derivative_decay _ f.property.2.2 j
      (fun k hk => hf k (hk.trans (Finset.le_sup (f := id) hj)))
    have hlim : ∀ᶠ r : ℝ in 𝓝 0, r < δ ∧ r < ε / (2*A) := by
      apply Filter.Eventually.and
      · exact ((isOpen_lt continuous_id continuous_const).mem_nhds hδ)
      · exact ((isOpen_lt continuous_id continuous_const).mem_nhds (show (0 : ℝ) < ε / (2*A) by positivity))
    filter_upwards [hlim] with r hr
    intro hrpos u
    apply (hb r hrpos hr.1 u).trans
    have ha := (lt_div_iff₀ (by positivity : 0 < 2*A)).mp hr.2
    nlinarith
  have hall := F.eventually_all.mpr hj
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hall
  let r : ℝ := min (δ/2) (1/4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsmall : r ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hrδ : dist r 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨g, hzero, hinf, hopen⟩ := canonical_cutoff_approximant s f r hr hrsmall
  refine ⟨g, ⟨r/2, by positivity, hzero⟩, ?_⟩
  have hbound : ∀ j ∈ F, chartSeminorm s j (f-g) ≤ ε/2 := by
    intro j hj
    apply cutoff_chartSeminorm_le s (f-g) hopen j (ε/2)
    intro u
    change ‖iteratedFDeriv ℝ j (infinityCoordinate ((f : KPCplxCharacterHaar.ComplexGL2 → ℂ) - g)) u‖ ≤ ε/2
    rw [hinf]
    exact hball hrδ j hj hr u
  have hsup : (F.sup (chartSeminorm s)) (f-g) ≤ ε/2 := by
    have hgen : ∀ I : Finset ℕ, (∀ j ∈ I, chartSeminorm s j (f-g) ≤ ε/2) →
        (I.sup (chartSeminorm s)) (f-g) ≤ ε/2 := by
      intro I hI
      induction I using Finset.induction_on with
      | empty => simpa using (show (0 : ℝ) ≤ ε/2 by positivity)
      | @insert j I hj ih =>
        rw [Finset.sup_insert, Seminorm.sup_apply]
        exact max_le (hI j (by simp)) (ih (fun k hk => hI k (by simp [hk])))
    exact hgen F hbound
  linarith

end DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation
