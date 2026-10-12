module

public import DedekindZetaZeroFree.Adeles.Quotients.Sobolev.WeightedIntegralAction

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace DedekindZetaZeroFree

open KPCompactInteriorH1

private theorem act_inv_act {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (γ : Γ) {x : E n} (hx : x ∈ D.chart) :
    D.act γ⁻¹ (D.act γ x) = x := by
  have h := D.act_mul γ⁻¹ γ x hx
  rw [inv_mul_cancel, D.act_one x hx] at h
  exact h.symm

private theorem average_eq_zero_off {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r) (hu : tsupport u ⊆ D.chart)
    {x : E n} (hx : x ∉ ⋃ γ : Γ, D.act γ⁻¹ '' tsupport u) :
    KPChartL2.average n r Γ D.chart D.act D.cocycle u x = 0 := by
  classical
  by_cases hxc : x ∈ D.chart
  · rw [KPChartL2.average, Set.indicator_of_mem hxc]
    have hz : ∀ γ : Γ, u (D.act γ x) = 0 := by
      intro γ
      by_contra hnz
      exact hx (Set.mem_iUnion.mpr
        ⟨γ, D.act γ x, subset_closure hnz, act_inv_act D γ hxc⟩)
    simp [hz]
  · rw [KPChartL2.average, Set.indicator_of_notMem hxc]

private theorem tsupport_average_subset {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r)
    (hcomp : HasCompactSupport u) (hu : tsupport u ⊆ D.chart) :
    tsupport (KPChartL2.average n r Γ D.chart D.act D.cocycle u) ⊆
      ⋃ γ : Γ, D.act γ⁻¹ '' tsupport u := by
  have hKc : IsCompact (⋃ γ : Γ, D.act γ⁻¹ '' tsupport u) :=
    isCompact_iUnion fun γ =>
      hcomp.image_of_continuousOn ((D.smooth_action γ⁻¹).continuousOn.mono hu)
  refine closure_minimal (fun x hx => ?_) hKc.isClosed
  by_contra hxK
  exact hx (average_eq_zero_off D u hu hxK)

private theorem contDiff_average {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r)
    (hu : ContDiff ℝ ∞ u) (hcomp : HasCompactSupport u) (hsup : tsupport u ⊆ D.chart) :
    ContDiff ℝ ∞ (KPChartL2.average n r Γ D.chart D.act D.cocycle u) := by
  classical
  have hKc : IsCompact (⋃ γ : Γ, D.act γ⁻¹ '' tsupport u) :=
    isCompact_iUnion fun γ =>
      hcomp.image_of_continuousOn ((D.smooth_action γ⁻¹).continuousOn.mono hsup)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ (⋃ γ : Γ, D.act γ⁻¹ '' tsupport u)
  · have hxchart : x ∈ D.chart := by
      obtain ⟨γ, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact D.act_mem γ⁻¹ y (hsup hy)
    have hon : ContDiffOn ℝ ∞
        (KPChartL2.average n r Γ D.chart D.act D.cocycle u) D.chart :=
      (kp_cont_chart_equivariant_average_smooth n r hn hr Γ D u
        hu.contDiffOn hcomp hsup).1
    exact hon.contDiffAt (D.open_chart.mem_nhds hxchart)
  · have hev : KPChartL2.average n r Γ D.chart D.act D.cocycle u =ᶠ[nhds x]
        fun _ => (0 : V r) := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact average_eq_zero_off D u hsup hy
    exact (contDiffAt_const (c := (0 : V r))).congr_of_eventuallyEq hev

private theorem tsupport_average_subset_invariant {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r) (hcomp : HasCompactSupport u)
    (O : Set (E n)) (hOchart : O ⊆ D.chart)
    (hOinv : ∀ (γ : Γ) (x : E n), x ∈ O → D.act γ x ∈ O)
    (hsupO : tsupport u ⊆ O) :
    tsupport (KPChartL2.average n r Γ D.chart D.act D.cocycle u) ⊆ O := by
  refine (tsupport_average_subset D u hcomp (hsupO.trans hOchart)).trans ?_
  intro x hx
  obtain ⟨γ, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  exact hOinv γ⁻¹ y (hsupO hy)

private theorem inverse_cocycle' {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (γ : Γ) {x : E n} (hx : x ∈ D.chart) (v : V r) :
    (D.cocycle γ x).symm v = D.cocycle γ⁻¹ (D.act γ x) v := by
  have hc := D.cocycle_mul γ⁻¹ γ x hx ((D.cocycle γ x).symm v)
  simpa [D.cocycle_one x hx] using hc

private theorem contDiffOn_inverse_cocycle_apply {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (γ : Γ) :
    ContDiffOn ℝ ∞ (fun p : E n × V r => (D.cocycle γ p.1).symm p.2)
      (D.chart ×ˢ Set.univ) := by
  have hact : ContDiffOn ℝ ∞ (fun p : E n × V r => D.act γ p.1)
      (D.chart ×ˢ Set.univ) :=
    (D.smooth_action γ).comp contDiffOn_fst (fun p hp => hp.1)
  have hpair : ContDiffOn ℝ ∞ (fun p : E n × V r => (D.act γ p.1, p.2))
      (D.chart ×ˢ Set.univ) := hact.prodMk contDiffOn_snd
  have hcc : ContDiffOn ℝ ∞ (fun p : E n × V r => D.cocycle γ⁻¹ p.1 p.2)
      (D.chart ×ˢ Set.univ) := D.smooth_cocycle γ⁻¹
  exact (hcc.comp hpair (fun p hp => ⟨D.act_mem γ p.1 hp.1, Set.mem_univ _⟩)).congr
    (fun p hp => inverse_cocycle' D γ hp.1 p.2)

private theorem hasFDerivAt_average_term {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (γ : Γ) (u : E n → V r) (hu : ContDiff ℝ ∞ u)
    {x : E n} (hx : x ∈ D.chart) :
    HasFDerivAt (fun y => (D.cocycle γ y).symm (u (D.act γ y)))
      ((fderiv ℝ (fun p : E n × V r => (D.cocycle γ p.1).symm p.2)
          (x, u (D.act γ x))).comp
        (fderiv ℝ (fun y => (y, u (D.act γ y))) x)) x := by
  have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hΨ : HasFDerivAt (fun p : E n × V r => (D.cocycle γ p.1).symm p.2)
      (fderiv ℝ (fun p : E n × V r => (D.cocycle γ p.1).symm p.2)
        (x, u (D.act γ x))) (x, u (D.act γ x)) :=
    (((contDiffOn_inverse_cocycle_apply D γ).contDiffAt
        ((D.open_chart.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ _⟩)).differentiableAt
      hn0).hasFDerivAt
  have hdact : HasFDerivAt (D.act γ) (fderiv ℝ (D.act γ) x) x :=
    (((D.smooth_action γ).contDiffAt (D.open_chart.mem_nhds hx)).differentiableAt
      hn0).hasFDerivAt
  have hdu : HasFDerivAt u (fderiv ℝ u (D.act γ x)) (D.act γ x) :=
    ((hu.differentiable hn0) (D.act γ x)).hasFDerivAt
  have hcomp2 : HasFDerivAt (fun y => u (D.act γ y))
      ((fderiv ℝ u (D.act γ x)).comp (fderiv ℝ (D.act γ) x)) x :=
    HasFDerivAt.comp x hdu hdact
  have hg : HasFDerivAt (fun y => (y, u (D.act γ y)))
      ((1 : E n →L[ℝ] E n).prod
        ((fderiv ℝ u (D.act γ x)).comp (fderiv ℝ (D.act γ) x))) x :=
    (hasFDerivAt_id x).prodMk hcomp2
  have h := HasFDerivAt.comp x hΨ hg
  rw [hg.fderiv]
  exact h

private theorem norm_average_le {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r) {x : E n} (hx : x ∈ D.chart) :
    ‖KPChartL2.average n r Γ D.chart D.act D.cocycle u x‖ ≤
      (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, ‖u (D.act γ x)‖ := by
  rw [KPChartL2.average, Set.indicator_of_mem hx, norm_smul, norm_inv,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∑ γ : Γ, (D.cocycle γ x).symm (u (D.act γ x))‖
      ≤ ∑ γ : Γ, ‖(D.cocycle γ x).symm (u (D.act γ x))‖ := norm_sum_le _ _
    _ = ∑ γ : Γ, ‖u (D.act γ x)‖ := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [LinearIsometryEquiv.norm_map]

private theorem fderiv_average {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r) (hu : ContDiff ℝ ∞ u)
    {x : E n} (hx : x ∈ D.chart) :
    fderiv ℝ (KPChartL2.average n r Γ D.chart D.act D.cocycle u) x =
      (Fintype.card Γ : ℂ)⁻¹ •
        ∑ γ : Γ, fderiv ℝ (fun y => (D.cocycle γ y).symm (u (D.act γ y))) x := by
  have hev : KPChartL2.average n r Γ D.chart D.act D.cocycle u =ᶠ[nhds x]
      (fun y => (Fintype.card Γ : ℂ)⁻¹ •
        ∑ γ : Γ, (D.cocycle γ y).symm (u (D.act γ y))) := by
    filter_upwards [D.open_chart.mem_nhds hx] with y hy
    rw [KPChartL2.average, Set.indicator_of_mem hy]
  have hterm : ∀ γ ∈ (Finset.univ : Finset Γ),
      HasFDerivAt (fun y => (D.cocycle γ y).symm (u (D.act γ y)))
        (fderiv ℝ (fun y => (D.cocycle γ y).symm (u (D.act γ y))) x) x := by
    intro γ _
    have h := hasFDerivAt_average_term D γ u hu hx
    rw [← h.fderiv] at h
    exact h
  have hfin := (HasFDerivAt.fun_sum hterm).const_smul (Fintype.card Γ : ℂ)⁻¹
  exact ((hev.hasFDerivAt_iff).mpr hfin).fderiv

private theorem norm_average_sq_le {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r) {x : E n} (hx : x ∈ D.chart) :
    ‖KPChartL2.average n r Γ D.chart D.act D.cocycle u x‖ ^ 2 ≤
      (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, ‖u (D.act γ x)‖ ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos
  have h := norm_average_le D u hx
  have hR : 0 ≤ (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, ‖u (D.act γ x)‖ :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun γ _ => norm_nonneg _)
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans ?_
  have hsq : (∑ γ : Γ, ‖u (D.act γ x)‖) ^ 2 ≤
      (Fintype.card Γ : ℝ) * ∑ γ : Γ, ‖u (D.act γ x)‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun γ : Γ => ‖u (D.act γ x)‖)
  calc ((Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, ‖u (D.act γ x)‖) ^ 2
      = (Fintype.card Γ : ℝ)⁻¹ ^ 2 * (∑ γ : Γ, ‖u (D.act γ x)‖) ^ 2 := by
        rw [mul_pow]
    _ ≤ (Fintype.card Γ : ℝ)⁻¹ ^ 2 *
          ((Fintype.card Γ : ℝ) * ∑ γ : Γ, ‖u (D.act γ x)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, ‖u (D.act γ x)‖ ^ 2 := by
        field_simp

private theorem norm_fderiv_average_le {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r) (hu : ContDiff ℝ ∞ u)
    {x : E n} (hx : x ∈ D.chart) (j : Fin n) :
    ‖fderiv ℝ (KPChartL2.average n r Γ D.chart D.act D.cocycle u) x
        (coordinateDirection j)‖ ≤
      (Fintype.card Γ : ℝ)⁻¹ *
        ∑ γ : Γ, ‖fderiv ℝ (fun y => (D.cocycle γ y).symm (u (D.act γ y))) x
          (coordinateDirection j)‖ := by
  rw [fderiv_average D u hu hx, ContinuousLinearMap.smul_apply, norm_smul, norm_inv,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [ContinuousLinearMap.sum_apply]
  exact norm_sum_le _ _

 noncomputable def inverseOperator {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (γ : Γ) (x : E n) : V r →L[ℝ] V r :=
  (D.cocycle γ x).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

private theorem contDiffOn_inverseOperator {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (γ : Γ) :
    ContDiffOn ℝ ∞ (inverseOperator D γ) D.chart := by
  apply contDiffOn_clm_apply.mpr
  intro v
  exact (contDiffOn_inverse_cocycle_apply D γ).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx, Set.mem_univ _⟩)

private theorem exists_differential_bounds {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (C : Set (E n)) (hC : IsCompact C) (hCchart : C ⊆ D.chart) :
    ∃ A K : ℝ, 1 ≤ A ∧ 1 ≤ K ∧ ∀ γ x, x ∈ C →
      ‖fderiv ℝ (D.act γ) x‖ ≤ A ∧ ‖fderiv ℝ (inverseOperator D γ) x‖ ≤ K := by
  classical
  have hact : ∀ γ : Γ, ∃ A : ℝ, ∀ x ∈ C, ‖fderiv ℝ (D.act γ) x‖ ≤ A := fun γ =>
    hC.exists_bound_of_continuousOn
      (((D.smooth_action γ).continuousOn_fderiv_of_isOpen D.open_chart (by simp)).mono hCchart)
  have hinv : ∀ γ : Γ, ∃ K : ℝ, ∀ x ∈ C, ‖fderiv ℝ (inverseOperator D γ) x‖ ≤ K := fun γ =>
    hC.exists_bound_of_continuousOn
      (((contDiffOn_inverseOperator D γ).continuousOn_fderiv_of_isOpen
        D.open_chart (by simp)).mono hCchart)
  choose a ha using hact
  choose k hk using hinv
  refine ⟨1 + ∑ γ : Γ, |a γ|, 1 + ∑ γ : Γ, |k γ|,
    by have : 0 ≤ ∑ γ : Γ, |a γ| := Finset.sum_nonneg (fun γ _ => abs_nonneg (a γ)); linarith,
    by have : 0 ≤ ∑ γ : Γ, |k γ| := Finset.sum_nonneg (fun γ _ => abs_nonneg (k γ)); linarith, ?_⟩
  intro γ x hx
  constructor
  · exact (ha γ x hx).trans ((le_abs_self _).trans (by
      have := Finset.single_le_sum (fun δ _ => abs_nonneg (a δ)) (Finset.mem_univ γ)
      linarith))
  · exact (hk γ x hx).trans ((le_abs_self _).trans (by
      have := Finset.single_le_sum (fun δ _ => abs_nonneg (k δ)) (Finset.mem_univ γ)
      linarith))

private theorem norm_fderiv_operator_term_le {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (γ : Γ) (u : E n → V r) (hu : ContDiff ℝ ∞ u)
    {x : E n} (hx : x ∈ D.chart) (z : E n) :
    ‖fderiv ℝ (fun y => (D.cocycle γ y).symm (u (D.act γ y))) x z‖ ≤
      ‖fderiv ℝ u (D.act γ x)‖ * ‖fderiv ℝ (D.act γ) x‖ * ‖z‖ +
        ‖fderiv ℝ (inverseOperator D γ) x‖ * ‖u (D.act γ x)‖ * ‖z‖ := by
  have hact := ((D.smooth_action γ).contDiffAt (D.open_chart.mem_nhds hx)).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hi := ((contDiffOn_inverseOperator D γ).contDiffAt
    (D.open_chart.mem_nhds hx)).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hud := (hu.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)) (D.act γ x)
  have hd := hi.hasFDerivAt.clm_apply (hud.hasFDerivAt.comp x hact.hasFDerivAt)
  change ‖fderiv ℝ (fun y => inverseOperator D γ y ((u ∘ D.act γ) y)) x z‖ ≤ _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · change ‖(D.cocycle γ x).symm (fderiv ℝ u (D.act γ x) (fderiv ℝ (D.act γ) x z))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    calc ‖fderiv ℝ u (D.act γ x) (fderiv ℝ (D.act γ) x z)‖
        ≤ ‖fderiv ℝ u (D.act γ x)‖ * ‖fderiv ℝ (D.act γ) x z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ u (D.act γ x)‖ * (‖fderiv ℝ (D.act γ) x‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring
  · calc ‖(fderiv ℝ (inverseOperator D γ) x z) (u (D.act γ x))‖
        ≤ ‖fderiv ℝ (inverseOperator D γ) x z‖ * ‖u (D.act γ x)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (inverseOperator D γ) x‖ * ‖z‖) * ‖u (D.act γ x)‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring

private theorem finiteH0_smooth_compact {n r : ℕ} (u : E n → V r)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    FiniteH0 Set.univ u (fun j x => fderiv ℝ u x (coordinateDirection j)) := by
  simp only [FiniteH0, Measure.restrict_univ]
  refine ⟨hu.continuous.memLp_of_hasCompactSupport hc, fun j => ?_⟩
  have hcont : Continuous (fun x => fderiv ℝ u x (coordinateDirection j)) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcc : HasCompactSupport (fun x => fderiv ℝ u x (coordinateDirection j)) :=
    (hc.fderiv ℝ).comp_left (g := fun T : E n →L[ℝ] V r => T (coordinateDirection j)) rfl
  exact hcont.memLp_of_hasCompactSupport hcc

private theorem opNorm_le_coordinate_sum {n r : ℕ} (T : E n →L[ℝ] V r) :
    ‖T‖ ≤ ∑ j : Fin n, ‖T (coordinateDirection j)‖ := by
  classical
  apply T.opNorm_le_bound (Finset.sum_nonneg fun j _ => norm_nonneg _)
  intro z
  have hz : ∑ j : Fin n, (z j) • coordinateDirection j = z := by
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      coordinateDirection] using h
  calc ‖T z‖ = ‖∑ j : Fin n, (z j) • T (coordinateDirection j)‖ := by
          conv_lhs => rw [← hz, map_sum]
          simp only [map_smul]
    _ ≤ ∑ j : Fin n, ‖(z j) • T (coordinateDirection j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, ‖T (coordinateDirection j)‖ * ‖z‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul, mul_comm]
          exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le z j) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private theorem compact_weighted_finite {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) {K : Set (E n)} (hK : IsCompact K) (hKD : K ⊆ D.chart) :
    KPChartL2.weightedMeasure n D.chart D.weight K < ⊤ := by
  rw [KPChartL2.weightedMeasure, withDensity_apply _ hK.measurableSet,
    Measure.restrict_restrict hK.measurableSet, Set.inter_eq_left.mpr hKD]
  have hi := (D.locally_integrable_weight.mono_set hKD).integrableOn_isCompact hK
  apply lt_of_le_of_lt _ hi.hasFiniteIntegral
  apply lintegral_mono
  intro x
  dsimp only
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

private theorem smooth_compact_weighted_memLp {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (u : E n → V r) (hu : Continuous u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ D.chart) :
    MemLp u 2 (KPChartL2.weightedMeasure n D.chart D.weight) := by
  let μ := KPChartL2.weightedMeasure n D.chart D.weight
  let K := tsupport u
  have hKm : MeasurableSet K := hc.measurableSet
  haveI : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact compact_weighted_finite D hc hs⟩
  have hmem : MemLp u 2 (μ.restrict K) := hu.memLp_of_hasCompactSupport hc
  have hind := (memLp_indicator_iff_restrict hKm.nullMeasurableSet).mpr hmem
  have heq : K.indicator u = u := Set.indicator_eq_self.mpr subset_closure
  rwa [heq] at hind

private theorem average_congr_ae {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ) (u w : E n → V r)
    (h : u =ᵐ[KPChartL2.weightedMeasure n D.chart D.weight] w) :
    KPChartL2.average n r Γ D.chart D.act D.cocycle u =ᵐ[
      KPChartL2.weightedMeasure n D.chart D.weight]
      KPChartL2.average n r Γ D.chart D.act D.cocycle w := by
  classical
  have ht : ∀ᵐ x ∂KPChartL2.weightedMeasure n D.chart D.weight,
      ∀ γ : Γ, u (D.act γ x) = w (D.act γ x) := by
    rw [Filter.eventually_all]
    intro γ
    exact (D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [ht] with x hx
  simp only [KPChartL2.average]
  by_cases hxc : x ∈ D.chart
  · simp [Set.indicator_of_mem hxc, hx]
  · simp [Set.indicator_of_notMem hxc]

private theorem average_toLp_eq {n r : ℕ} {Γ : Type*} [Group Γ] [Fintype Γ]
    (D : KPChartL2.Data n r Γ)
    (P : Lp (V r) 2 (KPChartL2.weightedMeasure n D.chart D.weight) →L[ℂ]
      Lp (V r) 2 (KPChartL2.weightedMeasure n D.chart D.weight))
    (hP : ∀ f, ∀ᵐ x ∂KPChartL2.weightedMeasure n D.chart D.weight,
      (P f) x = KPChartL2.average n r Γ D.chart D.act D.cocycle f x)
    (u : E n → V r) (hu : MemLp u 2 (KPChartL2.weightedMeasure n D.chart D.weight))
    (hv : MemLp (KPChartL2.average n r Γ D.chart D.act D.cocycle u) 2
      (KPChartL2.weightedMeasure n D.chart D.weight)) :
    hv.toLp _ = P (hu.toLp u) := by
  apply Lp.ext
  have hp : (P (hu.toLp u)) =ᵐ[KPChartL2.weightedMeasure n D.chart D.weight]
      KPChartL2.average n r Γ D.chart D.act D.cocycle (hu.toLp u) := hP _
  exact (MemLp.coeFn_toLp hv).trans
    ((average_congr_ae D _ _ (MemLp.coeFn_toLp hu).symm).trans hp.symm)

private theorem norm_fderiv_average_coordinate_le {n r : ℕ} {Γ : Type*}
    [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ)
    (C : Set (E n)) (hCchart : C ⊆ D.chart) (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hb : ∀ γ x, x ∈ C → ‖fderiv ℝ (D.act γ) x‖ ≤ A ∧
      ‖fderiv ℝ (inverseOperator D γ) x‖ ≤ K)
    (u : E n → V r) (hu : ContDiff ℝ ∞ u) {x : E n} (hx : x ∈ C) (j : Fin n) :
    ‖fderiv ℝ (KPChartL2.average n r Γ D.chart D.act D.cocycle u) x
      (coordinateDirection j)‖ ≤
      (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ,
        (A * (∑ k : Fin n, ‖fderiv ℝ u (D.act γ x) (coordinateDirection k)‖) +
          K * ‖u (D.act γ x)‖) := by
  refine (norm_fderiv_average_le D u hu (hCchart hx) j).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun γ _ => ?_
  have ht := norm_fderiv_operator_term_le D γ u hu (hCchart hx) (coordinateDirection j)
  have hz : ‖coordinateDirection j‖ = 1 := by simp [coordinateDirection, EuclideanSpace.norm_single]
  rw [hz, mul_one, mul_one] at ht
  refine ht.trans (add_le_add ?_ ?_)
  · calc ‖fderiv ℝ u (D.act γ x)‖ * ‖fderiv ℝ (D.act γ) x‖
        ≤ ‖fderiv ℝ u (D.act γ x)‖ * A :=
          mul_le_mul_of_nonneg_left (hb γ x hx).1 (norm_nonneg _)
      _ ≤ (∑ k : Fin n, ‖fderiv ℝ u (D.act γ x) (coordinateDirection k)‖) * A :=
          mul_le_mul_of_nonneg_right (opNorm_le_coordinate_sum _) hA
      _ = _ := mul_comm _ _
  · exact mul_le_mul_of_nonneg_right (hb γ x hx).2 (norm_nonneg _)

private theorem sq_average_le {Γ : Type*} [Group Γ] [Fintype Γ] (t : Γ → ℝ) :
    ((Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, t γ) ^ 2 ≤
      (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, (t γ) ^ 2 := by
  classical
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := t)
  simp only [Finset.card_univ] at h
  calc ((Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, t γ) ^ 2
      = (Fintype.card Γ : ℝ)⁻¹ ^ 2 * (∑ γ : Γ, t γ) ^ 2 := mul_pow _ _ _
    _ ≤ (Fintype.card Γ : ℝ)⁻¹ ^ 2 *
        ((Fintype.card Γ : ℝ) * ∑ γ : Γ, (t γ) ^ 2) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by
      have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp

private theorem coordinate_derivative_square_bound {n r : ℕ} {Γ : Type*}
    [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ)
    (C : Set (E n)) (hCchart : C ⊆ D.chart) (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hb : ∀ γ x, x ∈ C → ‖fderiv ℝ (D.act γ) x‖ ≤ A ∧
      ‖fderiv ℝ (inverseOperator D γ) x‖ ≤ K)
    (u : E n → V r) (hu : ContDiff ℝ ∞ u) {x : E n} (hx : x ∈ C) (j : Fin n) :
    ‖fderiv ℝ (KPChartL2.average n r Γ D.chart D.act D.cocycle u) x
      (coordinateDirection j)‖ ^ 2 ≤
      (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ,
        (2 * A ^ 2 * n * (∑ k : Fin n, ‖fderiv ℝ u (D.act γ x) (coordinateDirection k)‖ ^ 2) +
          2 * K ^ 2 * ‖u (D.act γ x)‖ ^ 2) := by
  classical
  have ht := norm_fderiv_average_coordinate_le D C hCchart A K hA hK hb u hu hx j
  refine (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans ((sq_average_le _).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun γ _ => ?_
  have hsum := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun k => ‖fderiv ℝ u (D.act γ x) (coordinateDirection k)‖)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hsum' := mul_le_mul_of_nonneg_left hsum (sq_nonneg A)
  nlinarith [sq_nonneg (A * (∑ k : Fin n, ‖fderiv ℝ u (D.act γ x) (coordinateDirection k)‖) -
    K * ‖u (D.act γ x)‖)]

private theorem averaged_projection_and_contraction {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    {Γ : Type*} [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ)
    (P : Lp (V r) 2 (KPChartL2.weightedMeasure n D.chart D.weight) →L[ℂ]
      Lp (V r) 2 (KPChartL2.weightedMeasure n D.chart D.weight))
    (hPnorm : ∀ f, ‖P f‖ ≤ ‖f‖)
    (hP : ∀ f, ∀ᵐ x ∂KPChartL2.weightedMeasure n D.chart D.weight,
      (P f) x = KPChartL2.average n r Γ D.chart D.act D.cocycle f x)
    (u u' : E n → V r) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ D.chart) (hu' : ContDiff ℝ ∞ u') (hc' : HasCompactSupport u')
    (hs' : tsupport u' ⊆ D.chart) :
    let v := KPChartL2.average n r Γ D.chart D.act D.cocycle u
    let v' := KPChartL2.average n r Γ D.chart D.act D.cocycle u'
    ∃ (hum : MemLp u 2 (KPChartL2.weightedMeasure n D.chart D.weight))
      (hu'm : MemLp u' 2 (KPChartL2.weightedMeasure n D.chart D.weight))
      (hvm : MemLp v 2 (KPChartL2.weightedMeasure n D.chart D.weight))
      (hv'm : MemLp v' 2 (KPChartL2.weightedMeasure n D.chart D.weight)),
      ‖hvm.toLp v - hv'm.toLp v'‖ ≤ ‖hum.toLp u - hu'm.toLp u'‖ := by
  dsimp only
  have hav := kp_cont_chart_equivariant_average_smooth n r hn hr Γ D u hu.contDiffOn hc hs
  have hav' := kp_cont_chart_equivariant_average_smooth n r hn hr Γ D u' hu'.contDiffOn hc' hs'
  have hum := smooth_compact_weighted_memLp D u hu.continuous hc hs
  have hu'm := smooth_compact_weighted_memLp D u' hu'.continuous hc' hs'
  have hvm := smooth_compact_weighted_memLp D _ (contDiff_average hn hr D u hu hc hs).continuous
    hav.2.1 hav.2.2.1
  have hv'm := smooth_compact_weighted_memLp D _ (contDiff_average hn hr D u' hu' hc' hs').continuous
    hav'.2.1 hav'.2.2.1
  refine ⟨hum, hu'm, hvm, hv'm, ?_⟩
  rw [average_toLp_eq D P hP u hum hvm, average_toLp_eq D P hP u' hu'm hv'm, ← map_sub]
  exact hPnorm _

private theorem H0_bound_of_energy {n r : ℕ} (u v : E n → V r)
    (g h : Fin n → E n → V r) (hu : FiniteH0 Set.univ u g) (hv : FiniteH0 Set.univ v h)
    (T : ℝ) (hT : 0 ≤ T)
    (hb : (∫ x, ‖v x‖ ^ 2) + (∑ j : Fin n, ∫ x, ‖h j x‖ ^ 2) ≤
      T * ((∫ x, ‖u x‖ ^ 2) + (∑ j : Fin n, ∫ x, ‖g j x‖ ^ 2))) :
    H0 Set.univ v h hv ≤ (2 * Real.sqrt T) * H0 Set.univ u g hu := by
  have hF : 0 ≤ ∫ x, ‖u x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hG : 0 ≤ ∑ j : Fin n, ∫ x, ‖g j x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hV : 0 ≤ ∫ x, ‖v x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hH : 0 ≤ ∑ j : Fin n, ∫ x, ‖h j x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have heq : ∀ (f : E n → V r) (a : Fin n → E n → V r) (hf : FiniteH0 Set.univ f a),
      H0 Set.univ f a hf = Real.sqrt (∫ x, ‖f x‖ ^ 2) +
        Real.sqrt (∑ j : Fin n, ∫ x, ‖a j x‖ ^ 2) := by
    intro f a hf
    simp only [H0, l2Norm, Measure.restrict_univ]
    congr 2
    exact Finset.sum_congr rfl fun j _ => Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  rw [heq v h hv, heq u g hu]
  have hs := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul hT] at hs
  have hlow : Real.sqrt ((∫ x, ‖u x‖ ^ 2) + (∑ j : Fin n, ∫ x, ‖g j x‖ ^ 2)) ≤
      Real.sqrt (∫ x, ‖u x‖ ^ 2) + Real.sqrt (∑ j : Fin n, ∫ x, ‖g j x‖ ^ 2) := by
    nlinarith [Real.sq_sqrt hF, Real.sq_sqrt hG, Real.sq_sqrt (add_nonneg hF hG),
      Real.sqrt_nonneg ((∫ x, ‖u x‖ ^ 2) + (∑ j : Fin n, ∫ x, ‖g j x‖ ^ 2)),
      Real.sqrt_nonneg (∫ x, ‖u x‖ ^ 2), Real.sqrt_nonneg (∑ j : Fin n, ∫ x, ‖g j x‖ ^ 2),
      mul_nonneg (Real.sqrt_nonneg (∫ x, ‖u x‖ ^ 2))
        (Real.sqrt_nonneg (∑ j : Fin n, ∫ x, ‖g j x‖ ^ 2))]
  have hupp : Real.sqrt (∫ x, ‖v x‖ ^ 2) + Real.sqrt (∑ j : Fin n, ∫ x, ‖h j x‖ ^ 2) ≤
      2 * Real.sqrt ((∫ x, ‖v x‖ ^ 2) + (∑ j : Fin n, ∫ x, ‖h j x‖ ^ 2)) := by
    nlinarith [Real.sq_sqrt hV, Real.sq_sqrt hH, Real.sq_sqrt (add_nonneg hV hH),
      Real.sqrt_nonneg ((∫ x, ‖v x‖ ^ 2) + (∑ j : Fin n, ∫ x, ‖h j x‖ ^ 2)),
      Real.sqrt_nonneg (∫ x, ‖v x‖ ^ 2), Real.sqrt_nonneg (∑ j : Fin n, ∫ x, ‖h j x‖ ^ 2),
      sq_nonneg (Real.sqrt (∫ x, ‖v x‖ ^ 2) - Real.sqrt (∑ j : Fin n, ∫ x, ‖h j x‖ ^ 2))]
  have hh := mul_le_mul_of_nonneg_left hlow (Real.sqrt_nonneg T)
  nlinarith only [hupp, hs, hh]

private theorem averaged_energy_bound {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    {Γ : Type*} [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ)
    (C : Set (E n)) (hC : IsCompact C) (hCchart : C ⊆ D.chart)
    (A K L : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hb : ∀ γ x, x ∈ C → ‖fderiv ℝ (D.act γ) x‖ ≤ A ∧
      ‖fderiv ℝ (inverseOperator D γ) x‖ ≤ K)
    (u : E n → V r) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ D.chart)
    (hvs : tsupport (KPChartL2.average n r Γ D.chart D.act D.cocycle u) ⊆ C)
    (htransport : ∀ γ : Γ,
      (∫ x in C, ‖u (D.act γ x)‖ ^ 2) ≤ L * (∫ x, ‖u x‖ ^ 2))
    (hdtransport : ∀ (γ : Γ) (j : Fin n),
      (∫ x in C, ‖fderiv ℝ u (D.act γ x) (coordinateDirection j)‖ ^ 2) ≤
        L * (∫ x, ‖fderiv ℝ u x (coordinateDirection j)‖ ^ 2)) :
    let v := KPChartL2.average n r Γ D.chart D.act D.cocycle u
    (∫ x, ‖v x‖ ^ 2) + (∑ j : Fin n, ∫ x, ‖fderiv ℝ v x (coordinateDirection j)‖ ^ 2) ≤
      (L + 2 * K ^ 2 * n * L + 2 * A ^ 2 * n ^ 2 * L) *
        ((∫ x, ‖u x‖ ^ 2) + (∑ j : Fin n, ∫ x, ‖fderiv ℝ u x (coordinateDirection j)‖ ^ 2)) := by
  classical
  let v := KPChartL2.average n r Γ D.chart D.act D.cocycle u
  have hv := contDiff_average hn hr D u hu hc hs
  have hvc := (kp_cont_chart_equivariant_average_smooth n r hn hr Γ D u hu.contDiffOn hc hs).2.1
  have h0v := finiteH0_smooth_compact v hv hvc
  simp only [FiniteH0, Measure.restrict_univ] at h0v
  have hcU : ∀ γ : Γ, IntegrableOn (fun x => ‖u (D.act γ x)‖ ^ 2) C := fun γ =>
    ((hu.continuous.continuousOn.comp ((D.smooth_action γ).continuousOn.mono hCchart)
      (fun _ _ => Set.mem_univ _)).norm.pow 2).integrableOn_compact hC
  have hcG : ∀ (γ : Γ) (j : Fin n),
      IntegrableOn (fun x => ‖fderiv ℝ u (D.act γ x) (coordinateDirection j)‖ ^ 2) C := by
    intro γ j
    have hd : Continuous (fun x => fderiv ℝ u x (coordinateDirection j)) :=
      (hu.continuous_fderiv (by simp)).clm_apply continuous_const
    exact ((hd.continuousOn.comp ((D.smooth_action γ).continuousOn.mono hCchart)
      (fun _ _ => Set.mem_univ _)).norm.pow 2).integrableOn_compact hC
  have heqU : (∫ x in C, ‖v x‖ ^ 2) = ∫ x, ‖v x‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : v x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hvs h))
      simp [hz])
  have heqG : ∀ j : Fin n,
      (∫ x in C, ‖fderiv ℝ v x (coordinateDirection j)‖ ^ 2) =
        ∫ x, ‖fderiv ℝ v x (coordinateDirection j)‖ ^ 2 := by
    intro j
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : fderiv ℝ v x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hvs (tsupport_fderiv_subset ℝ ht)))
    simp [hz]
  have hcR : IntegrableOn (fun x => (Fintype.card Γ : ℝ)⁻¹ *
      ∑ γ : Γ, ‖u (D.act γ x)‖ ^ 2) C :=
    (integrable_finset_sum _ (fun γ _ => hcU γ)).const_mul _
  have hval : (∫ x, ‖v x‖ ^ 2) ≤ L * (∫ x, ‖u x‖ ^ 2) := by
    have hh := integral_mono_ae ((h0v.1.integrable_norm_pow (by norm_num)).restrict (s := C)) hcR
      (by filter_upwards [ae_restrict_mem hC.measurableSet] with x hx; exact norm_average_sq_le D u (hCchart hx))
    rw [heqU, integral_const_mul, integral_finset_sum _ (fun γ _ => hcU γ)] at hh
    refine hh.trans ?_
    calc (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, ∫ x in C, ‖u (D.act γ x)‖ ^ 2
        ≤ (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ, L * (∫ x, ‖u x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun γ _ => htransport γ) (by positivity)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (show (Fintype.card Γ : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)]
  have hder : ∀ j : Fin n, (∫ x, ‖fderiv ℝ v x (coordinateDirection j)‖ ^ 2) ≤
      2 * A ^ 2 * n * L * (∑ k : Fin n, ∫ x, ‖fderiv ℝ u x (coordinateDirection k)‖ ^ 2) +
      2 * K ^ 2 * L * (∫ x, ‖u x‖ ^ 2) := by
    intro j
    have hR : IntegrableOn (fun x => (Fintype.card Γ : ℝ)⁻¹ * ∑ γ : Γ,
        (2 * A ^ 2 * n * (∑ k : Fin n, ‖fderiv ℝ u (D.act γ x) (coordinateDirection k)‖ ^ 2) +
          2 * K ^ 2 * ‖u (D.act γ x)‖ ^ 2)) C := by
      refine (integrable_finset_sum _ (fun γ _ => ?_)).const_mul _
      exact ((integrable_finset_sum _ (fun k _ => hcG γ k)).const_mul _).add ((hcU γ).const_mul _)
    have hh := integral_mono_ae (((h0v.2 j).integrable_norm_pow (by norm_num)).restrict (s := C)) hR
      (by filter_upwards [ae_restrict_mem hC.measurableSet] with x hx;
          exact coordinate_derivative_square_bound D C hCchart A K hA hK hb u hu hx j)
    have hi : ∀ γ : Γ, IntegrableOn (fun x =>
        2 * A ^ 2 * n * (∑ k : Fin n, ‖fderiv ℝ u (D.act γ x) (coordinateDirection k)‖ ^ 2) +
          2 * K ^ 2 * ‖u (D.act γ x)‖ ^ 2) C := fun γ =>
      ((integrable_finset_sum _ (fun k _ => hcG γ k)).const_mul _).add ((hcU γ).const_mul _)
    rw [heqG j, integral_const_mul, integral_finset_sum _ (fun γ _ => hi γ)] at hh
    refine hh.trans ?_
    have hterm : ∀ γ : Γ,
      (∫ x in C, 2 * A ^ 2 * n * (∑ k : Fin n, ‖fderiv ℝ u (D.act γ x) (coordinateDirection k)‖ ^ 2) +
        2 * K ^ 2 * ‖u (D.act γ x)‖ ^ 2) ≤
      2 * A ^ 2 * n * L * (∑ k : Fin n, ∫ x, ‖fderiv ℝ u x (coordinateDirection k)‖ ^ 2) +
      2 * K ^ 2 * L * (∫ x, ‖u x‖ ^ 2) := by
      intro γ
      rw [integral_add ((integrable_finset_sum _ (fun k _ => hcG γ k)).const_mul _)
        ((hcU γ).const_mul _), integral_const_mul, integral_const_mul,
        integral_finset_sum _ (fun k _ => hcG γ k)]
      have hd := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hdtransport γ k)
      rw [← Finset.mul_sum] at hd
      have hh1 := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * A ^ 2 * n by positivity)
      have hh2 := mul_le_mul_of_nonneg_left (htransport γ) (show 0 ≤ 2 * K ^ 2 by positivity)
      nlinarith only [hh1, hh2]
    exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun γ _ => hterm γ)) (by positivity)).trans_eq
      (by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcΓ : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp)
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hder j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hd
  have hF : 0 ≤ ∫ x, ‖u x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hG : 0 ≤ ∑ j : Fin n, ∫ x, ‖fderiv ℝ u x (coordinateDirection j)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  dsimp only
  nlinarith [mul_nonneg (show 0 ≤ 2 * A ^ 2 * (n : ℝ) ^ 2 * L by positivity) hF,
    mul_nonneg (show 0 ≤ L + 2 * K ^ 2 * n * L by positivity) hG]

theorem kp_cont_compact_h1_smooth_average_bound
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (Γ : Type*) [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ)
    (C : Set (E n)) (hC : IsCompact C) (hCchart : C ⊆ D.chart) :
    let μ := KPChartL2.weightedMeasure n D.chart D.weight
    ∃ (B : ℝ) (P : Lp (V r) 2 μ →L[ℂ] Lp (V r) 2 μ),
      1 ≤ B ∧
      (∀ f, ‖P f‖ ≤ ‖f‖) ∧
      (∀ f, P (P f) = P f) ∧
      Set.range P = KPChartL2.equivariantL2 n r Γ μ D.act D.cocycle ∧
      (∀ f, ∀ᵐ x ∂μ,
        (P f) x = KPChartL2.average n r Γ D.chart D.act D.cocycle f x) ∧
      ∀ (O : Set (E n)), IsOpen O → O ⊆ D.chart →
        (∀ (γ : Γ) (x : E n), x ∈ O → D.act γ x ∈ O) → closure O = C →
        ((∀ (u : E n → V r), ContDiff ℝ ∞ u → HasCompactSupport u →
            tsupport u ⊆ O →
          let v := KPChartL2.average n r Γ D.chart D.act D.cocycle u
          ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ tsupport v ⊆ O ∧
          (∀ γ x, x ∈ D.chart → v (D.act γ x) = D.cocycle γ x (v x)) ∧
          ∃ (h0u : FiniteH0 Set.univ u
              (fun j x => fderiv ℝ u x (coordinateDirection j)))
            (h0v : FiniteH0 Set.univ v
              (fun j x => fderiv ℝ v x (coordinateDirection j)))
            (hu : MemLp u 2 μ) (hv : MemLp v 2 μ),
            H0 Set.univ v (fun j x => fderiv ℝ v x (coordinateDirection j)) h0v ≤
              B * H0 Set.univ u (fun j x => fderiv ℝ u x (coordinateDirection j)) h0u ∧
            hv.toLp v = P (hu.toLp u)) ∧
        (∀ (u u' : E n → V r),
          ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u ⊆ O →
          ContDiff ℝ ∞ u' → HasCompactSupport u' → tsupport u' ⊆ O →
          let v := KPChartL2.average n r Γ D.chart D.act D.cocycle u
          let v' := KPChartL2.average n r Γ D.chart D.act D.cocycle u'
          ∃ (hu : MemLp u 2 μ) (hu' : MemLp u' 2 μ)
            (hv : MemLp v 2 μ) (hv' : MemLp v' 2 μ),
            ‖hv.toLp v - hv'.toLp v'‖ ≤ ‖hu.toLp u - hu'.toLp u'‖)) := by
  classical
  dsimp only
  obtain ⟨A, K, hA, hK, hb⟩ := exists_differential_bounds D C hC hCchart
  obtain ⟨L, hLp, hLt⟩ := integral_action_le_compact_weight D C hC hCchart
  have hL : 0 ≤ L := hLp.le
  have htransport : ∀ (O : Set (E n)),
      (∀ γ x, x ∈ O → D.act γ x ∈ O) → closure O = C →
      ∀ (γ : Γ) (f : E n → V r), Continuous f → HasCompactSupport f → tsupport f ⊆ C →
        (∫ x in C, ‖f (D.act γ x)‖ ^ 2) ≤ L * (∫ x, ‖f x‖ ^ 2) := by
    intro O hOinv hOC γ f hf hc hs
    apply hLt γ (fun x => ‖f x‖ ^ 2) (hf.norm.pow 2) (fun _ => sq_nonneg _)
    intro x hx
    apply hs
    apply subset_closure
    intro hz
    exact hx (by simp [hz])
  let T := L + 2 * K ^ 2 * n * L + 2 * A ^ 2 * n ^ 2 * L
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨P, hPn, hPid, hPr, hPf⟩ :=
    (kp_cont_chart_equivariant_l2_projection n r hn hr Γ D).2
  refine ⟨max 1 (2 * Real.sqrt T), P, le_max_left _ _, hPn, hPid, hPr, hPf, ?_⟩
  intro O hO hOchart hOinv hOC
  constructor
  · intro u hu hc hs
    let v := KPChartL2.average n r Γ D.chart D.act D.cocycle u
    have hschart := hs.trans hOchart
    have hsuC : tsupport u ⊆ C := hs.trans (hOC ▸ subset_closure)
    have hav := kp_cont_chart_equivariant_average_smooth n r hn hr Γ D u hu.contDiffOn hc hschart
    have hvsO := tsupport_average_subset_invariant D u hc O hOchart hOinv hs
    have hv := contDiff_average hn hr D u hu hc hschart
    refine ⟨hv, hav.2.1, hvsO, hav.2.2.2, ?_⟩
    have h0u := finiteH0_smooth_compact u hu hc
    have h0v := finiteH0_smooth_compact v hv hav.2.1
    have hum := smooth_compact_weighted_memLp D u hu.continuous hc hschart
    have hvm := smooth_compact_weighted_memLp D v hv.continuous hav.2.1 hav.2.2.1
    refine ⟨h0u, h0v, hum, hvm, ?_, average_toLp_eq D P hPf u hum hvm⟩
    have hen := averaged_energy_bound hn hr D C hC hCchart A K L (by linarith) (by linarith)
      hL hb u hu hc hschart (hvsO.trans (hOC ▸ subset_closure))
      (fun γ => htransport O hOinv hOC γ u hu.continuous hc hsuC) (fun γ j => ?_)
    · exact (H0_bound_of_energy u v _ _ h0u h0v T hT hen).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by
          unfold H0 l2Norm
          exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    · have hder : Continuous (fun x => fderiv ℝ u x (coordinateDirection j)) :=
        (hu.continuous_fderiv (by simp)).clm_apply continuous_const
      have hcder : HasCompactSupport (fun x => fderiv ℝ u x (coordinateDirection j)) :=
        (hc.fderiv ℝ).comp_left (g := fun T : E n →L[ℝ] V r => T (coordinateDirection j)) rfl
      have hsder : tsupport (fun x => fderiv ℝ u x (coordinateDirection j)) ⊆ C :=
        (tsupport_comp_subset (g := fun T : E n →L[ℝ] V r => T (coordinateDirection j)) rfl
          (fderiv ℝ u)).trans
          ((tsupport_fderiv_subset ℝ).trans hsuC)
      exact htransport O hOinv hOC γ (fun x => fderiv ℝ u x (coordinateDirection j)) hder hcder hsder
  · intro u u' hu hc hs hu' hc' hs'
    exact averaged_projection_and_contraction hn hr D P hPn hPf u u' hu hc (hs.trans hOchart)
      hu' hc' (hs'.trans hOchart)

end DedekindZetaZeroFree

end
