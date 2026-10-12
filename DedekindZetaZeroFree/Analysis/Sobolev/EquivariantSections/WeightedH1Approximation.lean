module

public import DedekindZetaZeroFree.Analysis.Sobolev.Approximation.CompactInteriorSmoothDensity
public import DedekindZetaZeroFree.Analysis.Sobolev.EquivariantSections.SmoothAveragingBounds
public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.L2ClosednessAndUniqueness

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open MeasureTheory TopologicalSpace KPCompactInteriorH1 Filter
open scoped ContDiff ENNReal Topology

namespace KPCompactInteriorH1

private lemma enorm_eq (r : ℕ) (v : V r) : ‖v‖ₑ = ENNReal.ofReal ‖v‖ :=
  (ofReal_norm v).symm

private lemma eLpNorm_two_eq_ofReal_l2Norm {n r : ℕ} (μ : Measure (E n))
    (f : E n → V r) (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (l2Norm μ f hf) := by
  have hint : Integrable (fun x => ‖f x‖ ^ (2 : ℕ)) μ :=
    hf.integrable_norm_pow (by norm_num)
  have hnn : 0 ≤ᵐ[μ] fun x => ‖f x‖ ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun x => by positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  have hto : ENNReal.toReal (2 : ℝ≥0∞) = 2 := by norm_num
  rw [hto]
  have hcongr : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ)
      = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) ∂μ := by
    apply lintegral_congr
    intro x
    rw [enorm_eq]
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [l2Norm, Real.sqrt_eq_rpow]

private lemma l2Norm_eq_toReal {n r : ℕ} (μ : Measure (E n)) (f : E n → V r)
    (hf : MemLp f 2 μ) : l2Norm μ f hf = (eLpNorm f 2 μ).toReal := by
  rw [eLpNorm_two_eq_ofReal_l2Norm μ f hf]
  unfold l2Norm
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

private lemma l2Norm_nonneg {n r : ℕ} (μ : Measure (E n)) (f : E n → V r)
    (hf : MemLp f 2 μ) : 0 ≤ l2Norm μ f hf := Real.sqrt_nonneg _

private lemma tendsto_l2Norm_of_tendsto_eLpNorm {n r : ℕ} (μ : Measure (E n))
    (fm : ℕ → E n → V r) (f : E n → V r)
    (herr : ∀ m, MemLp (fm m - f) 2 μ)
    (h : Tendsto (fun m => eLpNorm (fm m - f) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => l2Norm μ (fm m - f) (herr m)) atTop (𝓝 0) := by
  have heq : (fun m => l2Norm μ (fm m - f) (herr m))
      = fun m => (eLpNorm (fm m - f) 2 μ).toReal :=
    funext fun m => l2Norm_eq_toReal μ (fm m - f) (herr m)
  rw [heq]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

private lemma tendsto_eLpNorm_of_tendsto_l2Norm {n r : ℕ} (μ : Measure (E n))
    (fm : ℕ → E n → V r) (herr : ∀ m, MemLp (fm m) 2 μ)
    (h : Tendsto (fun m => l2Norm μ (fm m) (herr m)) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fm m) 2 μ) atTop (𝓝 0) := by
  have heq : (fun m => eLpNorm (fm m) 2 μ)
      = fun m => ENNReal.ofReal (l2Norm μ (fm m) (herr m)) :=
    funext fun m => eLpNorm_two_eq_ofReal_l2Norm μ (fm m) (herr m)
  rw [heq, show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
  exact ENNReal.tendsto_ofReal h

private lemma l2Norm_congr_ae {n r : ℕ} (μ : Measure (E n)) {f g : E n → V r}
    (hfg : f =ᵐ[μ] g) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    l2Norm μ f hf = l2Norm μ g hg := by
  unfold l2Norm
  congr 1
  exact integral_congr_ae (hfg.mono fun x hx => by simp only [hx])

private lemma l2Norm_deriv_le_H0 {n r : ℕ} (f : E n → V r) (g : Fin n → E n → V r)
    (h : FiniteH0 Set.univ f g) (j : Fin n) :
    l2Norm (volume.restrict Set.univ) (g j) (h.2 j) ≤ H0 Set.univ f g h := by
  have h2 : l2Norm (volume.restrict Set.univ) (g j) (h.2 j)
      ≤ Real.sqrt (∑ i, (l2Norm (volume.restrict Set.univ) (g i) (h.2 i)) ^ 2) :=
    Real.le_sqrt_of_sq_le (Finset.single_le_sum
      (fun i _ => sq_nonneg (l2Norm (volume.restrict Set.univ) (g i) (h.2 i)))
      (Finset.mem_univ j))
  have h3 : l2Norm (volume.restrict Set.univ) (g j) (h.2 j)
      ≤ l2Norm (volume.restrict Set.univ) f h.1
        + Real.sqrt (∑ i, (l2Norm (volume.restrict Set.univ) (g i) (h.2 i)) ^ 2) :=
    h2.trans (le_add_of_nonneg_left (l2Norm_nonneg (volume.restrict Set.univ) f h.1))
  exact h3

private lemma memLp_restrict_univ {n r : ℕ} {f : E n → V r}
    (h : MemLp f 2 (volume.restrict Set.univ)) : MemLp f 2 volume :=
  (Measure.restrict_univ (μ := (volume : Measure (E n)))) ▸ h

private lemma cauchySeq_Lp_of_tendsto_l2Norm {n r : ℕ} (fm : ℕ → E n → V r)
    (hfm : ∀ m, MemLp (fm m) 2 (volume : Measure (E n)))
    (h : Tendsto (fun p : ℕ × ℕ => l2Norm volume (fm p.1 - fm p.2)
        ((hfm p.1).sub (hfm p.2))) atTop (𝓝 0)) :
    CauchySeq (fun m => (hfm m).toLp (fm m)) := by
  rw [MeasureTheory.Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
  have hfun : (fun p : ℕ × ℕ => eLpNorm (⇑((hfm p.1).toLp (fm p.1)) -
        ⇑((hfm p.2).toLp (fm p.2))) 2 (volume : Measure (E n)))
      = fun p : ℕ × ℕ => ENNReal.ofReal (l2Norm volume (fm p.1 - fm p.2)
          ((hfm p.1).sub (hfm p.2))) := by
    funext p
    rw [eLpNorm_congr_ae ((hfm p.1).coeFn_toLp.sub (hfm p.2).coeFn_toLp)]
    exact eLpNorm_two_eq_ofReal_l2Norm volume _ _
  rw [hfun, show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
  exact ENNReal.tendsto_ofReal h

end KPCompactInteriorH1

open KPCompactInteriorH1

theorem kp_cont_compact_interior_equivariant_h1_approximation
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (Γ : Type*) [Group Γ] [Fintype Γ] (D : KPChartL2.Data n r Γ)
    (Q : InverseMetric (chartOpens D))
    (A : Connection (r := r) (chartOpens D))
    (hQ : Q.IsInvariant D) (hAunitary : A.IsUnitary)
    (hAcompatible : A.IsCompatible D)
    (K : Set (E n)) (hKcompact : IsCompact K)
    (hKinvariant : ∀ γ x, x ∈ K → D.act γ x ∈ K)
    (O : Opens (E n)) (hKO : K ⊆ (O : Set (E n)))
    (hOcompact : IsCompact (closure (O : Set (E n))))
    (hOchart : closure (O : Set (E n)) ⊆ D.chart)
    (hOinvariant : ∀ γ x, x ∈ (O : Set (E n)) →
      D.act γ x ∈ (O : Set (E n)))
    (f : E n → V r) (g : Fin n → E n → V r)
    (hweak : WeakFirst (chartOpens D) f g)
    (hzero : ∀ᵐ x ∂(volume.restrict D.chart), x ∉ K → f x = 0)
    (hequivariant : ∀ γ : Γ,
      ∀ᵐ x ∂(KPChartL2.weightedMeasure n D.chart D.weight),
        f (D.act γ x) = D.cocycle γ x (f x))
    (hfinite : FiniteHw D.chart D.weight Q A f g)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (h : E n → V r)
      (herror : FiniteHw D.chart D.weight Q A
        (fun x => f x - h x)
        (fun j x => g j x - fderiv ℝ h x (coordinateDirection j))),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      tsupport h ⊆ (O : Set (E n)) ∧
      (∀ γ x, x ∈ D.chart → h (D.act γ x) = D.cocycle γ x (h x)) ∧
      Hw D.chart D.weight Q A (fun x => f x - h x)
        (fun j x => g j x - fderiv ℝ h x (coordinateDirection j)) herror < ε := by
  classical
  let Ω : Opens (E n) := chartOpens D
  have hKΩ : K ⊆ (Ω : Set (E n)) := fun x hx => hOchart (subset_closure (hKO hx))
  have hOΩ : (O : Set (E n)) ⊆ (Ω : Set (E n)) := fun x hx => hOchart (subset_closure hx)
  have hzero' : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0 :=
    hzero.mono (fun x hx hxK => hx hxK.2)
  obtain ⟨hFmemLp, hGmemLp, hFint, hGint, hFzero, hGzero, hFts, hGts, hFeq, hGeq⟩ :=
    compactZeroExtension_properties hKcompact hKΩ hweak hzero'
  have hFweak : WeakFirst (⊤ : Opens (E n)) (compactZeroExtension K f)
      (fun j => compactZeroExtension K (g j)) :=
    compactZeroExtension_weakFirst hKcompact hKΩ hweak hzero'
  obtain ⟨u, hu_smooth, hu_comp, hu_supp, hFmemLp2, hGmemLp2, hu_memLp, hud_memLp,
      herr_u, hderr_u, hFu_tend, hGd_tend⟩ :=
    exists_nonequivariant_h1_sequence (n := n) (r := r) (by omega) (by omega)
      (Ω := Ω) (O := O) hKcompact hKO hOΩ hweak hzero'
  set C : Set (E n) := closure (O : Set (E n)) with hCdef
  obtain ⟨c_w, C_w, κ, Λ, M, hcw, hCw, hκ, hΛ, hM, hbounds⟩ :=
    exists_compact_metric_bounds Ω C hOcompact hOchart D.weight D.smooth_weight
      D.positive_weight Q A
  have havg := kp_cont_compact_h1_smooth_average_bound n r hn hr Γ D C hOcompact hOchart
  dsimp only at havg
  obtain ⟨B, P, hB1, hPnorm, hPid, hPrange, hPformula, hlast⟩ := havg
  let v : ℕ → E n → V r :=
    fun m => KPChartL2.average n r Γ D.chart D.act D.cocycle (u m)
  have hvm (m : ℕ) :=
    (hlast (O : Set (E n)) O.isOpen (fun x hx => hOchart (subset_closure hx))
      hOinvariant (by rw [hCdef])).1
      (u m) (hu_smooth m) (hu_comp m) (hu_supp m)
  have hv_smooth (m : ℕ) : ContDiff ℝ ∞ (v m) := (hvm m).1
  have hv_comp (m : ℕ) : HasCompactSupport (v m) := (hvm m).2.1
  have hv_supp (m : ℕ) : tsupport (v m) ⊆ (O : Set (E n)) := (hvm m).2.2.1
  have hv_equi (m : ℕ) : ∀ γ x, x ∈ D.chart →
      v m (D.act γ x) = D.cocycle γ x (v m x) := (hvm m).2.2.2.1
  have havg_sub (m m' : ℕ) :
      KPChartL2.average n r Γ D.chart D.act D.cocycle (fun x => u m x - u m' x)
        = fun x => v m x - v m' x := by
    funext x
    simp only [v, KPChartL2.average]
    by_cases hx : x ∈ D.chart
    · simp only [Set.indicator_of_mem hx]
      rw [← smul_sub, ← Finset.sum_sub_distrib]
      refine congrArg (fun z => (Fintype.card Γ : ℂ)⁻¹ • z) ?_
      exact Finset.sum_congr rfl (fun γ _ => by simp only [Pi.sub_apply, map_sub])
    · simp only [Set.indicator_of_notMem hx, Pi.sub_apply]
      simp
  have hvm_data (m : ℕ) := (hvm m).2.2.2.2
  choose h0u h0v huμ hvμ hrest using hvm_data
  have hvm_bound (m : ℕ) := (hrest m).1
  have hvm_P (m : ℕ) := (hrest m).2

  have hfd_u (m m' : ℕ) : (fun x => fderiv ℝ (fun y => u m y - u m' y) x) =
      fun x => fderiv ℝ (u m) x - fderiv ℝ (u m') x := by
    funext x
    exact fderiv_sub (((hu_smooth m).differentiable (by simp)).differentiableAt)
      (((hu_smooth m').differentiable (by simp)).differentiableAt)
  have hfd_v (m m' : ℕ) : (fun x => fderiv ℝ (fun y => v m y - v m' y) x) =
      fun x => fderiv ℝ (v m) x - fderiv ℝ (v m') x := by
    funext x
    exact fderiv_sub (((hv_smooth m).differentiable (by simp)).differentiableAt)
      (((hv_smooth m').differentiable (by simp)).differentiableAt)

  have hdiffH0 (m m' : ℕ) :
      ∃ (h0u' : FiniteH0 Set.univ (fun x => u m x - u m' x)
            (fun j x => fderiv ℝ (fun y => u m y - u m' y) x (coordinateDirection j)))
        (h0v' : FiniteH0 Set.univ
            (KPChartL2.average n r Γ D.chart D.act D.cocycle (fun x => u m x - u m' x))
            (fun j x => fderiv ℝ
              (KPChartL2.average n r Γ D.chart D.act D.cocycle (fun x => u m x - u m' x)) x
              (coordinateDirection j))),
        H0 Set.univ (KPChartL2.average n r Γ D.chart D.act D.cocycle (fun x => u m x - u m' x))
            (fun j x => fderiv ℝ
              (KPChartL2.average n r Γ D.chart D.act D.cocycle (fun x => u m x - u m' x)) x
              (coordinateDirection j)) h0v' ≤
          B * H0 Set.univ (fun x => u m x - u m' x)
            (fun j x => fderiv ℝ (fun y => u m y - u m' y) x (coordinateDirection j)) h0u' := by
    have hd := (hlast (O : Set (E n)) O.isOpen (fun x hx => hOchart (subset_closure hx))
      hOinvariant (by rw [hCdef])).1 (fun x => u m x - u m' x)
      ((hu_smooth m).sub (hu_smooth m')) ((hu_comp m).sub (hu_comp m'))
      ((tsupport_sub (u m) (u m')).trans (Set.union_subset (hu_supp m) (hu_supp m')))
    obtain ⟨h0u', h0v', _huμ, _hvμ, hb, _hP⟩ := hd.2.2.2.2
    exact ⟨h0u', h0v', hb⟩
  choose h0ud h0vd hbd using hdiffH0

  have hcongr2 (m m' : ℕ) (j : Fin n) : (fun x => fderiv ℝ
        (KPChartL2.average n r Γ D.chart D.act D.cocycle (fun x => u m x - u m' x)) x
        (coordinateDirection j)) =
      fun x => fderiv ℝ (v m) x (coordinateDirection j) - fderiv ℝ (v m') x (coordinateDirection j) := by
    funext x
    rw [havg_sub m m']
    exact congrArg (fun T => T (coordinateDirection j))
      (fderiv_sub (((hv_smooth m).differentiable (by simp)).differentiableAt)
        (((hv_smooth m').differentiable (by simp)).differentiableAt))
  have hderiv_bound (m m' : ℕ) (j : Fin n) :
      l2Norm (volume.restrict Set.univ)
        (fun x => fderiv ℝ (v m) x (coordinateDirection j)
          - fderiv ℝ (v m') x (coordinateDirection j))
        (((h0v m).2 j).sub ((h0v m').2 j)) ≤
      B * H0 Set.univ (fun x => u m x - u m' x)
        (fun j x => fderiv ℝ (fun y => u m y - u m' y) x (coordinateDirection j)) (h0ud m m') := by
    rw [l2Norm_congr_ae (volume.restrict Set.univ)
      (Filter.Eventually.of_forall (fun x => congrFun (hcongr2 m m' j).symm x))
      (((h0v m).2 j).sub ((h0v m').2 j)) ((h0vd m m').2 j)]
    exact (l2Norm_deriv_le_H0 _ _ (h0vd m m') j).trans (hbd m m')
  have hnorm (μ : Measure (E n)) (a b : E n → V r) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      ‖ha.toLp a - hb.toLp b‖ = l2Norm μ (a - b) (ha.sub hb) := by
    rw [← ha.toLp_sub hb, Lp.norm_toLp, ← l2Norm_eq_toReal μ (a - b) (ha.sub hb)]
  have huLp_tend : Tendsto (fun m => (hu_memLp m).toLp (u m)) atTop
      (𝓝 (hFmemLp.toLp (compactZeroExtension K f))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [hnorm, l2Norm, Pi.sub_apply] using hFu_tend
  have hudLp_tend (j : Fin n) : Tendsto
      (fun m => (hud_memLp m j).toLp (fun x => fderiv ℝ (u m) x (coordinateDirection j)))
      atTop (𝓝 ((hGmemLp j).toLp (compactZeroExtension K (g j)))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [hnorm, l2Norm, Pi.sub_apply] using hGd_tend j
  have hfst : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    exact tendsto_atTop.mpr fun b => eventually_atTop.mpr ⟨(b, 0), fun p hp => hp.1⟩
  have hsnd : Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    exact tendsto_atTop.mpr fun b => eventually_atTop.mpr ⟨(0, b), fun p hp => hp.2⟩
  have hu_diff_tend : Tendsto (fun p : ℕ × ℕ =>
      l2Norm volume (u p.1 - u p.2) ((hu_memLp p.1).sub (hu_memLp p.2))) atTop (𝓝 0) := by
    have ht := ((huLp_tend.comp hfst).sub (huLp_tend.comp hsnd)).norm
    simpa only [Function.comp_apply, sub_self, norm_zero, hnorm, l2Norm, Pi.sub_apply] using ht
  have hud_diff_tend (j : Fin n) : Tendsto (fun p : ℕ × ℕ =>
      l2Norm volume (fun x => fderiv ℝ (u p.1) x (coordinateDirection j) -
        fderiv ℝ (u p.2) x (coordinateDirection j))
        ((hud_memLp p.1 j).sub (hud_memLp p.2 j))) atTop (𝓝 0) := by
    have ht := (((hudLp_tend j).comp hfst).sub ((hudLp_tend j).comp hsnd)).norm
    simpa only [Function.comp_apply, sub_self, norm_zero, hnorm, l2Norm, Pi.sub_apply] using ht
  have huH0_diff_tend : Tendsto (fun p : ℕ × ℕ =>
      H0 Set.univ (fun x => u p.1 x - u p.2 x)
        (fun j x => fderiv ℝ (fun y => u p.1 y - u p.2 y) x (coordinateDirection j))
        (h0ud p.1 p.2)) atTop (𝓝 0) := by
    have hs := tendsto_finset_sum Finset.univ fun j _ => (hud_diff_tend j).pow 2
    have ht := hu_diff_tend.add (Real.continuous_sqrt.continuousAt.tendsto.comp hs)
    simp only [Finset.sum_const_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Real.sqrt_zero, add_zero] at ht
    convert ht using 1
    funext p
    unfold H0 l2Norm
    simp only [Measure.restrict_univ]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    apply integral_congr_ae
    filter_upwards with x
    rw [congrFun (hfd_u p.1 p.2) x, ContinuousLinearMap.sub_apply]
  have hvd_mem (m : ℕ) (j : Fin n) : MemLp
      (fun x => fderiv ℝ (v m) x (coordinateDirection j)) 2 volume :=
    memLp_restrict_univ ((h0v m).2 j)
  have hvd_Cauchy (j : Fin n) : CauchySeq (fun m =>
      (hvd_mem m j).toLp (fun x => fderiv ℝ (v m) x (coordinateDirection j))) := by
    apply cauchySeq_Lp_of_tendsto_l2Norm
    apply squeeze_zero (fun p => l2Norm_nonneg _ _ _) (fun p => ?_)
      (by simpa using huH0_diff_tend.const_mul B)
    simpa only [l2Norm, Measure.restrict_univ, Pi.sub_apply] using hderiv_bound p.1 p.2 j
  choose q hq_limit using fun j => cauchySeq_tendsto_of_complete (hvd_Cauchy j)
  have hqder_limit (j : Fin n) : Tendsto
      (fun m => eLpNorm ((fun x => fderiv ℝ (v m) x (coordinateDirection j)) - (q j : E n → V r))
        2 volume) atTop (𝓝 0) := by
    have ht := tendsto_iff_edist_tendsto_0.mp (hq_limit j)
    convert ht using 1
    funext m
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hvd_mem m j).coeFn_toLp.symm.sub (Filter.EventuallyEq.rfl))
  have hfμ := hfinite.1
  have hfclass : hfμ.toLp f ∈ KPChartL2.equivariantL2 n r Γ
      (KPChartL2.weightedMeasure n D.chart D.weight) D.act D.cocycle := by
    intro γ
    filter_upwards [hfμ.coeFn_toLp,
      (D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp hfμ.coeFn_toLp,
      hequivariant γ] with x hx hγ he
    change (hfμ.toLp f) (D.act γ x) = f (D.act γ x) at hγ
    rw [hγ, hx]
    exact he
  have hPfix : P (hfμ.toLp f) = hfμ.toLp f := by
    obtain ⟨y, hy⟩ := hPrange.symm ▸ hfclass
    rw [← hy, hPid]
  have hFμeq : compactZeroExtension K f =ᵐ[KPChartL2.weightedMeasure n D.chart D.weight] f :=
    hFeq.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  have hFμ : MemLp (compactZeroExtension K f) 2
      (KPChartL2.weightedMeasure n D.chart D.weight) := hfμ.ae_eq hFμeq.symm
  have hprojected_limit (hu_limit : Tendsto (fun m => (huμ m).toLp (u m))
      atTop (𝓝 (hfμ.toLp f))) : Tendsto
      (fun m => eLpNorm (v m - f) 2 (KPChartL2.weightedMeasure n D.chart D.weight))
      atTop (𝓝 0) := by
    have ht := tendsto_iff_edist_tendsto_0.mp ((P.continuous.tendsto _).comp hu_limit)
    rw [hPfix] at ht
    convert ht using 1
    funext m
    simp only [Function.comp_apply]
    rw [← hvm_P m, Lp.edist_toLp_toLp]
  have huerror_supp (m : ℕ) : ∀ x ∉ C, u m x - compactZeroExtension K f x = 0 := by
    intro x hx
    have hxK : x ∉ K := fun hk => hx (subset_closure (hKO hk))
    have hxu : x ∉ tsupport (u m) := fun hu => hx (subset_closure (hu_supp m hu))
    rw [image_eq_zero_of_notMem_tsupport hxu, hFzero x hxK, sub_self]
  have hverror_supp (m : ℕ) : ∀ x ∉ C, v m x - compactZeroExtension K f x = 0 := by
    intro x hx
    have hxK : x ∉ K := fun hk => hx (subset_closure (hKO hk))
    have hxv : x ∉ tsupport (v m) := fun hv => hx (subset_closure (hv_supp m hv))
    rw [image_eq_zero_of_notMem_tsupport hxv, hFzero x hxK, sub_self]
  have hENN_tend (a b : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤)
      (hb : Tendsto b atTop (𝓝 0)) (hab : ∀ m, a m ≤ c * b m) :
      Tendsto a atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using ENNReal.Tendsto.const_mul hb (Or.inr hc))
    · exact fun _ => bot_le
    · exact hab
  have hv_limit : Tendsto (fun m => eLpNorm (v m - compactZeroExtension K f) 2 volume)
      atTop (𝓝 0) := by
    have huμ_limit : Tendsto (fun m => eLpNorm (u m - compactZeroExtension K f) 2
        (KPChartL2.weightedMeasure n D.chart D.weight)) atTop (𝓝 0) := by
      apply hENN_tend _ _ (ENNReal.ofReal (Real.sqrt C_w)) ENNReal.ofReal_ne_top
        (tendsto_eLpNorm_of_tendsto_l2Norm volume _ herr_u hFu_tend)
      intro m
      exact (compact_weighted_l2_upper Ω C hOcompact hOchart D.weight C_w hCw
        (fun x hx => (hbounds x hx).1.2) _
        (Filter.Eventually.of_forall (huerror_supp m)) (herr_u m)).choose_spec.1
    have huclass_limit : Tendsto (fun m => (huμ m).toLp (u m)) atTop (𝓝 (hfμ.toLp f)) := by
      apply tendsto_iff_edist_tendsto_0.mpr
      convert huμ_limit using 1
      funext m
      rw [Lp.edist_toLp_toLp]
      exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hFμeq.symm)
    have hvμ_limit : Tendsto (fun m => eLpNorm (v m - compactZeroExtension K f) 2
        (KPChartL2.weightedMeasure n D.chart D.weight)) atTop (𝓝 0) := by
      convert hprojected_limit huclass_limit using 1
      funext m
      exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hFμeq)
    apply hENN_tend _ _ (ENNReal.ofReal ((Real.sqrt c_w)⁻¹))
      ENNReal.ofReal_ne_top hvμ_limit
    intro m
    exact (compact_weighted_l2_lower Ω C hOcompact hOchart D.weight D.smooth_weight
      c_w hcw (fun x hx => (hbounds x hx).1.1) _
      (Filter.Eventually.of_forall (hverror_supp m)) ((hvμ m).sub hFμ)).choose_spec.1
  have hq_weak : WeakFirst (⊤ : Opens (E n)) (compactZeroExtension K f)
      (fun j => (q j : E n → V r)) := by
    apply weakFirst_of_smooth_compactSupport_l2_limit
      (⊤ : Opens (E n)) v (compactZeroExtension K f) (fun j => (q j : E n → V r))
      hv_smooth hv_comp (fun _ => Set.subset_univ _)
    · simpa only [Opens.coe_top, Measure.restrict_univ] using hFmemLp
    · intro j
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (q j)
    · simpa only [Opens.coe_top, Measure.restrict_univ] using hv_limit
    · intro j
      simpa only [Opens.coe_top, Measure.restrict_univ] using hqder_limit j
  have hqeq (j : Fin n) : (q j : E n → V r) =ᵐ[volume] compactZeroExtension K (g j) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      hq_weak.derivative_ae_eq hFweak j
  have hvd_limit (j : Fin n) : Tendsto
      (fun m => eLpNorm ((fun x => fderiv ℝ (v m) x (coordinateDirection j)) -
        compactZeroExtension K (g j)) 2 volume) atTop (𝓝 0) := by
    convert hqder_limit j using 1
    funext m
    exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub (hqeq j).symm)
  have hv_mem (m : ℕ) : MemLp (v m) 2 volume := memLp_restrict_univ (h0v m).1
  have herror0 (m : ℕ) : FiniteH0 D.chart (fun x => f x - v m x)
      (fun j x => g j x - fderiv ℝ (v m) x (coordinateDirection j)) := by
    constructor
    · exact (((hFmemLp.sub (hv_mem m)).mono_measure Measure.restrict_le_self).ae_eq
        (hFeq.sub Filter.EventuallyEq.rfl))
    · intro j
      exact ((((hGmemLp j).sub (hvd_mem m j)).mono_measure Measure.restrict_le_self).ae_eq
        ((hGeq j).sub Filter.EventuallyEq.rfl))
  have hrestrict (a : E n → V r) (ha : MemLp a 2 volume) :
      l2Norm (volume.restrict D.chart) a (ha.mono_measure Measure.restrict_le_self) ≤
        l2Norm volume a ha := by
    rw [l2Norm_eq_toReal, l2Norm_eq_toReal]
    exact ENNReal.toReal_mono ha.eLpNorm_ne_top
      (eLpNorm_mono_measure a Measure.restrict_le_self)
  have hferror_tend : Tendsto
      (fun m => l2Norm (volume.restrict D.chart) (fun x => f x - v m x) (herror0 m).1)
      atTop (𝓝 0) := by
    have ht := tendsto_l2Norm_of_tendsto_eLpNorm volume v (compactZeroExtension K f)
      (fun m => (hv_mem m).sub hFmemLp) hv_limit
    apply squeeze_zero (fun m => l2Norm_nonneg _ _ _) (fun m => ?_) ht
    change l2Norm (volume.restrict D.chart) (f - v m) _ ≤ _
    rw [l2Norm_congr_ae (volume.restrict D.chart) (hFeq.symm.sub Filter.EventuallyEq.rfl) (herror0 m).1
      ((hFmemLp.sub (hv_mem m)).mono_measure Measure.restrict_le_self)]
    calc
      _ ≤ l2Norm volume (compactZeroExtension K f - v m) (hFmemLp.sub (hv_mem m)) :=
        hrestrict _ (hFmemLp.sub (hv_mem m))
      _ = l2Norm volume (v m - compactZeroExtension K f) ((hv_mem m).sub hFmemLp) := by
        simp only [l2Norm, Pi.sub_apply, norm_sub_rev]
  have hgerror_tend (j : Fin n) : Tendsto
      (fun m => l2Norm (volume.restrict D.chart)
        (fun x => g j x - fderiv ℝ (v m) x (coordinateDirection j)) ((herror0 m).2 j))
      atTop (𝓝 0) := by
    have ht := tendsto_l2Norm_of_tendsto_eLpNorm volume
      (fun m x => fderiv ℝ (v m) x (coordinateDirection j))
      (compactZeroExtension K (g j)) (fun m => (hvd_mem m j).sub (hGmemLp j)) (hvd_limit j)
    apply squeeze_zero (fun m => l2Norm_nonneg _ _ _) (fun m => ?_) ht
    change l2Norm (volume.restrict D.chart) (g j - (fun x => fderiv ℝ (v m) x (coordinateDirection j))) _ ≤ _
    rw [l2Norm_congr_ae (volume.restrict D.chart) ((hGeq j).symm.sub Filter.EventuallyEq.rfl) ((herror0 m).2 j)
      (((hGmemLp j).sub (hvd_mem m j)).mono_measure Measure.restrict_le_self)]
    calc
      _ ≤ l2Norm volume (compactZeroExtension K (g j) -
          (fun x => fderiv ℝ (v m) x (coordinateDirection j)))
          ((hGmemLp j).sub (hvd_mem m j)) := hrestrict _ ((hGmemLp j).sub (hvd_mem m j))
      _ = l2Norm volume ((fun x => fderiv ℝ (v m) x (coordinateDirection j)) -
          compactZeroExtension K (g j)) ((hvd_mem m j).sub (hGmemLp j)) := by
        simp only [l2Norm, Pi.sub_apply, norm_sub_rev]
  have hH0error_tend : Tendsto (fun m => H0 D.chart (fun x => f x - v m x)
      (fun j x => g j x - fderiv ℝ (v m) x (coordinateDirection j)) (herror0 m))
      atTop (𝓝 0) := by
    have hs := tendsto_finset_sum Finset.univ fun j _ => (hgerror_tend j).pow 2
    have ht := hferror_tend.add (Real.continuous_sqrt.continuousAt.tendsto.comp hs)
    simpa only [H0, Function.comp_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
      Real.sqrt_zero, add_zero] using ht
  have hferror_supp (m : ℕ) : ∀ᵐ x ∂volume.restrict D.chart,
      x ∉ C → f x - v m x = 0 := by
    filter_upwards [hzero] with x hx hxC
    have hxK : x ∉ K := fun hk => hxC (subset_closure (hKO hk))
    have hxv : x ∉ tsupport (v m) := fun hv => hxC (subset_closure (hv_supp m hv))
    rw [hx hxK, image_eq_zero_of_notMem_tsupport hxv, sub_self]
  have hgzero := weakFirst_zero_off_compact hKcompact hKΩ hweak hzero'
  have hgerror_supp (m : ℕ) (j : Fin n) : ∀ᵐ x ∂volume.restrict D.chart,
      x ∉ C → g j x - fderiv ℝ (v m) x (coordinateDirection j) = 0 := by
    filter_upwards [hgzero j, ae_restrict_mem D.open_chart.measurableSet] with x hx hxΩ hxC
    have hxK : x ∉ K := fun hk => hxC (subset_closure (hKO hk))
    have hxder : x ∉ tsupport (fun x => fderiv ℝ (v m) x (coordinateDirection j)) := by
      intro hs
      exact hxC (subset_closure (hv_supp m ((tsupport_fderiv_apply_subset ℝ (f := v m)
        (coordinateDirection j)) hs)))
    rw [hx ⟨hxΩ, hxK⟩, image_eq_zero_of_notMem_tsupport hxder, sub_self]
  obtain ⟨c, C', hc, hC', hnormbounds⟩ := kp_cont_compact_h1_metric_bounds
    Ω C hOcompact hOchart D.weight D.smooth_weight D.positive_weight Q A
  let hwerror (m : ℕ) : FiniteHw D.chart D.weight Q A (fun x => f x - v m x)
      (fun j x => g j x - fderiv ℝ (v m) x (coordinateDirection j)) :=
    (compact_finiteH0_iff_finiteHw Ω C hOcompact hOchart D.weight D.smooth_weight
      D.positive_weight Q A _ _ (herror0 m).1.aestronglyMeasurable
      (fun j => ((herror0 m).2 j).aestronglyMeasurable)
      (hferror_supp m) (hgerror_supp m)).mp (herror0 m)
  have herr_le (m : ℕ) : Hw D.chart D.weight Q A (fun x => f x - v m x)
      (fun j x => g j x - fderiv ℝ (v m) x (coordinateDirection j)) (hwerror m) ≤
      C' * H0 D.chart (fun x => f x - v m x)
        (fun j x => g j x - fderiv ℝ (v m) x (coordinateDirection j)) (herror0 m) :=
    (hnormbounds _ _ (hferror_supp m) (hgerror_supp m) (herror0 m)).2
  have ht : Tendsto (fun m => C' * H0 D.chart (fun x => f x - v m x)
      (fun j x => g j x - fderiv ℝ (v m) x (coordinateDirection j)) (herror0 m))
      atTop (𝓝 0) := by simpa using hH0error_tend.const_mul C'
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨v m, hwerror m, hv_smooth m, hv_comp m, hv_supp m, hv_equi m,
    (herr_le m).trans_lt hm⟩

end DedekindZetaZeroFree

end
