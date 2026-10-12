module

public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.CompactJetTopology

@[expose] public section

set_option maxHeartbeats 800000
noncomputable section
namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.ContourLift
open KPContLocalNorm MeasureTheory Filter Set
open scoped Topology

 def assemble {n : ℕ} (v : Fin n → ℂ) : Space n →L[ℝ] ℂ :=
  ∑ i, (EuclideanSpace.proj i).smulRight (v i)

private lemma assemble_deriv {n : ℕ} (u : Space n → ℂ) (x : Space n) :
    fderiv ℝ u x = assemble (fun i => coordinateDerivativeList [i] u x) := by
  classical
  apply ContinuousLinearMap.ext
  intro y
  have he : y = ∑ i : Fin n, y i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  rw [he]
  simp [assemble, coordinateDerivativeList, map_sum, EuclideanSpace.single_apply]

private lemma list_index {n : ℕ} (l : List (Fin n)) :
    ∃ m, ∃ α : MultiIndex n m, l.Perm α.directions := by
  classical
  let m := ∑ i : Fin n, l.count i
  let α : MultiIndex n m := ⟨fun i => ⟨l.count i, by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (l.count j)) (Finset.mem_univ i)
    dsimp [m]; omega⟩, by simp [m]⟩
  refine ⟨m, α, List.perm_iff_count.mpr ?_⟩
  intro i
  rw [MultiIndex.directions, List.count_flatMap,
    ← List.sum_toFinset _ (List.nodup_finRange n)]
  simp [α, Function.comp_def, List.count_replicate]

private lemma list_sub {n : ℕ} (B : LocalBall n) (u v : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v B.carrier) (l : List (Fin n)) :
    EqOn (coordinateDerivativeList l (fun y => u y - v y))
      (fun y => coordinateDerivativeList l u y - coordinateDerivativeList l v y) B.carrier := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    have he := (eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) ih).fderiv_eq (𝕜 := ℝ)
    have hd (w : Space n → ℂ) (hw : ContDiffOn ℝ (⊤ : ℕ∞) w B.carrier) :=
      ((WeakJets.Raw.coordinateDerivativeList_smooth_on l hw).differentiableOn (by simp)).differentiableAt
        (Metric.isOpen_ball.mem_nhds hx)
    simp only [coordinateDerivativeList]
    rw [he]
    exact congrArg (fun L : Space n →L[ℝ] ℂ => L (EuclideanSpace.single i 1))
      (fderiv_sub (hd u hu) (hd v hv))

private lemma list_family_continuous {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier)
    (hj : Raw.JetContinuousOn B f O)
    (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (l : List (Fin n)) :
    Continuous (fun z : O => (⟨fun x : K => coordinateDerivativeList l (f z) x,
      ((WeakJets.Raw.coordinateDerivativeList_smooth_on l (hf z z.property)).continuousOn.mono hKB).restrict⟩ : C(K, ℂ))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨m, α, hp⟩ := list_index l
  apply Metric.continuous_iff.mpr
  intro z₀ ε hε
  obtain ⟨δ, hδ, hb⟩ := hj z₀ z₀.property K hK hKB m ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_lt_iff _ hε).mpr
  intro x
  change ‖coordinateDerivativeList l (f z) x - coordinateDerivativeList l (f z₀) x‖ < ε
  have he := list_sub B _ _ (hf z z.property) (hf z₀ z₀.property) l (hKB x.property)
  dsimp only at he
  rw [← he]
  rw [WeakJets.Raw.coordinateDerivativeList_perm_on hp
    ((hf z z.property).sub (hf z₀ z₀.property)) (hKB x.property)]
  exact hb z z.property hz α x

private lemma joint_list {n : ℕ} (B : LocalBall n) (O : Set ℂ)
    (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier)
    (hj : Raw.JetContinuousOn B f O) (K : Set (Space n))
    (hK : IsCompact K) (hKB : K ⊆ B.carrier) (l : List (Fin n))
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hc : Metric.closedBall c ρ ⊆ O) :
    Continuous (fun p : K × ℝ => coordinateDerivativeList l (f (circleMap c ρ p.2)) p.1) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hz : ∀ t, circleMap c ρ t ∈ O := fun t =>
    hc (Metric.sphere_subset_closedBall (circleMap_mem_sphere c hρ.le t))
  have hh := (list_family_continuous B O f hf hj K hK hKB l).comp
    ((continuous_circleMap c ρ).subtype_mk hz)
  exact continuous_eval.comp ((hh.comp continuous_snd).prodMk continuous_fst)

private lemma compact_integral_deriv {n : ℕ} (B : LocalBall n)
    (g : List (Fin n) → Space n → ℝ → ℂ)
    (hs : ∀ l t, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => g l x t) B.carrier)
    (hd : ∀ l i x t, x ∈ B.carrier →
      fderiv ℝ (fun y => g l y t) x (EuclideanSpace.single i 1) = g (i :: l) x t)
    (hj : ∀ K : Set (Space n), IsCompact K → K ⊆ B.carrier →
      ∀ l, Continuous (fun p : K × ℝ => g l p.1 p.2))
    (l : List (Fin n)) {x : Space n} (hx : x ∈ B.carrier) :
    HasFDerivAt (fun x => ∫ t in Icc 0 (2 * Real.pi), g l x t)
      (assemble (fun i => ∫ t in Icc 0 (2 * Real.pi), g (i :: l) x t)) x := by
  classical
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hx)
  let K := Metric.closedBall x (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKB : K ⊆ B.carrier := fun y hy => hrB (Metric.mem_ball.mpr
    ((Metric.mem_closedBall.mp hy).trans_lt (by linarith)))
  have hxK : x ∈ K := Metric.mem_closedBall_self (by positivity)
  let g' : Space n → ℝ → Space n →L[ℝ] ℂ := fun y t => assemble (fun i => g (i :: l) y t)
  have hc' : Continuous (fun p : K × ℝ => g' p.1 p.2) := by
    apply continuous_finset_sum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ (Space n) ℂ (EuclideanSpace.proj i)).continuous.comp
      (hj K hK hKB (i :: l))
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).exists_bound_of_continuousOn hc'.continuousOn
  let μ := volume.restrict (Icc (0 : ℝ) (2 * Real.pi))
  have hcont (k : List (Fin n)) (y : Space n) (hy : y ∈ K) : Continuous (g k y) :=
    (hj K hK hKB k).comp ((continuous_const (y := (⟨y, hy⟩ : K))).prodMk continuous_id)
  have hi' : Integrable (g' x) μ :=
    (hc'.comp ((continuous_const (y := (⟨x, hxK⟩ : K))).prodMk continuous_id)).continuousOn.integrableOn_compact isCompact_Icc
  have HH := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (F := g l) (F' := g') (s := K) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x (by positivity))
    (by filter_upwards [Metric.closedBall_mem_nhds x (show 0 < r / 2 by positivity)] with y hy
        exact (hcont l y hy).aestronglyMeasurable)
    ((hcont l x hxK).continuousOn.integrableOn_compact isCompact_Icc)
    hi'.aestronglyMeasurable
    (by
      rw [ae_restrict_iff' measurableSet_Icc]
      exact Eventually.of_forall fun t ht y hy => hC (⟨y, hy⟩, t) ⟨mem_univ _, ht⟩)
    (integrable_const C)
    (Eventually.of_forall fun t y hy => by
      have hh := ((hs l t).differentiableOn (by simp)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (hKB hy))
      convert hh.hasFDerivAt using 1
      rw [assemble_deriv]
      change assemble (fun i => g (i :: l) y t) = assemble _
      congr 1
      funext i
      exact (hd l i y t (hKB hy)).symm)
  have he : (∫ t, g' x t ∂μ) = assemble (fun i => ∫ t, g (i :: l) x t ∂μ) := by
    simp only [g', assemble]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      exact (ContinuousLinearMap.smulRightL ℝ (Space n) ℂ (EuclideanSpace.proj i)).integral_comp_comm
        ((hcont (i :: l) x hxK).continuousOn.integrableOn_compact isCompact_Icc)
    · intro i _
      exact (ContinuousLinearMap.smulRightL ℝ (Space n) ℂ (EuclideanSpace.proj i)).integrable_comp
        ((hcont (i :: l) x hxK).continuousOn.integrableOn_compact isCompact_Icc)
  exact he ▸ HH

theorem coefficient_smooth_and_derivatives {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier)
    (hjets : Raw.JetContinuousOn B f O)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ O)
    (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => (cauchyPowerSeries (fun z => f z x) c ρ j) (fun _ => (1 : ℂ)))
      B.carrier ∧
    ∀ (m : ℕ) (α : MultiIndex n m),
      Set.EqOn
        (coordinateDerivative α
          (fun x => (cauchyPowerSeries (fun z => f z x) c ρ j) (fun _ => (1 : ℂ))))
        (fun x => (cauchyPowerSeries (fun z => coordinateDerivative α (f z) x)
          c ρ j) (fun _ => (1 : ℂ))) B.carrier := by
  classical
  have hz (t : ℝ) : circleMap c ρ t ∈ O :=
    hclosed (Metric.sphere_subset_closedBall (circleMap_mem_sphere c hρ.le t))
  have hn (t : ℝ) : circleMap c ρ t - c ≠ 0 := by
    have hh := circleMap_mem_sphere c hρ.le t
    rw [Metric.mem_sphere, dist_eq_norm] at hh
    intro he
    rw [he, norm_zero] at hh
    linarith
  let k : ℝ → ℂ := fun t => (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    deriv (circleMap c ρ) t * (circleMap c ρ t - c)⁻¹ ^ j * (circleMap c ρ t - c)⁻¹
  have hk : Continuous k := by
    dsimp [k]
    apply Continuous.mul
    · apply Continuous.mul
      · exact continuous_const.mul (by
        change Continuous (fun t => deriv (circleMap c ρ) t)
        simp only [deriv_circleMap]
        exact (continuous_circleMap 0 ρ).mul continuous_const)
      · exact (((continuous_circleMap c ρ).sub continuous_const).inv₀ hn).pow j
    · exact ((continuous_circleMap c ρ).sub continuous_const).inv₀ hn
  let g : List (Fin n) → Space n → ℝ → ℂ := fun l x t =>
    k t * coordinateDerivativeList l (f (circleMap c ρ t)) x
  let J : List (Fin n) → Space n → ℂ := fun l x => ∫ t in Icc 0 (2 * Real.pi), g l x t
  have hs (l : List (Fin n)) (t : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => g l x t) B.carrier :=
    contDiffOn_const.mul (WeakJets.Raw.coordinateDerivativeList_smooth_on l (hf _ (hz t)))
  have hd (l : List (Fin n)) (i : Fin n) (x : Space n) (t : ℝ) (hx : x ∈ B.carrier) :
      fderiv ℝ (fun y => g l y t) x (EuclideanSpace.single i 1) = g (i :: l) x t := by
    have hh := ((WeakJets.Raw.coordinateDerivativeList_smooth_on l (hf _ (hz t))).differentiableOn
      (by simp)).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
    have he := (hh.hasFDerivAt.const_smul (k t)).fderiv
    exact congrArg (fun L : Space n →L[ℝ] ℂ => L (EuclideanSpace.single i 1)) he
  have hj (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier) (l : List (Fin n)) :
      Continuous (fun p : K × ℝ => g l p.1 p.2) :=
    (hk.comp continuous_snd).mul (joint_list B O f hf hjets K hK hKB l c ρ hρ hclosed)
  have hJd (l : List (Fin n)) (x : Space n) (hx : x ∈ B.carrier) :
      HasFDerivAt (J l) (assemble (fun i => J (i :: l) x)) x :=
    compact_integral_deriv B g hs hd hj l hx
  have hJs (m : ℕ) (l : List (Fin n)) : ContDiffOn ℝ m (J l) B.carrier := by
    induction m generalizing l with
    | zero =>
      exact contDiffOn_zero.mpr (fun x hx => (hJd l x hx).differentiableAt.continuousAt.continuousWithinAt)
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen (show IsOpen B.carrier from Metric.isOpen_ball)]
      refine ⟨fun x hx => (hJd l x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have hh : ContDiffOn ℝ m (fun x => assemble (fun i => J (i :: l) x)) B.carrier := by
        apply ContDiffOn.sum
        intro i _
        exact (ContinuousLinearMap.smulRightL ℝ (Space n) ℂ (EuclideanSpace.proj i)).contDiff.comp_contDiffOn (ih (i :: l))
      exact hh.congr (fun x hx => (hJd l x hx).fderiv)
  have hJe (l : List (Fin n)) : EqOn (coordinateDerivativeList l (J [])) (J l) B.carrier := by
    induction l with
    | nil => intro x hx; rfl
    | cons i l ih =>
      intro x hx
      have he := (eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) ih).fderiv_eq (𝕜 := ℝ)
      simp only [coordinateDerivativeList]
      rw [he, (hJd l x hx).fderiv]
      simp [assemble, EuclideanSpace.single_apply, Pi.single_apply]
  have hformula (l : List (Fin n)) (x : Space n) :
      (cauchyPowerSeries (fun z => coordinateDerivativeList l (f z) x) c ρ j) (fun _ => (1 : ℂ)) = J l x := by
    rw [cauchyPowerSeries_apply, circleIntegral_def_Icc]
    simp only [one_div, smul_eq_mul, J, g, k]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by ring
  have hzero : (fun x => (cauchyPowerSeries (fun z => f z x) c ρ j) (fun _ => (1 : ℂ))) = J [] := by
    funext x
    exact hformula [] x
  rw [hzero]
  refine ⟨contDiffOn_infty.mpr (fun m => hJs m []), ?_⟩
  intro m α x hx
  exact (hJe α.directions hx).trans (hformula α.directions x).symm
end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly.ContourLift

end
