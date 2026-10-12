module

public import DedekindZetaZeroFree.Analysis.Sobolev.Cubes.CellAverageError

@[expose] public section

namespace DedekindZetaZeroFree
namespace KPCubeGraphRellich

open KPCubeAverage

noncomputable abbrev GradientSpace (n : ℕ) (a : ℝ) :=
  PiLp 2 (fun _ : Fin n => CubeLp n a)

noncomputable abbrev ProductSpace (n : ℕ) (a : ℝ) :=
  WithLp 2 (CubeLp n a × GradientSpace n a)

theorem smooth_coordinate_memLp (n : ℕ) (a : ℝ) (f : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin n) :
    MeasureTheory.MemLp (coordinateDerivative n f j) 2 (cubeMeasure n a) := by
  exact smooth_memLp n a (coordinateDerivative n f j)
    ((hf.fderiv_right (by simp)).clm_apply contDiff_const)

noncomputable def smoothJet (n : ℕ) (a : ℝ) (f : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ProductSpace n a :=
  WithLp.toLp 2
    ((smooth_memLp n a f hf).toLp f,
      WithLp.toLp 2 (fun j : Fin n =>
        (smooth_coordinate_memLp n a f hf j).toLp (coordinateDerivative n f j)))

noncomputable def smoothSubspace (n : ℕ) (a : ℝ) : Submodule ℂ (ProductSpace n a) :=
  Submodule.span ℂ {u | ∃ (f : Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f),
    u = smoothJet n a f hf}

private theorem coordinateDerivative_add (n : ℕ) (f g : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : Fin n) :
    coordinateDerivative n (f + g) j =
      coordinateDerivative n f j + coordinateDerivative n g j := by
  funext x
  simp only [coordinateDerivative, Pi.add_apply]
  rw [fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x),
    ContinuousLinearMap.add_apply]

private theorem coordinateDerivative_smul (n : ℕ) (f : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℂ) (j : Fin n) :
    coordinateDerivative n (c • f) j = c • coordinateDerivative n f j := by
  funext x
  simp only [coordinateDerivative, Pi.smul_apply]
  rw [fderiv_const_smul (hf.differentiable (by simp) x) c, ContinuousLinearMap.smul_apply]

private theorem smoothJet_zero (n : ℕ) (a : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (0 : Space n → ℂ)) :
    smoothJet n a (0 : Space n → ℂ) hf = 0 := by
  rw [smoothJet, WithLp.toLp_eq_zero, Prod.mk_eq_zero]
  refine ⟨MeasureTheory.MemLp.toLp_zero _, ?_⟩
  rw [WithLp.toLp_eq_zero]
  funext j
  have h0 : coordinateDerivative n (0 : Space n → ℂ) j = 0 := by
    funext x
    simp [coordinateDerivative, fderiv_zero]
  rw [MeasureTheory.MemLp.toLp_congr (smooth_coordinate_memLp n a 0 hf j)
    (smooth_memLp n a 0 hf) (Filter.EventuallyEq.of_eq h0)]
  exact MeasureTheory.MemLp.toLp_zero _

private theorem smoothJet_add (n : ℕ) (a : ℝ) (f g : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    smoothJet n a (f + g) (hf.add hg) = smoothJet n a f hf + smoothJet n a g hg := by
  rw [smoothJet, smoothJet, smoothJet, WithLp.ext_iff]
  simp only [WithLp.ofLp_toLp, WithLp.ofLp_add, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_
  · rw [← MeasureTheory.MemLp.toLp_add (smooth_memLp n a f hf) (smooth_memLp n a g hg)]
  · rw [← WithLp.toLp_add, WithLp.ext_iff, WithLp.ofLp_toLp]
    funext j
    simp only [Pi.add_apply]
    rw [← MeasureTheory.MemLp.toLp_add (smooth_coordinate_memLp n a f hf j)
      (smooth_coordinate_memLp n a g hg j)]
    exact MeasureTheory.MemLp.toLp_congr _ _
      (Filter.EventuallyEq.of_eq (coordinateDerivative_add n f g hf hg j))

private theorem smoothJet_smul (n : ℕ) (a : ℝ) (f : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℂ) :
    smoothJet n a (c • f) (hf.const_smul c) = c • smoothJet n a f hf := by
  rw [smoothJet, smoothJet, WithLp.ext_iff]
  simp only [WithLp.ofLp_toLp, WithLp.ofLp_smul, Prod.smul_mk]
  refine Prod.ext ?_ ?_
  · rw [← MeasureTheory.MemLp.toLp_const_smul c (smooth_memLp n a f hf)]
  · rw [← WithLp.toLp_smul, WithLp.ext_iff, WithLp.ofLp_toLp]
    funext j
    simp only [Pi.smul_apply]
    rw [← MeasureTheory.MemLp.toLp_const_smul c (smooth_coordinate_memLp n a f hf j)]
    exact MeasureTheory.MemLp.toLp_congr _ _
      (Filter.EventuallyEq.of_eq (coordinateDerivative_smul n f hf c j))

theorem mem_smoothSubspace_iff (n : ℕ) (a : ℝ) (u : ProductSpace n a) :
    u ∈ smoothSubspace n a ↔
      ∃ (f : Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f), u = smoothJet n a f hf := by
  constructor
  · intro hu
    rw [smoothSubspace] at hu
    refine Submodule.span_induction
      (p := fun x _ => ∃ (f : Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f),
        x = smoothJet n a f hf) ?_ ?_ ?_ ?_ hu
    · rintro v ⟨f, hf, rfl⟩
      exact ⟨f, hf, rfl⟩
    · exact ⟨0, contDiff_zero_fun, (smoothJet_zero n a contDiff_zero_fun).symm⟩
    · rintro v w _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, hf.add hg, (smoothJet_add n a f g hf hg).symm⟩
    · rintro c v _ ⟨f, hf, rfl⟩
      exact ⟨c • f, hf.const_smul c, (smoothJet_smul n a f hf c).symm⟩
  · rintro ⟨f, hf, rfl⟩
    rw [smoothSubspace]
    exact Submodule.subset_span ⟨f, hf, rfl⟩

noncomputable def graphSubspace (n : ℕ) (a : ℝ) : Submodule ℂ (ProductSpace n a) :=
  (smoothSubspace n a).topologicalClosure

noncomputable abbrev GraphSpace (n : ℕ) (a : ℝ) := graphSubspace n a

instance graphSpace_completeSpace (n : ℕ) (a : ℝ) : CompleteSpace (GraphSpace n a) :=
  inferInstanceAs (CompleteSpace (smoothSubspace n a).topologicalClosure)

noncomputable def projection (n : ℕ) (a : ℝ) : GraphSpace n a →L[ℂ] CubeLp n a :=
  (WithLp.fstL 2 ℂ (CubeLp n a) (GradientSpace n a)).comp (graphSubspace n a).subtypeL

private theorem norm_toLp_sq (n : ℕ) (a : ℝ) (f : Space n → ℂ)
    (hf : MeasureTheory.MemLp f 2 (cubeMeasure n a)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(cubeMeasure n a) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), MeasureTheory.L2.inner_def]
  rw [← integral_re
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hf.toLp f))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem smoothJet_gradient_norm_sq (n : ℕ) (a : ℝ) (f : Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ‖(smoothJet n a f hf).snd‖ ^ 2 =
      ∫ x, gradientEnergy n f x ∂(cubeMeasure n a) := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Fin n, ‖(smooth_coordinate_memLp n a f hf j).toLp
    (coordinateDerivative n f j)‖ ^ 2) = _
  simp_rw [norm_toLp_sq]
  unfold gradientEnergy
  rw [MeasureTheory.integral_finset_sum]
  intro j hj
  exact ((smooth_coordinate_memLp n a f hf j).norm).integrable_sq

theorem smoothJet_average_error_sq (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (hm : 1 ≤ m) (f : Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ‖(smoothJet n a f hf).fst - average n a m (smoothJet n a f hf).fst‖ ^ 2 ≤
      (((n : ℝ) + 1) * side a m) ^ 2 * ‖smoothJet n a f hf‖ ^ 2 := by
  have h := smooth_error_bound n hn a ha m hm f hf
  change ‖(smoothJet n a f hf).fst - average n a m (smoothJet n a f hf).fst‖ ^ 2 ≤
    ((n : ℝ) + 1) ^ 2 * side a m ^ 2 *
      (∫ x, gradientEnergy n f x ∂(cubeMeasure n a)) at h
  rw [← smoothJet_gradient_norm_sq n a f hf] at h
  have hp := WithLp.prod_norm_sq_eq_of_L2 (smoothJet n a f hf)
  have hg : ‖(smoothJet n a f hf).snd‖ ^ 2 ≤ ‖smoothJet n a f hf‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(smoothJet n a f hf).fst‖]
  calc
    _ ≤ ((n : ℝ) + 1) ^ 2 * side a m ^ 2 * ‖(smoothJet n a f hf).snd‖ ^ 2 := h
    _ ≤ ((n : ℝ) + 1) ^ 2 * side a m ^ 2 * ‖smoothJet n a f hf‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by ring

theorem projection_average_error (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (hm : 1 ≤ m) :
    ‖projection n a - (average n a m).comp (projection n a)‖ ≤
      ((n : ℝ) + 1) * (2 * a / (m : ℝ)) := by
  let C : ℝ := ((n : ℝ) + 1) * (2 * a / (m : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let T : ProductSpace n a →L[ℂ] CubeLp n a :=
    WithLp.fstL 2 ℂ (CubeLp n a) (GradientSpace n a) -
      (average n a m).comp (WithLp.fstL 2 ℂ (CubeLp n a) (GradientSpace n a))
  have hclosed : IsClosed {u : ProductSpace n a | ‖T u‖ ^ 2 ≤ C ^ 2 * ‖u‖ ^ 2} :=
    isClosed_le (T.continuous.norm.pow 2) (continuous_const.mul (continuous_norm.pow 2))
  have hs : (smoothSubspace n a : Set (ProductSpace n a)) ⊆
      {u | ‖T u‖ ^ 2 ≤ C ^ 2 * ‖u‖ ^ 2} := by
    intro u hu
    obtain ⟨f, hf, rfl⟩ := (mem_smoothSubspace_iff n a u).mp hu
    exact smoothJet_average_error_sq n hn a ha m hm f hf
  have hclosure := closure_minimal hs hclosed
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  have hu : ‖T (u : ProductSpace n a)‖ ^ 2 ≤ C ^ 2 * ‖(u : ProductSpace n a)‖ ^ 2 :=
    hclosure u.property
  change ‖T (u : ProductSpace n a)‖ ≤ C * ‖(u : ProductSpace n a)‖
  nlinarith [norm_nonneg (T (u : ProductSpace n a)),
    mul_nonneg hC (norm_nonneg (u : ProductSpace n a))]

set_option backward.isDefEq.respectTransparency.types false in

theorem projection_isCompactOperator (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (projection n a) := by
  classical
  have hcompact (m : ℕ) : IsCompactOperator (average n a m) := by
    let V := Submodule.span ℂ (Set.range (cellIndicator n a m))
    letI : FiniteDimensional ℂ V := cell_span_finiteDimensional n a m
    let A := (average n a m).codRestrict V (fun x =>
      average_range n a m ⟨x, rfl⟩)
    exact (isCompactOperator_of_locallyCompactSpace_dom A).clm_comp V.subtypeL
  apply isCompactOperator_of_tendsto
    (F := fun m : ℕ => (average n a m).comp (projection n a)) (l := Filter.atTop)
  · change Filter.Tendsto _ _ (@nhds _ (inferInstance : NormedAddCommGroup
      (GraphSpace n a →L[ℂ] CubeLp n a)).toUniformSpace.toTopologicalSpace _)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (f := fun m : ℕ => ‖(average n a m).comp (projection n a) - projection n a‖)
      (g := fun m : ℕ => ((n : ℝ) + 1) * (2 * a / (m : ℝ)))
      (Filter.Eventually.of_forall (fun m => ContinuousLinearMap.opNorm_nonneg _))
      (Filter.eventually_atTop.2 ⟨1, fun m hm => ?_⟩) ?_
    · have hrev : ‖(average n a m).comp (projection n a) - projection n a‖ =
          ‖projection n a - (average n a m).comp (projection n a)‖ := by
        rw [← ContinuousLinearMap.opNorm_neg]
        congr 1
        abel
      rw [hrev]
      exact projection_average_error n hn a ha m hm
    · simpa using ((tendsto_const_div_atTop_nhds_zero_nat (2 * a)).const_mul ((n : ℝ) + 1))
  · exact Filter.Eventually.of_forall (fun m =>
      (hcompact m).comp_clm (projection n a))

end KPCubeGraphRellich
end DedekindZetaZeroFree
