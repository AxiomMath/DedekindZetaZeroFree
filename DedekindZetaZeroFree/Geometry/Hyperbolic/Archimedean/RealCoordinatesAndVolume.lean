module

public import DedekindZetaZeroFree.Geometry.HyperbolicActionMetricAndVolume

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPArchRealCoordinates
variable (d : ℕ)

def coordinates : EuclideanSpace ℝ (Fin (d * 3)) ≃ₜ KPArch.Space d where
  toFun p i :=
    (⟨p (finProdFinEquiv (i, 0)), p (finProdFinEquiv (i, 1))⟩,
      p (finProdFinEquiv (i, 2)))
  invFun z := WithLp.toLp 2 (fun k =>
    let ik := finProdFinEquiv.symm k
    if ik.2 = 0 then (z ik.1).1.re
    else if ik.2 = 1 then (z ik.1).1.im else (z ik.1).2)
  left_inv := by
    intro p
    apply PiLp.ext
    intro k
    obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective k
    fin_cases j <;> simp
  right_inv := by
    intro z
    funext i
    apply Prod.ext
    · apply Complex.ext <;> simp
    · simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.prodMk
    · have hr := (EuclideanSpace.proj (𝕜 := ℝ) (finProdFinEquiv (i, (0 : Fin 3)))).continuous
      have hi := (EuclideanSpace.proj (𝕜 := ℝ) (finProdFinEquiv (i, (1 : Fin 3)))).continuous
      convert (Complex.continuous_ofReal.comp hr).add
        ((Complex.continuous_ofReal.comp hi).mul (continuous_const (y := Complex.I))) using 1
      funext p
      apply Complex.ext <;> simp
    · exact (EuclideanSpace.proj (finProdFinEquiv (i, 2))).continuous
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (d * 3) => ℝ)).comp
    apply continuous_pi
    intro k
    dsimp only
    split_ifs
    · exact Complex.continuous_re.comp (continuous_fst.comp (continuous_apply _))
    · exact Complex.continuous_im.comp (continuous_fst.comp (continuous_apply _))
    · exact continuous_snd.comp (continuous_apply _)

def density (p : EuclideanSpace ℝ (Fin (d * 3))) : ℝ :=
  KPArch.volumeDensity (d) (coordinates d p)

theorem coordinate_volume : Measure.map (coordinates d) volume =
    (volume : Measure (KPArch.Space d)) := by
  let e := (coordinates d).symm.toMeasurableEquiv.trans
    (MeasurableEquiv.toLp 2 (Fin (d * 3) → ℝ)).symm
  have he : MeasurePreserving e (volume : Measure (KPArch.Space d)) volume := by
    refine ⟨e.measurable, ?_⟩
    apply Eq.symm
    apply Measure.pi_eq
    intro s hs
    rw [MeasurableEquiv.map_apply]
    have hpre : e ⁻¹' Set.pi Set.univ s = Set.pi Set.univ
        (fun i : Fin (d) =>
          (Complex.measurableEquivRealProd ⁻¹'
            (s (finProdFinEquiv (i, 0)) ×ˢ s (finProdFinEquiv (i, 1)))) ×ˢ
            s (finProdFinEquiv (i, 2))) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
        Set.mem_prod, Complex.measurableEquivRealProd_apply]
      change (∀ k, (if (finProdFinEquiv.symm k).2 = 0 then (z (finProdFinEquiv.symm k).1).1.re
        else if (finProdFinEquiv.symm k).2 = 1 then (z (finProdFinEquiv.symm k).1).1.im
        else (z (finProdFinEquiv.symm k).1).2) ∈ s k) ↔ _
      constructor
      · intro h i
        exact ⟨⟨by simpa using h (finProdFinEquiv (i, 0)),
          by simpa using h (finProdFinEquiv (i, 1))⟩,
          by simpa using h (finProdFinEquiv (i, 2))⟩
      · intro h k
        obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective k
        fin_cases j
        · simpa using (h i).1.1
        · simpa using (h i).1.2
        · simpa using (h i).2
    rw [hpre, volume_pi_pi]
    simp_rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp_rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
        ((hs _ |>.prod (hs _)).nullMeasurableSet), Measure.volume_eq_prod, Measure.prod_prod]
    rw [← finProdFinEquiv.prod_comp]
    simp only [Fintype.prod_prod_type, Fin.prod_univ_three]
  have ht := (PiLp.volume_preserving_toLp (Fin (d * 3))).comp he
  have hf : WithLp.toLp 2 ∘ e = (coordinates d).symm := rfl
  rw [hf] at ht
  exact (ht.symm (coordinates d).symm.toMeasurableEquiv).map_eq

theorem density_smooth : ContDiff ℝ (⊤ : ℕ∞) (density d) := by
  unfold density KPArch.volumeDensity KPArch.height
  apply contDiff_prod
  intro i hi
  exact (((EuclideanSpace.proj (finProdFinEquiv (i, (2 : Fin 3)))).contDiff.exp).inv
    (fun p => ne_of_gt (Real.exp_pos _))).pow 2

theorem density_positive (p : EuclideanSpace ℝ (Fin (d * 3))) :
    0 < density d p := by
  unfold density KPArch.volumeDensity KPArch.height
  apply Finset.prod_pos
  intro i hi
  exact pow_pos (inv_pos.mpr (Real.exp_pos _)) 2

theorem metric_volume : Measure.map (coordinates d)
    (volume.withDensity (fun p => ENNReal.ofReal (density d p))) =
      KPArch.hyperbolicVolume (d) := by
  ext s hs
  rw [Measure.map_apply (coordinates d).continuous.measurable hs,
    withDensity_apply _ ((coordinates d).continuous.measurable hs),
    KPArch.hyperbolicVolume, withDensity_apply _ hs]
  have hm := coordinate_volume d
  have hg : Measurable (fun z : KPArch.Space d =>
      s.indicator (fun z => ENNReal.ofReal (KPArch.volumeDensity (d) z)) z) := by
    apply Measurable.indicator _ hs
    apply ENNReal.measurable_ofReal.comp
    unfold KPArch.volumeDensity KPArch.height
    fun_prop
  rw [← lintegral_indicator hs, ← hm, lintegral_map hg (coordinates d).continuous.measurable]
  rw [← lintegral_indicator ((coordinates d).continuous.measurable hs)]
  rfl

end DedekindZetaZeroFree.KPArchRealCoordinates

end
