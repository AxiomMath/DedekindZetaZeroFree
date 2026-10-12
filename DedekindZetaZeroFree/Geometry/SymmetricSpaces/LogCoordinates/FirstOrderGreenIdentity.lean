module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.ScalarLaplacianGraph

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Filter Topology
open _root_.DedekindZetaZeroFree.HyperbolicChart renaming first_order_green → DedekindZetaZeroFree.HyperbolicChart.first_order_green
namespace DedekindZetaZeroFree.KPContinuation.RawFundamentalDomain.Green
open KPCuspCutoffGraphApproximation
variable (F : Type) [Field F] [NumberField F]

 lemma from_to (q : Coordinates F) : fromArch F (toArch F q) = q := by
  ext ⟨i,k⟩
  fin_cases k <;> rfl

 lemma to_from (x : Arch F) : toArch F (fromArch F x) = x := by
  ext i : 1
  apply Prod.ext
  · apply Complex.ext <;> rfl
  · rfl

 def coordEquiv : Coordinates F ≃L[ℝ] Arch F :=
  (show Coordinates F ≃ₗ[ℝ] Arch F from
    { toFun := toArch F
      invFun := fromArch F
      left_inv := from_to F
      right_inv := to_from F
      map_add' := by intros; ext i : 1; apply Prod.ext; apply Complex.ext <;> rfl; rfl
      map_smul' := by
        intros
        ext i : 1
        apply Prod.ext
        · apply Complex.ext <;> simp [toArch, PiLp.smul_apply]
        · rfl
    }).toContinuousLinearEquiv

private lemma phi_preserving :
    MeasurePreserving (fun p : Fin 3 → ℝ =>
      (Complex.measurableEquivPi.symm (fun j : Fin 2 => p (Fin.castSucc j)), p 2))
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure (ℂ × ℝ)) := by
  have hp := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have hs := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin 2 → ℝ)))
  have hc := (Complex.volume_preserving_equiv_pi).symm
  have hid : MeasurePreserving (id : ℝ → ℝ) (volume : Measure ℝ) (volume : Measure ℝ) :=
    MeasurePreserving.id _
  have hcomp := (hc.prod hid).comp (hs.comp hp)
  convert hcomp using 1
  funext p
  simp only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply, Prod.map_apply,
    Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap, id_eq, Fin.removeNth_apply,
    Fin.succAbove_last, Fin.castSucc_zero, Fin.castSucc_one, Fin.last]
  congr 1 <;> rfl

private lemma curry_preserving (d : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin d) (Fin 3) ℝ)
      (volume : Measure (Fin d × Fin 3 → ℝ)) (volume : Measure (Fin d → Fin 3 → ℝ)) := by
  have key : (volume : Measure (Fin d × Fin 3 → ℝ)) =
      Measure.map (MeasurableEquiv.curry (Fin d) (Fin 3) ℝ).symm
        (volume : Measure (Fin d → Fin 3 → ℝ)) := by
    rw [show (volume : Measure (Fin d × Fin 3 → ℝ)) =
        Measure.pi (fun _ : Fin d × Fin 3 => (volume : Measure ℝ)) from rfl,
      show (volume : Measure (Fin d → Fin 3 → ℝ)) =
        Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) from rfl]
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Measure.map_apply (MeasurableEquiv.curry _ _ _).symm.measurable
      (MeasurableSet.pi (Set.to_countable _) fun i _ => hs i)]
    have hpre : (MeasurableEquiv.curry (Fin d) (Fin 3) ℝ).symm ⁻¹' (Set.pi Set.univ s) =
        Set.pi Set.univ (fun i : Fin d => Set.pi Set.univ (fun j : Fin 3 => s (i,j))) := by
      ext g
      simp [MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair, Set.mem_univ_pi]
    rw [hpre]
    simp only [Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry _ _ _).measurable, ?_⟩
  rw [key, MeasurableEquiv.map_map_symm]

private lemma coord_volume_preserving :
    MeasurePreserving (toArch F) (volume : Measure (Coordinates F)) (volume : Measure (Arch F)) := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin (KPCuspLogShape.dimension F) × Fin 3)
  have h2 := curry_preserving (KPCuspLogShape.dimension F)
  have h3 := volume_preserving_pi (fun _ : Fin (KPCuspLogShape.dimension F) => phi_preserving)
  convert h3.comp (h2.comp h1) using 1
  funext p i
  simp [toArch, Function.comp_def, Complex.measurableEquivPi, mul_comm]
  apply Complex.ext <;> simp

private lemma coord_density (p : Coordinates F) :
    KPArch.volumeDensity _ (toArch F p) = HyperbolicChart.density _ p := by
  have he (u : ℝ) : (Real.exp u)⁻¹ ^ 2 = Real.exp (-2 * u) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  simp only [KPArch.volumeDensity, KPArch.height, HyperbolicChart.density, toArch, he]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

private lemma coord_measure_preserving :
    MeasurePreserving (toArch F) (HyperbolicChart.measure _) (KPArch.hyperbolicVolume _) := by
  have hf := coord_volume_preserving F
  refine ⟨hf.measurable, ?_⟩
  have hρ : Measurable (fun z : Arch F => ENNReal.ofReal (KPArch.volumeDensity _ z)) := by
    unfold KPArch.volumeDensity KPArch.height; fun_prop
  have hmap : Measure.map (toArch F)
      ((volume : Measure (Coordinates F)).withDensity
        ((fun z : Arch F => ENNReal.ofReal (KPArch.volumeDensity _ z)) ∘ toArch F)) =
      (volume : Measure (Arch F)).withDensity
        (fun z => ENNReal.ofReal (KPArch.volumeDensity _ z)) := by
    ext s hs
    rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
      withDensity_apply _ hs]
    rw [← hf.map_eq]
    rw [← lintegral_indicator (hf.measurable hs), ← lintegral_indicator hs,
      lintegral_map (hρ.indicator hs) hf.measurable]
    congr 1
  simpa only [Function.comp_def, coord_density, HyperbolicChart.measure,
    KPArch.hyperbolicVolume] using hmap

private lemma cd_congr {d : ℕ} {W Z : HyperbolicChart.Space d → HyperbolicChart.Cotangent d}
    {q : HyperbolicChart.Space d} (h : W =ᶠ[𝓝 q] Z) :
    HyperbolicChart.codifferential d W q = HyperbolicChart.codifferential d Z q := by
  have hval := h.eq_of_nhds
  unfold HyperbolicChart.codifferential HyperbolicChart.coordinateDerivative
  congr 1
  funext i
  have hder (k : Fin 3) :
      fderiv ℝ (fun p => W p i k) q = fderiv ℝ (fun p => Z p i k) q :=
    (h.fun_comp (fun a => a i k)).fderiv_eq
  rw [hval, hder 0, hder 1, hder 2]

private lemma cd_off {d : ℕ} (W : HyperbolicChart.Space d → HyperbolicChart.Cotangent d)
    {q : HyperbolicChart.Space d} (hq : q ∉ tsupport W) :
    HyperbolicChart.codifferential d W q = 0 := by
  have h : W =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
  rw [cd_congr h]
  simp [HyperbolicChart.codifferential, HyperbolicChart.coordinateDerivative]

private lemma localized_green {d : ℕ} (f : HyperbolicChart.Space d → ℂ)
    (W : HyperbolicChart.Space d → HyperbolicChart.Cotangent d)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hc : HasCompactSupport W) :
    (∫ q, HyperbolicChart.pairing d (HyperbolicChart.differential d f q) (W q)
      ∂HyperbolicChart.measure d) =
    ∫ q, star (f q) * HyperbolicChart.codifferential d W q ∂HyperbolicChart.measure d := by
  obtain ⟨r, hr⟩ := hc.isBounded.subset_ball (0 : HyperbolicChart.Space d)
  let b : ContDiffBump (0 : HyperbolicChart.Space d) :=
    { rIn := max r 1
      rOut := max r 1 + 1
      rIn_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      rIn_lt_rOut := lt_add_one _ }
  let g : HyperbolicChart.Space d → ℂ := fun q => (b q : ℂ) * f q
  have hb (q) (hq : q ∈ tsupport W) : b =ᶠ[𝓝 q] 1 := by
    apply b.eventuallyEq_one_of_mem_ball
    exact Metric.ball_subset_ball (le_max_left _ _) (hr hq)
  have hg (q) (hq : q ∈ tsupport W) : g =ᶠ[𝓝 q] f := by
    filter_upwards [hb q hq] with p hp
    simp [g, hp]
  have hleft (q) : HyperbolicChart.pairing d (HyperbolicChart.differential d g q) (W q) =
      HyperbolicChart.pairing d (HyperbolicChart.differential d f q) (W q) := by
    by_cases hq : q ∈ tsupport W
    · have hd := (hg q hq).fderiv_eq (𝕜 := ℝ)
      unfold HyperbolicChart.differential HyperbolicChart.coordinateDerivative
      rw [hd]
    · rw [image_eq_zero_of_notMem_tsupport hq]
      simp [HyperbolicChart.pairing]
  have hright (q) : star (g q) * HyperbolicChart.codifferential d W q =
      star (f q) * HyperbolicChart.codifferential d W q := by
    by_cases hq : q ∈ tsupport W
    · rw [(hg q hq).eq_of_nhds]
    · rw [cd_off W hq]; simp
  have hgc : HasCompactSupport g :=
    (b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).mul hf
  have he := (DedekindZetaZeroFree.HyperbolicChart.first_order_green d g W hgs hgc hW hc).2.2
  simpa only [hleft, hright] using he

theorem standard_log_chart_first_order_green
    (S : Set (Arch F)) (hS : IsOpen S)
    (s : Arch F → ℂ)
    (V : Arch F → HyperbolicChart.Cotangent (KPCuspLogShape.dimension F))
    (hs : ContDiff ℝ (⊤ : ℕ∞) s)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hext : ContDiff ℝ (⊤ : ℕ∞) (S.indicator V))
    (hcompact : HasCompactSupport (S.indicator V))
    (hsupport : tsupport (S.indicator V) ⊆ S) :
    (∫ x in S, HyperbolicChart.pairing (KPCuspLogShape.dimension F)
      (HyperbolicChart.differential _ (s ∘ toArch F) (fromArch F x)) (V x)
      ∂KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) =
    ∫ x in S, star (s x) * HyperbolicChart.codifferential _
      (V ∘ toArch F) (fromArch F x)
      ∂KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) := by
  let T := toArch F ⁻¹' S
  let W := S.indicator V ∘ toArch F
  have hT : IsOpen T := hS.preimage (coordEquiv F).continuous
  have hWs : tsupport W ⊆ T := by
    change tsupport (S.indicator V ∘ (coordEquiv F).toHomeomorph) ⊆ T
    rw [tsupport_comp_eq_preimage]
    exact Set.preimage_mono hsupport
  have hWc : HasCompactSupport W :=
    hcompact.comp_homeomorph (coordEquiv F).toHomeomorph
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := hext.comp (coordEquiv F).contDiff
  have hf : ContDiff ℝ (⊤ : ℕ∞) (s ∘ toArch F) := hs.comp (coordEquiv F).contDiff
  have hloc (q) (hq : q ∈ T) : (V ∘ toArch F) =ᶠ[𝓝 q] W := by
    filter_upwards [hT.mem_nhds hq] with p hp
    exact (Set.indicator_of_mem (show toArch F p ∈ S from hp) V).symm
  let L : Arch F → ℂ := fun x => HyperbolicChart.pairing _
    (HyperbolicChart.differential _ (s ∘ toArch F) (fromArch F x)) (S.indicator V x)
  let R : Arch F → ℂ := fun x => star (s x) * HyperbolicChart.codifferential _ W (fromArch F x)
  have hLeq : (∫ x in S, HyperbolicChart.pairing _
      (HyperbolicChart.differential _ (s ∘ toArch F) (fromArch F x)) (V x)
      ∂KPArch.hyperbolicVolume _) = ∫ x, L x ∂KPArch.hyperbolicVolume _ := by
    calc
      _ = ∫ x in S, L x ∂KPArch.hyperbolicVolume _ := by
        apply setIntegral_congr_fun hS.measurableSet
        intro x hx
        simp only [L, Set.indicator_of_mem hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
        intro x hx
        simp [L, Set.indicator_of_notMem hx, HyperbolicChart.pairing])
  have hReq : (∫ x in S, star (s x) * HyperbolicChart.codifferential _
      (V ∘ toArch F) (fromArch F x) ∂KPArch.hyperbolicVolume _) =
      ∫ x, R x ∂KPArch.hyperbolicVolume _ := by
    calc
      _ = ∫ x in S, R x ∂KPArch.hyperbolicVolume _ := by
        apply setIntegral_congr_fun hS.measurableSet
        intro x hx
        have ht : fromArch F x ∈ T := by simpa [T, to_from] using hx
        exact congrArg (fun z => star (s x) * z) (cd_congr (hloc _ ht))
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
        intro x hx
        have ht : fromArch F x ∉ tsupport W := by
          intro hm
          have := hWs hm
          exact hx (by simpa [T, to_from] using this)
        simp only [R, cd_off W ht, mul_zero])
  rw [hLeq, hReq]
  have hmp := coord_measure_preserving F
  have hemb : MeasurableEmbedding (toArch F) := (coordEquiv F).toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hemb L, ← hmp.integral_comp hemb R]
  simpa only [L, R, W, from_to, Function.comp_apply] using
    localized_green (s ∘ toArch F) W hf hW hWc

end DedekindZetaZeroFree.KPContinuation.RawFundamentalDomain.Green

end
