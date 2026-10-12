module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.FractionalIntegrals.NormalizedKernel

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.RotationCalculus

noncomputable def rawRadialExtension (F : Sphere → ℂ) (x : Ambient) : ℂ :=
  if hx : x ≠ 0 then
    F ⟨‖x‖⁻¹ • x, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  else 0

def RawSphereSmooth (F : Sphere → ℂ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (rawRadialExtension F) {x : Ambient | x ≠ 0}

open MeasureTheory Set Filter Metric
open scoped Topology
universe u
variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
private lemma local_bound {s : Set P} (hs : IsOpen s) {x : P} (hx : x ∈ s)
    {g : P × Ambient → E} (hg : ContinuousOn g (s ×ˢ {y : Ambient | y ≠ 0})) :
    ∃ u ∈ 𝓝 x, u ⊆ s ∧ ∃ C : ℝ, ∀ z ∈ u, ∀ y : Sphere, ‖g (z,y)‖ ≤ C := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  let u := closedBall x (r / 2)
  have hu : u ⊆ s := fun z hz => hsub (by
    apply mem_ball.mpr
    exact lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hk : IsCompact (u ×ˢ Metric.sphere (0 : Ambient) 1) :=
    (isCompact_closedBall (x := x) (r := r / 2)).prod (isCompact_sphere _ _)
  have hgc : ContinuousOn g (u ×ˢ Metric.sphere (0 : Ambient) 1) := hg.mono (by
    rintro ⟨z,y⟩ ⟨hz,hy⟩
    refine ⟨hu hz, ?_⟩
    have hy' := mem_sphere_zero_iff_norm.mp hy
    intro he; change (y : Ambient) = 0 at he; simp [he] at hy')
  obtain ⟨C,hC⟩ := hk.bddAbove_image (hgc.norm)
  refine ⟨u, closedBall_mem_nhds x (by linarith), hu, C, ?_⟩
  intro z hz y
  exact hC (mem_image_of_mem _ ⟨hz,y.property⟩)

private lemma sphere_cont {s : Set P} {g : P × Ambient → E}
    (hg : ContinuousOn g (s ×ˢ {y : Ambient | y ≠ 0})) {x : P} (hx : x ∈ s) :
    Continuous (fun y : Sphere => g (x,y)) := by
  apply hg.comp_continuous (continuous_const.prodMk continuous_subtype_val)
  intro y
  refine ⟨hx, ?_⟩
  have hy := mem_sphere_zero_iff_norm.mp y.property
  intro he; change (y : Ambient) = 0 at he; simp [he] at hy

private lemma sphere_integrable {s : Set P} {g : P × Ambient → E}
    (hg : ContinuousOn g (s ×ˢ {y : Ambient | y ≠ 0})) {x : P} (hx : x ∈ s)
    {k : Sphere → ℝ} (hk : Integrable k sphereArea) :
    Integrable (fun y : Sphere => k y • g (x,y)) sphereArea := by
  have hc := sphere_cont hg hx
  have hb := isCompact_univ.bddAbove_image hc.norm.continuousOn
  obtain ⟨C,hC⟩ := hb
  exact hk.smul_bdd C hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => hC (mem_image_of_mem _ (mem_univ y))))

private lemma integral_continuous {s : Set P} (hs : IsOpen s)
    {g : P × Ambient → E} (hg : ContinuousOn g (s ×ˢ {y : Ambient | y ≠ 0}))
    {k : Sphere → ℝ} (hk : Integrable k sphereArea) :
    ContinuousOn (fun x => ∫ y : Sphere, k y • g (x,y) ∂sphereArea) s := by
  intro x hx
  obtain ⟨u, hu, hus, C, hC⟩ := local_bound hs hx hg
  apply ContinuousAt.continuousWithinAt
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun y => ‖k y‖ * C)
  · filter_upwards [hu] with z hz
    exact (sphere_integrable hg (hus hz) hk).aestronglyMeasurable
  · filter_upwards [hu] with z hz
    exact Eventually.of_forall (fun y => by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hC z hz y) (norm_nonneg _))
  · exact hk.norm.mul_const C
  · apply Eventually.of_forall
    intro y
    change Tendsto (fun z : P => k y • g (z,(y : Ambient))) (𝓝 x) (𝓝 (k y • g (x,y)))
    apply (continuousAt_const.smul _)
    have hn : (y : Ambient) ≠ 0 := by
      have hn := mem_sphere_zero_iff_norm.mp y.property
      intro he; simp [he] at hn
    have hc : ContinuousAt (fun z : P => g (z,(y : Ambient))) x :=
      (hg.continuousAt ((hs.prod isOpen_ne).mem_nhds (show (x,(y : Ambient)) ∈ s ×ˢ {y : Ambient | y ≠ 0} from ⟨hx,hn⟩))).comp (f := fun z : P => (z,(y : Ambient)))
        (show ContinuousAt (fun z : P => (z,(y : Ambient))) x from continuousAt_id.prodMk continuousAt_const)
    exact hc

private lemma integral_hasFDerivAt {s : Set P} (hs : IsOpen s)
    {g : P × Ambient → E} (hg : ContDiffOn ℝ 1 g (s ×ˢ {y : Ambient | y ≠ 0}))
    {k : Sphere → ℝ} (hk : Integrable k sphereArea) {x : P} (hx : x ∈ s) :
    HasFDerivAt (fun x => ∫ y : Sphere, k y • g (x,y) ∂sphereArea)
      (∫ y : Sphere, k y • (fderiv ℝ g (x,y)).comp (ContinuousLinearMap.inl ℝ P Ambient)
        ∂sphereArea) x := by
  let g' : P × Ambient → P →L[ℝ] E := fun q =>
    (fderiv ℝ g q).comp (ContinuousLinearMap.inl ℝ P Ambient)
  have hgc : ContinuousOn g' (s ×ˢ {y : Ambient | y ≠ 0}) := by
    exact (hg.continuousOn_fderiv_of_isOpen (hs.prod isOpen_ne) le_rfl).clm_comp
      continuousOn_const
  obtain ⟨u, hu, hus, C, hC⟩ := local_bound hs hx hgc
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := u)
    (F' := fun z y => k y • g' (z,y)) (bound := fun y => ‖k y‖ * C) hu
  · filter_upwards [hu] with z hz
    exact (sphere_integrable hg.continuousOn (hus hz) hk).aestronglyMeasurable
  · exact sphere_integrable hg.continuousOn hx hk
  · exact (sphere_integrable hgc hx hk).aestronglyMeasurable
  · exact Eventually.of_forall (fun y z hz => by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hC z hz y) (norm_nonneg _))
  · exact hk.norm.mul_const C
  · apply Eventually.of_forall
    intro y z hz
    have hn : (y : Ambient) ≠ 0 := by
      have hn := mem_sphere_zero_iff_norm.mp y.property
      intro he; simp [he] at hn
    have hd := (hg.contDiffAt ((hs.prod isOpen_ne).mem_nhds (show (z,(y : Ambient)) ∈ s ×ˢ {y : Ambient | y ≠ 0} from ⟨hus hz,hn⟩))).differentiableAt
      (by norm_num)
    exact (hd.hasFDerivAt.comp z
      ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (y : Ambient) z))).const_smul (k y)

theorem weighted_sphere_integral_contDiff {s : Set P} (hs : IsOpen s)
    {g : P × Ambient → E} {n : ℕ∞}
    (hg : ContDiffOn ℝ n g (s ×ˢ {y : Ambient | y ≠ 0}))
    {k : Sphere → ℝ} (hk : Integrable k sphereArea) :
    ContDiffOn ℝ n (fun x => ∫ y : Sphere, k y • g (x,y) ∂sphereArea) s := by
  induction n using ENat.nat_induction generalizing E with
  | zero => exact contDiffOn_zero.mpr (integral_continuous hs hg.continuousOn hk)
  | succ n ih =>
    let g' : P × Ambient → P →L[ℝ] E := fun q =>
      (fderiv ℝ g q).comp (ContinuousLinearMap.inl ℝ P Ambient)
    have hg' : ContDiffOn ℝ (n : ℕ∞) g' (s ×ˢ {y : Ambient | y ≠ 0}) := by
      exact ((ContinuousLinearMap.compL ℝ P (P × Ambient) E).contDiff.comp_contDiffOn
        (hg.fderiv_of_isOpen (m := (n : ℕ∞)) (hs.prod isOpen_ne) (by simp))).clm_apply contDiffOn_const
    have hd : ∀ x ∈ s, HasFDerivAt
        (fun x => ∫ y : Sphere, k y • g (x,y) ∂sphereArea)
        (∫ y : Sphere, k y • g' (x,y) ∂sphereArea) x :=
      fun x hx => integral_hasFDerivAt hs (hg.of_le (by exact_mod_cast Nat.succ_pos n)) hk hx
    change ContDiffOn ℝ (((n : ℕ∞) : WithTop ℕ∞) + 1)
      (fun x => ∫ y : Sphere, k y • g (x,y) ∂sphereArea) s
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (E := P →L[ℝ] E) (g := g') hg').congr (fun x hx => (hd x hx).fderiv)
  | top ih =>
    rw [contDiffOn_infty] at hg ⊢
    exact fun n => ih n (hg n)

open MeasureTheory Set Filter Metric
open scoped Topology Pointwise RealInnerProductSpace
private theorem sphere_norm (x : Sphere) : ‖(x : Ambient)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.property
private theorem sphere_ne (x : Sphere) : (x : Ambient) ≠ 0 := by
  intro h; have := sphere_norm x; simp [h] at this
private theorem radial_sphere (F : Sphere → ℂ) (x : Sphere) : rawRadialExtension F x = F x := by
  simp only [rawRadialExtension, dif_pos (sphere_ne x), sphere_norm, inv_one, one_smul]
noncomputable def ortho (e : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  e.toHomeomorph.subtype (fun x => by
    change ‖x - 0‖ = 1 ↔ ‖e x - 0‖ = 1
    simp only [sub_zero, e.norm_map])
private theorem ortho_mp (e : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (ortho e) sphereArea sphereArea := by
  have hraw : MeasurePreserving (ortho e) volume.toSphere volume.toSphere := by
    refine ⟨(ortho e).measurable, Measure.ext fun s hs => ?_⟩
    rw [(ortho e).measurableEmbedding.map_apply,
      Measure.toSphere_apply' _ ((ortho e).measurable hs), Measure.toSphere_apply' _ hs]
    congr 1
    have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' ((ortho e) ⁻¹' s)) =
        e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
      ext z
      constructor
      · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨t, ht, e y, ⟨ortho e y, hy, rfl⟩, by simp⟩
      · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, heq⟩
        refine ⟨t, ht, e.symm y, ⟨(ortho e).symm y, ?_, rfl⟩, ?_⟩
        · simpa using hy
        · have := congrArg e.symm heq
          simpa using this
    rw [hset]
    exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _
  exact hraw.smul_measure _
private theorem integral_ortho (α : ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (F : Sphere → ℂ) (x : Sphere) :
    fractionalIntegral α F (ortho e x) =
      fractionalIntegral α (fun y => F (ortho e y)) x := by
  unfold fractionalIntegral
  rw [← (ortho_mp e).integral_comp (ortho e).measurableEmbedding]
  congr 1
  funext y
  change (fractionalKernel α (ortho e x) (ortho e y) : ℂ) * _ = _
  have hk : fractionalKernel α (ortho e x) (ortho e y) = fractionalKernel α x y := by
    simp only [fractionalKernel]
    change α * Real.rpow ((1 - inner ℝ (e x) (e y)) / 2) (α - 1) = _
    rw [e.inner_map_map]
  rw [hk]
noncomputable def normalize (x : Ambient) : Ambient := ‖x‖⁻¹ • x
private theorem normalize_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) normalize {x : Ambient | x ≠ 0} := by
  intro x hx
  exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id).contDiffWithinAt
private theorem normalize_norm {x : Ambient} (hx : x ≠ 0) : ‖normalize x‖ = 1 := by
  simp only [normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
noncomputable def localOrthogonal (z : Sphere) (x : Ambient) : Ambient ≃ₗᵢ[ℝ] Ambient :=
  (ℝ ∙ ((z : Ambient) - normalize x))ᗮ.reflection
def sectionDomain (z : Sphere) : Set Ambient :=
  {x | x ≠ 0 ∧ (z : Ambient) - normalize x ≠ 0}
private theorem section_smooth (z : Sphere) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : Ambient × Ambient => localOrthogonal z q.1 q.2)
      (sectionDomain z ×ˢ {y : Ambient | y ≠ 0}) := by
  have hn : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : Ambient × Ambient => normalize q.1)
      (sectionDomain z ×ˢ {y : Ambient | y ≠ 0}) :=
    normalize_smooth.comp contDiffOn_fst (fun q hq => hq.1.1)
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : Ambient × Ambient => (z : Ambient) - normalize q.1)
      (sectionDomain z ×ˢ {y : Ambient | y ≠ 0}) := contDiffOn_const.sub hn
  have hnv : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : Ambient × Ambient => ‖(z : Ambient) - normalize q.1‖)
      (sectionDomain z ×ˢ {y : Ambient | y ≠ 0}) := by
    intro q hq
    exact (contDiffAt_norm ℝ hq.1.2).comp_contDiffWithinAt q (hv q hq)
  have hh := hv.inner ℝ contDiffOn_snd
  have hi := (hnv.pow 2).inv (fun q hq => pow_ne_zero 2 (norm_ne_zero_iff.mpr hq.1.2))
  have H := contDiffOn_snd.sub (((hh.mul hi).smul hv).const_smul (2 : ℝ))
  apply H.congr
  intro q hq
  simp only [localOrthogonal, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  change -(2 • ((inner ℝ ((z : Ambient) - normalize q.1) q.2 / ‖(z : Ambient) - normalize q.1‖ ^ 2) • ((z : Ambient) - normalize q.1)) - q.2) =
    q.2 - 2 • ((inner ℝ ((z : Ambient) - normalize q.1) q.2 * (‖(z : Ambient) - normalize q.1‖ ^ 2)⁻¹) • ((z : Ambient) - normalize q.1))
  simp only [div_eq_mul_inv]
  module
private theorem section_open (z : Sphere) : IsOpen (sectionDomain z) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨hx, hv⟩ := hx
  have hn : ContinuousAt normalize x :=
    (normalize_smooth.contDiffAt (isOpen_ne.mem_nhds hx)).continuousAt
  have ht : (fun x : Ambient => (z : Ambient) - normalize x) x ≠ 0 := hv
  have h := (continuousAt_const.sub hn).eventually_ne ht
  filter_upwards [isOpen_ne.mem_nhds hx, h] with x hx hv
  exact ⟨hx, hv⟩
private theorem section_maps (z : Sphere) (x : Ambient) (hx : x ∈ sectionDomain z) :
    localOrthogonal z x z = normalize x := by
  exact Submodule.reflection_sub (by rw [sphere_norm, normalize_norm hx.1])

theorem fractionalIntegral_raw_smooth (α : ℝ) (hα : 0 < α)
    (F : Sphere → ℂ) (hF : RawSphereSmooth F) :
    RawSphereSmooth (fractionalIntegral α F) := by
  intro x hx
  let z : Sphere := ⟨-normalize x, by
    rw [mem_sphere_zero_iff_norm, norm_neg, normalize_norm hx]⟩
  have hxD : x ∈ sectionDomain z := by
    refine ⟨hx, ?_⟩
    change -normalize x - normalize x ≠ 0
    intro h
    have he : normalize x = 0 := by
      have h2 : (2 : ℝ) • normalize x = 0 := by
        have hh : normalize x + normalize x = 0 := by
          have := congrArg Neg.neg h
          simpa using this
        simpa [two_smul ℝ] using hh
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    have hn := normalize_norm hx
    simp [he] at hn
  let g : Ambient × Ambient → ℂ := fun q => rawRadialExtension F (localOrthogonal z q.1 q.2)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (sectionDomain z ×ˢ {y : Ambient | y ≠ 0}) := by
    apply hF.comp (section_smooth z)
    intro q hq
    change localOrthogonal z q.1 q.2 ≠ 0
    intro he
    have := congrArg (localOrthogonal z q.1).symm he
    exact hq.2 (by simpa using this)
  have hi := weighted_sphere_integral_contDiff (section_open z) hg
    ((fractionalKernel_mass α hα).2 z).1
  have heq : ∀ w ∈ sectionDomain z,
      rawRadialExtension (fractionalIntegral α F) w =
        ∫ y : Sphere, fractionalKernel α z y • g (w,y) ∂sphereArea := by
    intro w hw
    have hs : rawRadialExtension (fractionalIntegral α F) w =
        fractionalIntegral α F (ortho (localOrthogonal z w) z) := by
      simp only [rawRadialExtension, dif_pos hw.1]
      congr 1
      apply Subtype.ext
      exact (section_maps z w hw).symm
    rw [hs, integral_ortho]
    unfold fractionalIntegral
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      have hf : g (w,y) = F (ortho (localOrthogonal z w) y) :=
        radial_sphere F (ortho (localOrthogonal z w) y)
      dsimp only
      rw [hf]
      rfl)
  have ht := hi.congr heq
  exact (ht.contDiffAt ((section_open z).mem_nhds hxD)).contDiffWithinAt

end DedekindZetaZeroFree.ComplexFractionalInverse.RotationCalculus
