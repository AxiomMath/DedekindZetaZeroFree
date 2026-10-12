module

public import DedekindZetaZeroFree.Analysis.WeakH2.CoerciveDifferenceTest
public import DedekindZetaZeroFree.Analysis.Sobolev.Restriction.BallNormMonotonicity

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.WeakH2

open MeasureTheory KPContLocalNorm
open KPContLocalEnergy.SobolevEnergyEstimates.Raw

namespace RawRecovery

 theorem bounded_range_extension {T E : Type*} [AddCommGroup T] [Module ℂ T]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : T →ₗ[ℂ] E) (f : T →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t, ‖f t‖ ≤ C * ‖e t‖) :
    ∃ g : E →L[ℂ] ℂ, (∀ t, g (e t) = f t) ∧ ‖g‖ ≤ C := by
  classical
  have hker : e.ker ≤ f.ker := by
    intro t ht
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [LinearMap.mem_ker.mp ht, norm_zero, mul_zero] using hf t
  let fq := e.ker.liftQ f hker
  let fr : e.range →ₗ[ℂ] ℂ := fq.comp e.quotKerEquivRange.symm.toLinearMap
  have hfr : ∀ t, fr (e.rangeRestrict t) = f t := by
    intro t
    change (e.ker.liftQ f hker) (e.quotKerEquivRange.symm ⟨e t, _⟩) = f t
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ y : e.range, ‖fr y‖ ≤ C * ‖y‖ := by
    intro y
    obtain ⟨t, ht⟩ := y.property
    have he : e.rangeRestrict t = y := Subtype.ext ht
    rw [← he, hfr]
    exact hf t
  let fc : e.range →L[ℂ] ℂ := fr.mkContinuous C hb
  obtain ⟨g, hg, hgnorm⟩ := exists_extension_norm_eq e.range fc
  refine ⟨g, ?_, ?_⟩
  · intro t
    exact (hg (e.rangeRestrict t)).trans (hfr t)
  · rw [hgnorm]
    exact LinearMap.mkContinuous_norm_le _ hC hb
open KPContLocalNorm

 def testL2 {n : ℕ} (B : LocalBall n) :
    TestFunction B.toOpens ℂ ⊤ →ₗ[ℂ] BallL2 B where
  toFun φ := (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).toLp φ
  map_add' φ ψ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        ((φ + ψ).continuous.memLp_of_hasCompactSupport (p := 2) (φ + ψ).hasCompactSupport),
      Lp.coeFn_add
        ((φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).toLp φ)
        ((ψ.continuous.memLp_of_hasCompactSupport (p := 2) ψ.hasCompactSupport).toLp ψ),
      MemLp.coeFn_toLp
        (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport),
      MemLp.coeFn_toLp
        (ψ.continuous.memLp_of_hasCompactSupport (p := 2) ψ.hasCompactSupport)] with x h h' hφ hψ
    rw [h, h']
    change φ x + ψ x = _ + _
    rw [hφ, hψ]
  map_smul' c φ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        ((c • φ).continuous.memLp_of_hasCompactSupport (p := 2) (c • φ).hasCompactSupport),
      Lp.coeFn_smul c
        ((φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).toLp φ),
      MemLp.coeFn_toLp
        (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport)] with x h h' hφ
    simp only [RingHom.id_apply]
    rw [h, h']
    change c • φ x = c • _
    rw [hφ]

 theorem testL2_ae {n : ℕ} (B : LocalBall n) (φ : TestFunction B.toOpens ℂ ⊤) :
    testL2 B φ =ᵐ[volume.restrict B.carrier] φ :=
    MemLp.coeFn_toLp (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport)

 def derivativeTest {n : ℕ} (B : LocalBall n) : List (Fin n) →
    TestFunction B.toOpens ℂ ⊤ →L[ℂ] TestFunction B.toOpens ℂ ⊤
  | [] => ContinuousLinearMap.id ℂ _
  | i :: is => (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single i 1)).comp
      (derivativeTest B is)

 theorem derivativeTest_eq {n : ℕ} (B : LocalBall n) (is : List (Fin n))
    (φ : TestFunction B.toOpens ℂ ⊤) (x : Space n) :
    derivativeTest B is φ x = coordinateDerivativeList is (fun y => φ y) x := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    simp only [derivativeTest, ContinuousLinearMap.comp_apply]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
    change fderiv ℝ (fun y => derivativeTest B is φ y) x _ = _
    rw [show (fun y => derivativeTest B is φ y) = coordinateDerivativeList is (fun y => φ y)
      from funext ih]
    rfl

 theorem norm_star_L2 {n : ℕ} (B : LocalBall n) (u : BallL2 B) : ‖star u‖ = ‖u‖ := by
  simp only [Lp.norm_def]
  congr 1
  exact (eLpNorm_congr_ae (Lp.coeFn_star u)).trans (by simp)

 theorem integral_mul_eq_inner {n : ℕ} (B : LocalBall n) (u : BallL2 B)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier, u x * φ x) = inner ℂ (star u) (testL2 B φ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u, testL2_ae B φ] with x hu hφ
  simp [hu, hφ, RCLike.inner_apply, mul_comm]

 theorem weak_derivative_of_test_bound {n k : ℕ} (B : LocalBall n)
    (α : MultiIndex n k) (u : BallL2 B) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ φ : TestFunction B.toOpens ℂ ⊤,
      ‖∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x‖ ≤
        C * ‖testL2 B φ‖) :
    ∃ v : BallL2 B, IsWeakDerivative B α u v ∧ ‖v‖ ≤ C := by
  let f : TestFunction B.toOpens ℂ ⊤ →ₗ[ℂ] ℂ :=
    ((innerSL ℂ (star u)).toLinearMap.comp (testL2 B)).comp
      (derivativeTest B α.directions).toLinearMap
  have hf : ∀ φ, f φ =
      ∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x := by
    intro φ
    change inner ℂ (star u) (testL2 B (derivativeTest B α.directions φ)) = _
    rw [← integral_mul_eq_inner]
    simp only [derivativeTest_eq, coordinateDerivative]
  obtain ⟨g, hg, hgnorm⟩ := bounded_range_extension (testL2 B) f hC
    (by intro φ; rw [hf]; exact hb φ)
  let w : BallL2 B := (InnerProductSpace.toDual ℂ (BallL2 B)).symm g
  let v : BallL2 B := ((-1 : ℂ) ^ α.degree) • star w
  refine ⟨v, ?_, ?_⟩
  · intro φ
    rw [← hf φ, ← hg φ]
    have hw : g (testL2 B φ) = ∫ x in B.carrier, star w x * φ x := by
      rw [integral_mul_eq_inner, star_star]
      exact (InnerProductSpace.toDual_symm_apply).symm
    rw [hw]
    change _ = (-1 : ℂ) ^ α.degree *
      (∫ x in B.carrier, (((-1 : ℂ) ^ α.degree) • star w : BallL2 B) x * φ x)
    have heq : (∫ x in B.carrier, (((-1 : ℂ) ^ α.degree) • star w : BallL2 B) x * φ x) =
        (-1 : ℂ) ^ α.degree * (∫ x in B.carrier, star w x * φ x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul ((-1 : ℂ) ^ α.degree) (star w)] with x hx
      simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [heq, ← mul_assoc, ← mul_pow]
    simp
  · calc
      ‖v‖ = ‖w‖ := by
        rw [norm_smul, norm_star_L2, norm_pow]
        simp
      _ = ‖g‖ := (InnerProductSpace.toDual ℂ (BallL2 B)).symm.norm_map g
      _ ≤ C := hgnorm

theorem testL2_norm {n : ℕ} (B : LocalBall n) (φ : TestFunction B.toOpens ℂ ⊤) :
    ‖testL2 B φ‖ = Real.sqrt (∫ x in B.carrier, ‖φ x‖ ^ 2) := by
  have hs : ‖testL2 B φ‖ ^ 2 = ∫ x in B.carrier, ‖φ x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [testL2_ae B φ] with x hx
    rw [hx]
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem weak_derivative_of_integral_test_bound {n k : ℕ} (B : LocalBall n)
    (α : MultiIndex n k) (u : BallL2 B) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ φ : TestFunction B.toOpens ℂ ⊤,
      ‖∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x‖ ≤
        C * Real.sqrt (∫ x in B.carrier, ‖φ x‖ ^ 2)) :
    ∃ v : BallL2 B, IsWeakDerivative B α u v ∧ ‖v‖ ≤ C := by
  apply weak_derivative_of_test_bound B α u hC
  intro φ
  rw [testL2_norm]
  exact hb φ

end RawRecovery

open Filter Topology

private theorem finiteBall {n : ℕ} (B : LocalBall n) :
    IsFiniteMeasure (volume.restrict B.carrier) :=
  isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall B.center B.radius).measure_lt_top).ne

private theorem zeroExtension_integrable {n : ℕ} {B : LocalBall n} (g : BallL2 B) :
    Integrable (zeroExtension g) volume := by
  letI := finiteBall B
  exact (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
    ((Lp.memLp g).integrable (by norm_num))

private theorem integral_mul_test_bound {n : ℕ} (B : LocalBall n)
    (f : Space n → ℂ) (hf : MemLp f 2 (volume.restrict B.carrier))
    (φ : TestFunction B.toOpens ℂ ⊤) :
    ‖∫ x in B.carrier, f x * φ x‖ ≤
      Real.sqrt (∫ x in B.carrier, ‖f x‖ ^ 2) *
      Real.sqrt (∫ x in B.carrier, ‖φ x‖ ^ 2) := by
  let u : BallL2 B := hf.toLp f
  have hφ := φ.continuous.memLp_of_hasCompactSupport
    (μ := volume.restrict B.carrier) (p := 2) φ.hasCompactSupport
  let v : BallL2 B := hφ.toLp φ
  have heq : (∫ x in B.carrier, f x * φ x) = inner ℂ (star u) v := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star u, MemLp.coeFn_toLp hf,
      MemLp.coeFn_toLp hφ] with x hs hu hv
    change f x * φ x = inner ℂ (star u x) (v x)
    rw [hs]
    change f x * φ x = inner ℂ (star ((hf.toLp f) x)) ((hφ.toLp φ) x)
    simp [hu, hv, RCLike.inner_apply, mul_comm]
  rw [heq]
  have hstar : ‖star u‖ = ‖u‖ := by
    simp only [Lp.norm_def]
    congr 1
    exact (eLpNorm_congr_ae (Lp.coeFn_star u)).trans (by simp)
  have hnorm (w : BallL2 B) (a : Space n → ℂ) (ha : w =ᵐ[volume.restrict B.carrier] a) :
      ‖w‖ = Real.sqrt (∫ x in B.carrier, ‖a x‖ ^ 2) := by
    have hs : ‖w‖ ^ 2 = ∫ x in B.carrier, ‖a x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
      apply integral_congr_ae
      filter_upwards [ha] with x hx
      rw [hx]
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  have hu := hnorm u f (MemLp.coeFn_toLp hf)
  have hv := hnorm v φ (MemLp.coeFn_toLp hφ)
  simpa only [hstar, hu, hv] using (norm_inner_le_norm (star u) v)

private theorem translated_pairing_hasDeriv {n : ℕ} (B : LocalBall n)
    (f : Space n → ℂ) (hf : Integrable f volume)
    (φ : TestFunction B.toOpens ℂ ⊤) (e : Space n) :
    HasDerivAt (fun t : ℝ => ∫ x, f x * φ (x - t • e))
      (∫ x, -(f x * fderiv ℝ (fun y => φ y) x e)) 0 := by
  obtain ⟨C, hC⟩ :=
    (φ.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (φ.hasCompactSupport.fderiv ℝ)
  have hm (t : ℝ) : AEStronglyMeasurable (fun x => φ (x - t • e)) volume :=
    (φ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hd (x : Space n) (t : ℝ) :
      HasDerivAt (fun t : ℝ => f x * φ (x - t • e))
        (-(f x * fderiv ℝ (fun y => φ y) (x - t • e) e)) t := by
    have hp : HasDerivAt (fun t : ℝ => x - t • e) (-e) t := by
      simpa using (hasDerivAt_id t).smul_const e |>.const_sub x
    have hφd : HasFDerivAt (fun y => φ y) (fderiv ℝ (fun y => φ y) (x - t • e))
        (x - t • e) := (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    convert (hφd.comp_hasDerivAt t hp).const_mul (f x) using 1 <;> simp
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun x => -(f x * fderiv ℝ (fun y => φ y) (x - t • e) e)) volume := by
    exact (hf.aestronglyMeasurable.mul
      (((φ.contDiff.continuous_fderiv (by simp)).comp
        (continuous_id.sub continuous_const)).clm_apply continuous_const
        |>.aestronglyMeasurable)).neg
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hint (t : ℝ) : Integrable (fun x => f x * φ (x - t • e)) volume :=
    hf.mul_bdd (hm t) (Eventually.of_forall fun x => hCφ _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t : ℝ => fun x => f x * φ (x - t • e))
    (F' := fun t : ℝ => fun x => -(f x * fderiv ℝ (fun y => φ y) (x - t • e) e))
    (s := Set.univ) (bound := fun x => ‖f x‖ * (C * ‖e‖))
    (by simp) (Eventually.of_forall fun t => hf.aestronglyMeasurable.mul (hm t))
    (hint 0) (hmeas 0)
    (Eventually.of_forall fun x t _ => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))) (norm_nonneg _))
    (hf.norm.mul_const _) (Eventually.of_forall fun x t _ => hd x t)
  simpa using h.2

private theorem global_mul_test {n : ℕ} (B : LocalBall n) (f : Space n → ℂ)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x, f x * φ x) = ∫ x in B.carrier, f x * φ x := by
  rw [← integral_indicator (show MeasurableSet B.carrier from Metric.isOpen_ball.measurableSet)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ B.carrier
    · simp [hx]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (φ.tsupport_subset h))
      simp [hx, hz]

private theorem shifted_pairing_identity {n : ℕ} (B : LocalBall n)
    (f : Space n → ℂ) (hf : Integrable f volume)
    (φ : TestFunction B.toOpens ℂ ⊤) (k : Fin n) (t : ℝ) :
    (∫ x in B.carrier, differenceQuotient k t f x * φ x) =
      (t : ℂ)⁻¹ * ((∫ x, f x * φ (x - t • EuclideanSpace.single k 1)) -
        (∫ x, f x * φ x)) := by
  rw [← global_mul_test]
  have hc := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨C, hC⟩ := hc
  have h1 : Integrable (fun x => f x * φ x) volume :=
    hf.mul_bdd φ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have h2 : Integrable (fun x => f (x + t • EuclideanSpace.single k 1) * φ x) volume := by
    have hf' : Integrable (fun x => f (x + t • EuclideanSpace.single k 1)) volume :=
      ((measurePreserving_add_right volume _).integrable_comp hf.aestronglyMeasurable).mpr hf
    exact hf'.mul_bdd φ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have heq : (∫ x, f (x + t • EuclideanSpace.single k 1) * φ x) =
      ∫ x, f x * φ (x - t • EuclideanSpace.single k 1) := by
    have h := integral_add_right_eq_self
      (fun x => f x * φ (x - t • EuclideanSpace.single k 1))
      (μ := volume) (t • EuclideanSpace.single k 1)
    convert h using 1
    congr 1
    ext x
    congr 2
    abel
  calc
    _ = (t : ℂ)⁻¹ * (∫ x, f (x + t • EuclideanSpace.single k 1) * φ x - f x * φ x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp [differenceQuotient]; ring
    _ = _ := by rw [integral_sub h2 h1, heq]

theorem difference_bound_to_test_pairing {n : ℕ} (inner outer : LocalBall n)
    (hcenter : inner.center = outer.center) (hgap : inner.radius < outer.radius)
    (g : BallL2 outer) (k : Fin n) (δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A)
    (hbound : ∀ t : ℝ, t ≠ 0 → |t| < δ →
      MemLp (differenceQuotient k t (zeroExtension g)) 2 (volume.restrict inner.carrier) ∧
      (∫ x in inner.carrier, ‖differenceQuotient k t (zeroExtension g) x‖ ^ 2) ≤ A ^ 2) :
    ∀ φ : TestFunction inner.toOpens ℂ ⊤,
      ‖∫ x in inner.carrier, g x * coordinateDerivativeList [k] (fun y => φ y) x‖ ≤
        A * Real.sqrt (∫ x in inner.carrier, ‖φ x‖ ^ 2) := by
  intro φ
  let e : Space n := EuclideanSpace.single k 1
  let f := zeroExtension g
  have hf : Integrable f volume := zeroExtension_integrable g
  have hsub : inner.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hcenter]
    exact Metric.ball_subset_ball hgap.le
  have htarget : (∫ x, f x * fderiv ℝ (fun y => φ y) x e) =
      ∫ x in inner.carrier, g x * coordinateDerivativeList [k] (fun y => φ y) x := by
    let ψ : TestFunction inner.toOpens ℂ ⊤ := TestFunction.lineDerivCLM ℂ e φ
    have hψ : ∀ x, ψ x = fderiv ℝ (fun y => φ y) x e := by
      intro x
      simp only [ψ, TestFunction.lineDerivCLM_eq_fderivCLM,
        TestFunction.fderivCLM_apply_of_le φ (show (⊤ : ℕ∞) + 1 ≤ ⊤ by simp)]
    rw [show (fun x => f x * fderiv ℝ (fun y => φ y) x e) =
        (fun x => f x * ψ x) from funext fun x => by rw [hψ]]
    rw [global_mul_test inner f ψ]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet inner.carrier from
      Metric.isOpen_ball.measurableSet)] with x hx
    simp [f, zeroExtension, hsub hx, hψ, coordinateDerivativeList, e]
  have hlim : Tendsto
      (fun t : ℝ => ∫ x in inner.carrier, differenceQuotient k t f x * φ x)
      (𝓝[≠] 0)
      (𝓝 (-(∫ x in inner.carrier,
        g x * coordinateDerivativeList [k] (fun y => φ y) x))) := by
    have h := (translated_pairing_hasDeriv inner f hf φ e).tendsto_slope_zero
    rw [integral_neg, htarget] at h
    convert h using 1
    ext t
    rw [shifted_pairing_identity inner f hf φ k t]
    simp [Complex.real_smul, e]
  apply le_of_tendsto (by simpa only [norm_neg] using hlim.norm)
  have hevent : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 ∧ |t| < δ := by
    filter_upwards [self_mem_nhdsWithin,
      (Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun ht => by simpa using ht⟩ :
        ∀ᶠ t : ℝ in 𝓝 0, |t| < δ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    exact ⟨ht, htδ⟩
  filter_upwards [hevent] with t ht
  obtain ⟨hm, hb⟩ := hbound t ht.1 ht.2
  exact (integral_mul_test_bound inner _ hm φ).trans
    (mul_le_mul_of_nonneg_right ((Real.sqrt_le_iff).mpr ⟨hA, hb⟩)
      (Real.sqrt_nonneg _))

open KPContLocalEnergy.SobolevEnergyEstimates

private theorem dirs_length {n k : ℕ} (α : MultiIndex n k) :
    α.directions.length = α.degree := by
  simp [MultiIndex.directions, MultiIndex.degree, List.length_flatMap,
    ← List.sum_toFinset _ (List.nodup_finRange n), List.toFinset_finRange]

private theorem dirs_count {n k : ℕ} (α : MultiIndex n k) (i : Fin n) :
    α.directions.count i = (α.val i).val := by
  classical
  rw [MultiIndex.directions, List.count_flatMap,
    ← List.sum_toFinset _ (List.nodup_finRange n), List.toFinset_finRange]
  simp [Function.comp_def, List.count_replicate]

private theorem dirs_injective {n k : ℕ} :
    Function.Injective (MultiIndex.directions (n := n) (k := k)) := by
  intro α β h
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [← dirs_count, ← dirs_count, h]

 def low {n : ℕ} (α : MultiIndex n 2) (h : α.degree ≤ 1) : MultiIndex n 1 :=
  ⟨fun i => ⟨(α.val i).val, by
      have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (α.val j).val) (Finset.mem_univ i)
      change (α.val i).val < 2
      change (α.val i).val ≤ α.degree at hi
      omega⟩, h⟩

private theorem low_inj {n : ℕ} : Function.Injective
    (fun α : {α : MultiIndex n 2 // α.degree ≤ 1} => low α.val α.property) := by
  intro α β h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun γ : MultiIndex n 1 => (γ.val i).val) h

 theorem pair_dirs {n : ℕ} (α : MultiIndex n 2) (h : ¬ α.degree ≤ 1) :
    ∃ j k : Fin n, α.directions = [j,k] := by
  have hd := α.property
  have hl : α.directions.length = 2 := by rw [dirs_length]; change α.degree ≤ 2 at hd; omega
  obtain ⟨j, l, he⟩ := List.exists_cons_of_length_pos (show 0 < α.directions.length by omega)
  have hl' : l.length = 1 := by rw [he] at hl; simpa using hl
  obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hl'
  exact ⟨j, k, by rw [he, hk]⟩

 def pair {n : ℕ} (α : {α : MultiIndex n 2 // ¬ α.degree ≤ 1}) : Fin n × Fin n :=
  ((pair_dirs α.val α.property).choose,
    (pair_dirs α.val α.property).choose_spec.choose)

private theorem pair_spec {n : ℕ} (α : {α : MultiIndex n 2 // ¬ α.degree ≤ 1}) :
    α.val.directions = [(pair α).1, (pair α).2] :=
  (pair_dirs α.val α.property).choose_spec.choose_spec

private theorem pair_inj {n : ℕ} : Function.Injective (@pair n) := by
  intro α β h
  apply Subtype.ext
  apply dirs_injective
  rw [pair_spec, pair_spec, h]

private theorem high_card {n : ℕ} :
    Fintype.card {α : MultiIndex n 2 // ¬ α.degree ≤ 1} ≤ n ^ 2 := by
  classical
  have h := Fintype.card_le_of_injective (@pair n) pair_inj
  simpa [pow_two] using h
private theorem recover_high {n : ℕ} (B : LocalBall n) (u : IntegerSobolev B 1)
    {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ (j k : Fin n) (φ : TestFunction B.toOpens ℂ ⊤),
      ‖∫ x in B.carrier, gradient u j x * coordinateDerivativeList [k] (fun y => φ y) x‖ ≤
        A * Real.sqrt (∫ x in B.carrier, ‖φ x‖ ^ 2))
    (α : MultiIndex n 2) (ha : ¬ α.degree ≤ 1) :
    ∃ v : BallL2 B, IsWeakDerivative B α (value u) v ∧ ‖v‖ ≤ A := by
  obtain ⟨j, k, hd⟩ := pair_dirs α ha
  apply RawRecovery.weak_derivative_of_integral_test_bound B α (value u) hA
  intro φ
  let ψ := RawRecovery.derivativeTest B [k] φ
  have hψ : ∀ x, ψ x = coordinateDerivativeList [k] (fun y => φ y) x :=
    RawRecovery.derivativeTest_eq B [k] φ
  have hu := u.weak_derivatives (firstIndex j) ψ
  have hdeg : (firstIndex j).degree = 1 := by
    simp only [MultiIndex.degree, firstIndex, apply_ite Fin.val, Fin.val_one, Fin.val_zero]
    simp
  have hl : (∫ x in B.carrier, value u x * coordinateDerivative α (fun y => φ y) x) =
      -(∫ x in B.carrier, gradient u j x * coordinateDerivativeList [k] (fun y => φ y) x) := by
    change (∫ x in B.carrier, value u x * coordinateDerivative α (fun y => φ y) x) = _
    rw [coordinateDerivative, hd]
    have he : (fun y => ψ y) = coordinateDerivativeList [k] (fun y => φ y) := funext hψ
    simpa only [coordinateDerivative, firstIndex_directions, hdeg, pow_one,
      neg_one_mul, he, coordinateDerivativeList, KPContLocalEnergy.SobolevEnergyEstimates.Raw.value,
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient, zeroIndex] using hu
  rw [hl, norm_neg]
  exact hb j k φ

private theorem restrict_normSq {n : ℕ} (inner outer : LocalBall n)
    (hsub : inner.carrier ⊆ outer.carrier) (u : IntegerSobolev outer 1) :
    ∃ w : IntegerSobolev inner 1,
      (∀ α, w.derivatives α =ᵐ[volume.restrict inner.carrier] u.derivatives α) ∧
      w.normSq ≤ u.normSq := by
  let w := KPContLocalEnergy.restrictSobolev hsub u
  refine ⟨w, fun α => KPContLocalEnergy.restrictBallL2_ae hsub _, ?_⟩
  apply Finset.sum_le_sum
  intro α _
  exact pow_le_pow_left₀ (norm_nonneg _) (KPContLocalEnergy.norm_restrictBallL2_le hsub _) 2

theorem assemble_second_weak_derivatives {n : ℕ} (inner outer : LocalBall n)
    (hsub : inner.carrier ⊆ outer.carrier) (u : IntegerSobolev outer 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hpair : ∀ (j k : Fin n) (φ : TestFunction inner.toOpens ℂ ⊤),
      ‖∫ x in inner.carrier,
        gradient u j x * coordinateDerivativeList [k] (fun y => φ y) x‖ ≤
          A * Real.sqrt (∫ x in inner.carrier, ‖φ x‖ ^ 2)) :
    ∃ v : IntegerSobolev inner 2,
      (∀ᵐ x ∂volume.restrict inner.carrier, value v x = value u x) ∧
      v.normSq ≤ u.normSq + (n : ℝ) ^ 2 * A ^ 2 := by
  classical
  obtain ⟨w, hw, hwn⟩ := restrict_normSq inner outer hsub u
  have hb : ∀ (j k : Fin n) (φ : TestFunction inner.toOpens ℂ ⊤),
      ‖∫ x in inner.carrier, gradient w j x * coordinateDerivativeList [k] (fun y => φ y) x‖ ≤
        A * Real.sqrt (∫ x in inner.carrier, ‖φ x‖ ^ 2) := by
    intro j k φ
    have he : (∫ x in inner.carrier, gradient w j x * coordinateDerivativeList [k] (fun y => φ y) x) =
        ∫ x in inner.carrier, gradient u j x * coordinateDerivativeList [k] (fun y => φ y) x := by
      apply integral_congr_ae
      filter_upwards [hw (firstIndex j)] with x hx
      change w.derivatives (firstIndex j) x * _ = u.derivatives (firstIndex j) x * _
      rw [hx]
    rw [he]
    exact hpair j k φ
  have hr := fun α ha => recover_high inner w hA hb α ha
  let d : MultiIndex n 2 → BallL2 inner := fun α =>
    if h : α.degree ≤ 1 then w.derivatives (low α h) else (hr α h).choose
  have dz : d (zeroIndex n 2) = value w := by
    dsimp [d]
    rw [dif_pos (by simp [zeroIndex, MultiIndex.degree])]
    rfl
  have dw : ∀ α, IsWeakDerivative inner α (value w) (d α) := by
    intro α
    dsimp [d]
    split_ifs with h
    · have he := w.weak_derivatives (low α h)
      exact he
    · exact (hr α h).choose_spec.1
  let v : IntegerSobolev inner 2 := ⟨d, by intro α; rw [show
      (⟨fun _ => 0, by simp⟩ : MultiIndex n 2) = zeroIndex n 2 from rfl, dz]; exact dw α⟩
  refine ⟨v, ?_, ?_⟩
  · change d (zeroIndex n 2) =ᵐ[volume.restrict inner.carrier] value u
    rw [dz]
    exact hw (zeroIndex n 1)
  · have hl : (∑ α : {α : MultiIndex n 2 // α.degree ≤ 1}, ‖d α.val‖ ^ 2) ≤ w.normSq := by
      apply Finset.sum_le_sum_of_injOn (fun α => low α.val α.property)
      · exact low_inj.injOn
      · exact Finset.subset_univ _
      · intro α _
        simp only [d, dif_pos α.property]
        exact le_rfl
      · intro α _ _
        exact sq_nonneg _
    have hh : (∑ α : {α : MultiIndex n 2 // ¬ α.degree ≤ 1}, ‖d α.val‖ ^ 2) ≤
        (n : ℝ) ^ 2 * A ^ 2 := by
      calc
        _ ≤ ∑ _α : {α : MultiIndex n 2 // ¬ α.degree ≤ 1}, A ^ 2 := by
          apply Finset.sum_le_sum
          intro α _
          simp only [d, dif_neg α.property]
          exact pow_le_pow_left₀ (norm_nonneg _) (hr α.val α.property).choose_spec.2 2
        _ = (Fintype.card {α : MultiIndex n 2 // ¬ α.degree ≤ 1} : ℝ) * A ^ 2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast high_card (n := n)) (sq_nonneg _)
    change (∑ α, ‖d α‖ ^ 2) ≤ _
    rw [← Fintype.sum_subtype_add_sum_subtype (fun α : MultiIndex n 2 => α.degree ≤ 1)]
    exact add_le_add (hl.trans hwn) hh

end DedekindZetaZeroFree.WeakH2

end
