module

public import DedekindZetaZeroFree.Analysis.Sobolev.Restriction.IntegerOrderWeakDerivatives
public import DedekindZetaZeroFree.Analysis.Sobolev.LocalEmbeddingAndSmoothRepresentatives

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.WeakH2

open MeasureTheory KPContLocalNorm
open KPContLocalEnergy.SobolevEnergyEstimates.Raw

def zeroExtension {n : ℕ} {B : LocalBall n} (f : BallL2 B) : Space n → ℂ :=
  B.carrier.indicator (fun x => f x)

def differenceQuotient {n : ℕ} (k : Fin n) (t : ℝ) (f : Space n → ℂ) :
    Space n → ℂ :=
  fun x => (t : ℂ)⁻¹ * (f (x + t • EuclideanSpace.single k 1) - f x)

theorem zeroExtension_memLp {n : ℕ} {B : LocalBall n} (f : BallL2 B) :
    MemLp (zeroExtension f) 2 volume := by
  exact (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet).2 (Lp.memLp f)

theorem zeroExtension_norm {n : ℕ} {B : LocalBall n} (f : BallL2 B) :
    ‖(zeroExtension_memLp f).toLp (zeroExtension f)‖ = ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, zeroExtension,
    eLpNorm_indicator_eq_eLpNorm_restrict (show MeasurableSet B.carrier from
      Metric.isOpen_ball.measurableSet).nullMeasurableSet]

theorem differenceQuotient_memLp {n : ℕ} {B : LocalBall n}
    (f : BallL2 B) (k : Fin n) (t : ℝ) :
    MemLp (differenceQuotient k t (zeroExtension f)) 2 volume := by
  have hshift := (zeroExtension_memLp f).comp_measurePreserving
    (measurePreserving_add_right volume (t • EuclideanSpace.single k 1))
  exact (hshift.sub (zeroExtension_memLp f)).const_mul (t : ℂ)⁻¹

def differenceClass {n : ℕ} (inner : LocalBall n) {outer : LocalBall n}
    (f : BallL2 outer) (k : Fin n) (t : ℝ) : BallL2 inner :=
  ((differenceQuotient_memLp f k t).mono_measure Measure.restrict_le_self).toLp
    (differenceQuotient k t (zeroExtension f))

theorem differenceClass_ae {n : ℕ} (inner : LocalBall n) {outer : LocalBall n}
    (f : BallL2 outer) (k : Fin n) (t : ℝ) :
    ∀ᵐ x ∂volume.restrict inner.carrier,
      differenceClass inner f k t x = differenceQuotient k t (zeroExtension f) x :=
  MemLp.coeFn_toLp _

theorem safe_segment_mem {n : ℕ} (inner outer : LocalBall n)
    (hcenter : inner.center = outer.center) (k : Fin n) (t : ℝ)
    (hsafe : |t| < outer.radius - inner.radius) {x : Space n}
    (hx : x ∈ inner.carrier) {s : ℝ} (hs : |s| ≤ |t|) :
    x + s • EuclideanSpace.single k 1 ∈ outer.carrier := by
  have hnorm : ‖s • EuclideanSpace.single k (1 : ℝ)‖ = |s| := by
    simp [norm_smul, EuclideanSpace.norm_single, Real.norm_eq_abs]
  have hdist : dist x outer.center < inner.radius := by
    simpa only [LocalBall.carrier, Metric.mem_ball, hcenter] using hx
  change dist (x + s • EuclideanSpace.single k 1) outer.center < outer.radius
  calc
    dist (x + s • EuclideanSpace.single k 1) outer.center ≤
        dist (x + s • EuclideanSpace.single k 1) x + dist x outer.center := dist_triangle _ _ _
    _ = |s| + dist x outer.center := by rw [dist_eq_norm, add_sub_cancel_left, hnorm]
    _ < outer.radius := by linarith

private theorem derivative_support {n : ℕ} (l : List (Fin n)) (f : Space n → ℂ) :
    tsupport (coordinateDerivativeList l f) ⊆ tsupport f := by
  induction l with
  | nil => exact Set.Subset.rfl
  | cons i l ih => exact (tsupport_fderiv_apply_subset ℝ
      (EuclideanSpace.single i 1)).trans ih

private theorem derivative_smooth {n : ℕ} (l : List (Fin n))
    (f : Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
    exact (ih.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

private theorem derivative_translate {n : ℕ} (l : List (Fin n))
    (f : Space n → ℂ) (a x : Space n) :
    coordinateDerivativeList l (fun y => f (y - a)) x =
      coordinateDerivativeList l f (x - a) := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    change fderiv ℝ (coordinateDerivativeList l (fun y => f (y - a))) x _ = _
    have he : coordinateDerivativeList l (fun y => f (y - a)) =
        fun y => coordinateDerivativeList l f (y + -a) := by
      funext y
      simpa only [sub_eq_add_neg] using ih y
    rw [he, fderiv_comp_add_right]
    rfl

 def translatedTest {n : ℕ} {inner outer : LocalBall n}
    (a : Space n) (h : ∀ x ∈ inner.carrier, x + a ∈ outer.carrier)
    (φ : TestFunction inner.toOpens ℂ ⊤) : TestFunction outer.toOpens ℂ ⊤ := by
  refine ⟨fun x => φ (x - a), φ.contDiff.comp (contDiff_id.sub contDiff_const),
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight a), ?_⟩
  rw [show (fun x => φ (x - a)) = (fun x => φ x) ∘ Homeomorph.subRight a from rfl,
    tsupport_comp_eq_preimage]
  intro x hx
  have hm : x - a ∈ inner.carrier := φ.tsupport_subset hx
  change x ∈ outer.carrier
  simpa only [sub_add_cancel] using h (x - a) hm

private theorem shifted_integral {n : ℕ} {inner outer : LocalBall n}
    (f : BallL2 outer) (a : Space n)
    (h : ∀ x ∈ inner.carrier, x + a ∈ outer.carrier)
    (φ : TestFunction inner.toOpens ℂ ⊤) (l : List (Fin n)) :
    (∫ x in inner.carrier, zeroExtension f (x + a) *
        coordinateDerivativeList l (fun y => φ y) x) =
      ∫ x in outer.carrier, f x *
        coordinateDerivativeList l (fun y => translatedTest a h φ y) x := by
  have hrestrict : (∫ x in inner.carrier, zeroExtension f (x + a) *
        coordinateDerivativeList l (fun y => φ y) x) =
      ∫ x, zeroExtension f (x + a) * coordinateDerivativeList l (fun y => φ y) x := by
    rw [← integral_indicator (show MeasurableSet inner.carrier from Metric.isOpen_ball.measurableSet)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ inner.carrier
      · simp only [Set.indicator_of_mem hx]
      · have hz : coordinateDerivativeList l (fun y => φ y) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hm => hx (φ.tsupport_subset (derivative_support l _ hm)))
        simp [Set.indicator_of_notMem hx, hz])
  rw [hrestrict]
  have hshift := integral_sub_right_eq_self (μ := volume)
    (fun x => zeroExtension f (x + a) * coordinateDerivativeList l (fun y => φ y) x) a
  simp only [sub_add_cancel] at hshift
  rw [← hshift]
  simp_rw [← derivative_translate l (fun y => φ y) a]
  change (∫ x, zeroExtension f x *
    coordinateDerivativeList l (fun y => φ (y - a)) x) = _
  simp_rw [zeroExtension, ← Set.indicator_mul_left]
  rw [integral_indicator (show MeasurableSet outer.carrier from Metric.isOpen_ball.measurableSet)]
  rfl

private theorem shift_pair_integrable {n : ℕ} (inner : LocalBall n)
    {outer : LocalBall n} (f : BallL2 outer) (a : Space n)
    (φ : TestFunction inner.toOpens ℂ ⊤) (l : List (Fin n)) :
    Integrable (fun x => zeroExtension f (x + a) *
      coordinateDerivativeList l (fun y => φ y) x) (volume.restrict inner.carrier) := by
  have hf := ((zeroExtension_memLp f).comp_measurePreserving
    (measurePreserving_add_right volume a)).mono_measure
      (Measure.restrict_le_self (s := inner.carrier))
  have hd := (derivative_smooth l (fun y => φ y) φ.contDiff).continuous.memLp_of_hasCompactSupport
    (p := 2) (μ := volume.restrict inner.carrier) (φ.hasCompactSupport.of_isClosed_subset isClosed_closure (derivative_support l _))
  exact hf.integrable_mul hd

theorem differenceClass_weakDerivative {n m : ℕ} (inner outer : LocalBall n)
    (hsub : inner.carrier ⊆ outer.carrier) (k : Fin n) (t : ℝ)
    (hshift : ∀ x ∈ inner.carrier, x + t • EuclideanSpace.single k 1 ∈ outer.carrier)
    (α : MultiIndex n m) (f g : BallL2 outer) (hfg : IsWeakDerivative outer α f g) :
    IsWeakDerivative inner α (differenceClass inner f k t)
      (differenceClass inner g k t) := by
  intro φ
  let a : Space n := t • EuclideanSpace.single k 1
  have hzero : ∀ x ∈ inner.carrier, x + (0 : Space n) ∈ outer.carrier := by
    intro x hx
    simpa only [add_zero] using hsub hx
  have ht := hfg (translatedTest a hshift φ)
  have h0 := hfg (translatedTest 0 hzero φ)
  change (∫ x in outer.carrier, f x * coordinateDerivative α
    (fun y => translatedTest a hshift φ y) x) =
    (-1 : ℂ) ^ α.degree * (∫ x in outer.carrier, g x * translatedTest a hshift φ x) at ht
  change (∫ x in outer.carrier, f x * coordinateDerivative α
    (fun y => translatedTest 0 hzero φ y) x) =
    (-1 : ℂ) ^ α.degree * (∫ x in outer.carrier, g x * translatedTest 0 hzero φ x) at h0
  rw [coordinateDerivative, ← shifted_integral f a hshift φ α.directions] at ht
  rw [coordinateDerivative, ← shifted_integral f 0 hzero φ α.directions] at h0
  have hgt := shifted_integral g a hshift φ []
  have hg0 := shifted_integral g 0 hzero φ []
  simp only [coordinateDerivativeList] at hgt hg0
  rw [← hgt] at ht
  rw [← hg0] at h0
  have hleft : (∫ x in inner.carrier, differenceClass inner f k t x *
        coordinateDerivative α (fun y => φ y) x) =
      (t : ℂ)⁻¹ * ((∫ x in inner.carrier, zeroExtension f (x + a) *
          coordinateDerivative α (fun y => φ y) x) -
        ∫ x in inner.carrier, zeroExtension f (x + 0) *
          coordinateDerivative α (fun y => φ y) x) := by
    simp only [coordinateDerivative]
    rw [← integral_sub (shift_pair_integrable inner f a φ α.directions)
      (shift_pair_integrable inner f 0 φ α.directions), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [differenceClass_ae inner f k t] with x hx
    rw [hx]
    simp only [differenceQuotient, add_zero]
    dsimp [a]
    ring
  have hright : (∫ x in inner.carrier, differenceClass inner g k t x * φ x) =
      (t : ℂ)⁻¹ * ((∫ x in inner.carrier, zeroExtension g (x + a) * φ x) -
        ∫ x in inner.carrier, zeroExtension g (x + 0) * φ x) := by
    have hga := shift_pair_integrable inner g a φ []
    have hgzero := shift_pair_integrable inner g 0 φ []
    simp only [coordinateDerivativeList] at hga hgzero
    rw [← integral_sub hga hgzero, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [differenceClass_ae inner g k t] with x hx
    rw [hx]
    simp only [differenceQuotient, add_zero]
    dsimp [a]
    ring
  change (∫ x in inner.carrier, differenceClass inner f k t x *
    coordinateDerivative α (fun y => φ y) x) =
    (-1 : ℂ) ^ α.degree * (∫ x in inner.carrier, differenceClass inner g k t x * φ x)
  rw [hleft, hright, coordinateDerivative, ht, h0]
  ring

def translatedDifferenceSobolev {n m : ℕ} (inner outer : LocalBall n)
    (hsub : inner.carrier ⊆ outer.carrier) (k : Fin n) (t : ℝ)
    (hshift : ∀ x ∈ inner.carrier, x + t • EuclideanSpace.single k 1 ∈ outer.carrier)
    (u : IntegerSobolev outer m) : IntegerSobolev inner m where
  derivatives α := differenceClass inner (u.derivatives α) k t
  weak_derivatives α := differenceClass_weakDerivative inner outer hsub k t hshift
    α _ _ (u.weak_derivatives α)

theorem localized_difference_quotient_data {n : ℕ} (inner outer : LocalBall n)
    (hcenter : inner.center = outer.center) (hgap : inner.radius < outer.radius)
    (u : IntegerSobolev outer 1) (k : Fin n) (t : ℝ)
    (hsafe : |t| < outer.radius - inner.radius) :
    ∃ q : IntegerSobolev inner 1,
      (∀ᵐ x ∂volume.restrict inner.carrier,
        value q x = differenceQuotient k t (zeroExtension (value u)) x) ∧
      (∀ j : Fin n, ∀ᵐ x ∂volume.restrict inner.carrier,
        gradient q j x = differenceQuotient k t (zeroExtension (gradient u j)) x) := by
  have hsub : inner.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hcenter]
    exact Metric.ball_subset_ball hgap.le
  have hshift : ∀ x ∈ inner.carrier,
      x + t • EuclideanSpace.single k 1 ∈ outer.carrier :=
    fun x hx => safe_segment_mem inner outer hcenter k t hsafe hx (le_refl |t|)
  refine ⟨translatedDifferenceSobolev inner outer hsub k t hshift u, ?_, ?_⟩
  · exact differenceClass_ae inner (value u) k t
  · intro j
    exact differenceClass_ae inner (gradient u j) k t

def globalRestriction {n : ℕ} (inner : LocalBall n) :
    Lp ℂ 2 (volume : Measure (Space n)) →L[ℝ] BallL2 inner :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by norm_num)
    (by simpa only [one_smul] using (Measure.restrict_le_self (s := inner.carrier)))

theorem globalRestriction_norm_le {n : ℕ} (inner : LocalBall n)
    (f : Lp ℂ 2 (volume : Measure (Space n))) : ‖globalRestriction inner f‖ ≤ ‖f‖ := by
  have h : ‖globalRestriction inner‖ ≤ 1 := by
    simpa [globalRestriction] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2)
        (c := 1) (by norm_num)
        (by simpa only [one_smul] using (Measure.restrict_le_self (μ := volume) (s := inner.carrier))))
  exact (globalRestriction inner).le_opNorm f |>.trans (by nlinarith [norm_nonneg f])

def translatedGlobalClass {n : ℕ} (inner : LocalBall n)
    (f : Lp ℂ 2 (volume : Measure (Space n))) (a : Space n) : BallL2 inner :=
  globalRestriction inner
    (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f (-a))

theorem translatedGlobalClass_continuous {n : ℕ} (inner : LocalBall n)
    (f : Lp ℂ 2 (volume : Measure (Space n))) : Continuous (translatedGlobalClass inner f) := by
  exact (globalRestriction inner).continuous.comp
    ((KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2_continuous f).comp continuous_neg)

theorem translatedGlobalClass_norm_le {n : ℕ} (inner : LocalBall n)
    (f : Lp ℂ 2 (volume : Measure (Space n))) (a : Space n) :
    ‖translatedGlobalClass inner f a‖ ≤ ‖f‖ := by
  exact (globalRestriction_norm_le inner _).trans_eq
    (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2_norm f (-a))

theorem translatedGlobalClass_ae {n : ℕ} (inner : LocalBall n)
    (f : Lp ℂ 2 (volume : Measure (Space n))) (a : Space n) :
    ∀ᵐ x ∂volume.restrict inner.carrier, translatedGlobalClass inner f a x = f (x + a) := by
  have hr := Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1)
    (by norm_num) (by simpa only [one_smul] using
      (Measure.restrict_le_self (μ := volume) (s := inner.carrier)))
    (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f (-a))
  have ht := (Lp.coeFn_compMeasurePreserving f
    (measurePreserving_sub_right volume (-a))).filter_mono (ae_restrict_le (s := inner.carrier))
  filter_upwards [hr, ht] with x hx hy
  apply hx.trans
  change ((Lp.compMeasurePreserving (fun x => x - -a) _ f) x) = f (x + a)
  simpa only [sub_neg_eq_add, Function.comp_apply] using hy

def segmentAverage {n : ℕ} (inner : LocalBall n) {outer : LocalBall n}
    (f : BallL2 outer) (k : Fin n) (t : ℝ) : BallL2 inner :=
  t⁻¹ • ∫ s in (0 : ℝ)..t, translatedGlobalClass inner
    ((zeroExtension_memLp f).toLp (zeroExtension f)) (s • EuclideanSpace.single k 1)

theorem segmentAverage_norm_le {n : ℕ} (inner : LocalBall n) {outer : LocalBall n}
    (f : BallL2 outer) (k : Fin n) (t : ℝ) (ht : t ≠ 0) :
    ‖segmentAverage inner f k t‖ ≤ ‖f‖ := by
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖translatedGlobalClass inner ((zeroExtension_memLp f).toLp (zeroExtension f))
        (s • EuclideanSpace.single k 1)‖ ≤ ‖f‖ := by
    intro s hs
    exact (translatedGlobalClass_norm_le inner _ _).trans_eq (zeroExtension_norm f)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  change ‖t⁻¹ • _‖ ≤ ‖f‖
  rw [norm_smul]
  calc
    ‖t⁻¹‖ * ‖∫ s in (0 : ℝ)..t, translatedGlobalClass inner
        ((zeroExtension_memLp f).toLp (zeroExtension f)) (s • EuclideanSpace.single k 1)‖
        ≤ ‖t⁻¹‖ * (‖f‖ * |t - 0|) := mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ = ‖f‖ := by
      simp only [Real.norm_eq_abs, abs_inv, sub_zero]
      rw [mul_comm ‖f‖ |t|, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr ht), one_mul]

def testPairing {n : ℕ} {inner : LocalBall n}
    (φ : TestFunction inner.toOpens ℂ ⊤) : BallL2 inner →L[ℝ] ℂ :=
  let hφ : MemLp (fun x => φ x) 2 (volume.restrict inner.carrier) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  let L := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume.restrict inner.carrier) 2 2
  (L.flip (hφ.toLp (fun x => φ x))).restrictScalars ℝ

theorem testPairing_eq_integral {n : ℕ} {inner : LocalBall n}
    (φ : TestFunction inner.toOpens ℂ ⊤) (f : BallL2 inner) :
    testPairing φ f = ∫ x in inner.carrier, f x * φ x := by
  change ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume.restrict inner.carrier) 2 2)
    f ((φ.continuous.memLp_of_hasCompactSupport (p := 2)
      (μ := volume.restrict inner.carrier) φ.hasCompactSupport).toLp (fun x => φ x)) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (φ.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume.restrict inner.carrier)
      φ.hasCompactSupport)] with x hx
  simp only [ContinuousLinearMap.mul_apply']
  rw [hx]

theorem segmentAverage_testPairing {n : ℕ} (inner : LocalBall n) {outer : LocalBall n}
    (f : BallL2 outer) (k : Fin n) (t : ℝ)
    (φ : TestFunction inner.toOpens ℂ ⊤) :
    testPairing φ (segmentAverage inner f k t) =
      t⁻¹ • ∫ s in (0 : ℝ)..t,
        ∫ x in inner.carrier, zeroExtension f (x + s • EuclideanSpace.single k 1) * φ x := by
  let F := (zeroExtension_memLp f).toLp (zeroExtension f)
  have hc : Continuous (fun s : ℝ => translatedGlobalClass inner F
      (s • EuclideanSpace.single k 1)) :=
    (translatedGlobalClass_continuous inner F).comp (by fun_prop)
  have hp : ∀ s : ℝ, testPairing φ (translatedGlobalClass inner F
      (s • EuclideanSpace.single k 1)) =
      ∫ x in inner.carrier, zeroExtension f (x + s • EuclideanSpace.single k 1) * φ x := by
    intro s
    rw [testPairing_eq_integral]
    have hg := ((measurePreserving_add_right volume
      (s • EuclideanSpace.single k 1)).quasiMeasurePreserving.ae
        (zeroExtension_memLp f).coeFn_toLp).filter_mono (ae_restrict_le (s := inner.carrier))
    apply integral_congr_ae
    filter_upwards [translatedGlobalClass_ae inner F (s • EuclideanSpace.single k 1), hg]
      with x hx hy
    rw [hx, hy]
  change testPairing φ (t⁻¹ • ∫ s in (0 : ℝ)..t, translatedGlobalClass inner F
    (s • EuclideanSpace.single k 1)) = _
  rw [map_smul, ← (testPairing φ).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  simp_rw [hp]

private theorem zeroExtension_integrable {n : ℕ} {B : LocalBall n} (f : BallL2 B) :
    Integrable (zeroExtension f) volume := by
  apply (integrable_indicator_iff (show MeasurableSet B.carrier from
    Metric.isOpen_ball.measurableSet)).2
  letI : IsFiniteMeasure (volume.restrict B.carrier) :=
    ⟨by simpa only [Measure.restrict_apply_univ, LocalBall.carrier] using
      (Metric.isBounded_ball (x := B.center) (r := B.radius)).measure_lt_top⟩
  exact (Lp.memLp f).integrable (by norm_num)

private theorem translated_test_hasDerivAt {n : ℕ} {inner outer : LocalBall n}
    (f : BallL2 outer) (φ : TestFunction inner.toOpens ℂ ⊤) (k : Fin n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, zeroExtension f x * φ (x - s • EuclideanSpace.single k 1))
      (∫ x, -(zeroExtension f x * coordinateDerivativeList [k] (fun y => φ y)
        (x - s • EuclideanSpace.single k 1))) s := by
  let d : Space n → ℂ := coordinateDerivativeList [k] (fun y => φ y)
  have hd : Continuous d := (derivative_smooth [k] (fun y => φ y) φ.contDiff).continuous
  have hdc : HasCompactSupport d := φ.hasCompactSupport.of_isClosed_subset isClosed_closure
    (derivative_support [k] _)
  obtain ⟨C, hC⟩ := (hdc.isCompact_range hd).isBounded.exists_norm_le
  have hb : ∀ x, ‖d x‖ ≤ C := fun x => hC _ (Set.mem_range_self x)
  have hc : 0 ≤ C := (norm_nonneg (d 0)).trans (hb 0)
  obtain ⟨D, hD⟩ := (φ.hasCompactSupport.isCompact_range φ.continuous).isBounded.exists_norm_le
  have hDb : ∀ x, ‖φ x‖ ≤ D := fun x => hD _ (Set.mem_range_self x)
  have hi := zeroExtension_integrable f
  have hf : ∀ s : ℝ, Integrable
      (fun x => zeroExtension f x * φ (x - s • EuclideanSpace.single k 1)) volume := by
    intro s
    exact hi.mul_bdd (φ.continuous.comp (show Continuous
      (fun x : Space n => x - s • EuclideanSpace.single k 1) by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hDb _)
  have hm : ∀ s : ℝ, AEStronglyMeasurable
      (fun x => -(zeroExtension f x * d (x - s • EuclideanSpace.single k 1))) volume :=
    fun s => (hi.aestronglyMeasurable.mul (hd.comp (by fun_prop)).aestronglyMeasurable).neg
  have hderiv : ∀ x s, HasDerivAt
      (fun s : ℝ => zeroExtension f x * φ (x - s • EuclideanSpace.single k 1))
      (-(zeroExtension f x * d (x - s • EuclideanSpace.single k 1))) s := by
    intro x s
    have hs := ((hasDerivAt_id s).smul_const (EuclideanSpace.single k (1 : ℝ))).const_sub x
    have hφ := (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt s hs
    have hφ' : HasDerivAt (fun s : ℝ => φ (x - s • EuclideanSpace.single k 1))
        (-d (x - s • EuclideanSpace.single k 1)) s := by
      simpa only [one_smul, Function.comp_def, id_eq, ContinuousLinearMap.map_neg,
        d, coordinateDerivativeList] using hφ
    simpa only [mul_neg] using hφ'.const_mul (zeroExtension f x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := Set.univ) (bound := fun x => ‖zeroExtension f x‖ * C) (by simp)
    (Filter.Eventually.of_forall fun s => (hf s).aestronglyMeasurable) (hf s) (hm s)
    (Filter.Eventually.of_forall fun x s _ => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
    (hi.norm.mul_const C)
    (Filter.Eventually.of_forall fun x s _ => hderiv x s)).2

private theorem first_dirs {n : ℕ} (i : Fin n) : (firstIndex i).directions = [i] := by
  classical
  simp only [MultiIndex.directions, firstIndex, apply_ite Fin.val, Fin.val_one,
    Fin.val_zero, List.replicate_one, List.replicate_zero]
  have h : ∀ l : List (Fin n), l.flatMap (fun j => if j = i then [j] else []) = l.filter (· = i) := by
    intro l; induction l with
    | nil => rfl
    | cons j l ih => by_cases hj : j = i <;> simp [hj, ih]
  have hrep : ∀ j : Fin n, List.replicate (if j = i then 1 else 0) j =
      if j = i then [j] else [] := by intro j; split_ifs <;> simp
  simp_rw [hrep]
  rw [h, List.filter_eq]
  simp

private theorem first_degree {n : ℕ} (i : Fin n) : (firstIndex i).degree = 1 := by
  simp only [firstIndex, MultiIndex.degree, apply_ite Fin.val, Fin.val_one, Fin.val_zero]
  simp

private theorem global_shift_pair {n : ℕ} {inner outer : LocalBall n}
    (f : BallL2 outer) (a : Space n)
    (h : ∀ x ∈ inner.carrier, x + a ∈ outer.carrier)
    (φ : TestFunction inner.toOpens ℂ ⊤) (l : List (Fin n)) :
    (∫ x, zeroExtension f x *
      coordinateDerivativeList l (fun y => φ (y - a)) x) =
      ∫ x in inner.carrier, zeroExtension f (x + a) *
        coordinateDerivativeList l (fun y => φ y) x := by
  rw [shifted_integral f a h φ l]
  simp_rw [zeroExtension, ← Set.indicator_mul_left]
  rw [integral_indicator (show MeasurableSet outer.carrier from Metric.isOpen_ball.measurableSet)]
  rfl

set_option maxHeartbeats 800000 in

theorem differenceClass_eq_segmentAverage {n : ℕ} (inner outer : LocalBall n)
    (hcenter : inner.center = outer.center) (u : IntegerSobolev outer 1)
    (k : Fin n) (t : ℝ) (hsafe : |t| < outer.radius - inner.radius) :
    differenceClass inner (value u) k t = segmentAverage inner (gradient u k) k t := by
  have hsub : inner.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hcenter]
    exact Metric.ball_subset_ball (by linarith [abs_nonneg t])
  have hshift (s : ℝ) (hs : |s| ≤ |t|) :
      ∀ x ∈ inner.carrier, x + s • EuclideanSpace.single k 1 ∈ outer.carrier :=
    fun x hx => safe_segment_mem inner outer hcenter k t hsafe hx hs
  have hpair : ∀ φ : TestFunction inner.toOpens ℂ ⊤,
      testPairing φ (differenceClass inner (value u) k t) =
      testPairing φ (segmentAverage inner (gradient u k) k t) := by
    intro φ
    let P : ℝ → ℂ := fun s => ∫ x, zeroExtension (value u) x *
      φ (x - s • EuclideanSpace.single k 1)
    let G : ℝ → ℂ := fun s => testPairing φ (translatedGlobalClass inner
      ((zeroExtension_memLp (gradient u k)).toLp (zeroExtension (gradient u k)))
      (s • EuclideanSpace.single k 1))
    have hG : Continuous G := (testPairing φ).continuous.comp
      ((translatedGlobalClass_continuous inner _).comp (by fun_prop))
    have hGeq (s : ℝ) : G s = ∫ x in inner.carrier,
        zeroExtension (gradient u k) (x + s • EuclideanSpace.single k 1) * φ x := by
      rw [show G s = testPairing φ (translatedGlobalClass inner
        ((zeroExtension_memLp (gradient u k)).toLp (zeroExtension (gradient u k)))
        (s • EuclideanSpace.single k 1)) from rfl, testPairing_eq_integral]
      apply integral_congr_ae
      have hg := ((measurePreserving_add_right volume (s • EuclideanSpace.single k 1)).quasiMeasurePreserving.ae
        (zeroExtension_memLp (gradient u k)).coeFn_toLp).filter_mono (ae_restrict_le (s := inner.carrier))
      filter_upwards [translatedGlobalClass_ae inner _ (s • EuclideanSpace.single k 1), hg] with x hx hy
      rw [hx, hy]
    have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt P (G s) s := by
      intro s hs
      have habs : |s| ≤ |t| := by
        rcases (Set.mem_uIcc.mp hs) with hs | hs
        · rw [abs_of_nonneg hs.1, abs_of_nonneg (hs.1.trans hs.2)]
          exact hs.2
        · rw [abs_of_nonpos hs.2, abs_of_nonpos (hs.1.trans hs.2)]
          linarith
      have hw := u.weak_derivatives (firstIndex k)
        (translatedTest (s • EuclideanSpace.single k 1) (hshift s habs) φ)
      change (∫ x in outer.carrier, value u x * coordinateDerivative (firstIndex k)
        (fun y => translatedTest (s • EuclideanSpace.single k 1) (hshift s habs) φ y) x) =
        (-1 : ℂ) ^ (firstIndex k).degree *
          (∫ x in outer.carrier, gradient u k x * translatedTest (s • EuclideanSpace.single k 1) (hshift s habs) φ x) at hw
      simp only [coordinateDerivative, first_dirs, first_degree, pow_one] at hw
      have hleft : (∫ x, zeroExtension (value u) x *
          coordinateDerivativeList [k] (fun y => φ (y - s • EuclideanSpace.single k 1)) x) =
          -G s := by
        rw [global_shift_pair (value u) _ (hshift s habs) φ [k],
          shifted_integral (value u) _ (hshift s habs) φ [k], hw]
        have hg := shifted_integral (gradient u k) _ (hshift s habs) φ []
        simp only [coordinateDerivativeList] at hg
        rw [← hg, neg_one_mul, ← hGeq]
      have hd0 := translated_test_hasDerivAt (value u) φ k s
      have he : (∫ x, -(zeroExtension (value u) x *
          coordinateDerivativeList [k] (fun y => φ y) (x - s • EuclideanSpace.single k 1))) = G s := by
        rw [integral_neg]
        simp_rw [← derivative_translate [k] (fun y => φ y) (s • EuclideanSpace.single k 1)]
        rw [hleft, neg_neg]
      exact he ▸ hd0
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hG.intervalIntegrable 0 t)
    have he (s : ℝ) (hs : |s| ≤ |t|) : P s =
        ∫ x in inner.carrier, zeroExtension (value u) (x + s • EuclideanSpace.single k 1) * φ x := by
      exact global_shift_pair (value u) _ (hshift s hs) φ []
    rw [he t le_rfl, he 0 (by simpa using abs_nonneg t)] at hFTC
    rw [testPairing_eq_integral, segmentAverage_testPairing]
    have hleft : (∫ x in inner.carrier, differenceClass inner (value u) k t x * φ x) =
        (t : ℂ)⁻¹ * ((∫ x in inner.carrier,
          zeroExtension (value u) (x + t • EuclideanSpace.single k 1) * φ x) -
          ∫ x in inner.carrier, zeroExtension (value u) (x + 0 • EuclideanSpace.single k 1) * φ x) := by
      have hi := shift_pair_integrable inner (value u) (t • EuclideanSpace.single k 1) φ []
      have h0 := shift_pair_integrable inner (value u) 0 φ []
      simp only [coordinateDerivativeList] at hi h0
      simp only [zero_smul]
      rw [← integral_sub hi h0, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [differenceClass_ae inner (value u) k t] with x hx
      rw [hx]
      simp only [differenceQuotient, add_zero]
      ring
    rw [hleft]
    simp only [zero_smul, add_zero] at hFTC ⊢
    calc
      _ = (t : ℂ)⁻¹ * ∫ s in (0 : ℝ)..t, G s :=
        congrArg (fun z : ℂ => (t : ℂ)⁻¹ * z) hFTC.symm
      _ = _ := by simp only [hGeq, Complex.real_smul, Complex.ofReal_inv]
  let v := differenceClass inner (value u) k t
  let w := segmentAverage inner (gradient u k) k t
  have hzero := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict inner.carrier) (f := fun x => v x - w x)
    ((((Lp.memLp v).sub (Lp.memLp w)).locallyIntegrable (by norm_num)).locallyIntegrableOn inner.carrier)
  have htests : ∀ g : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ inner.carrier →
      (∫ x in inner.carrier, g x • (v x - w x)) = 0 := by
    intro g hg hgc hgs
    let φ : TestFunction inner.toOpens ℂ ⊤ :=
      ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp hg,
        by simpa only [Function.comp_def] using hgc.comp_left (g := Complex.ofReal) rfl, by
          change tsupport (fun x => (g x : ℂ)) ⊆ inner.carrier
          have hsupp : tsupport (fun x => (g x : ℂ)) = tsupport g := by
            unfold tsupport
            congr 1
            ext x
            simp
          rw [hsupp]
          exact hgs⟩
    have hp := hpair φ
    rw [testPairing_eq_integral, testPairing_eq_integral] at hp
    have hv := (Lp.memLp v).integrable_mul
      (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport)
    have hw := (Lp.memLp w).integrable_mul
      (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport)
    change Integrable (fun x => v x * φ x) (volume.restrict inner.carrier) at hv
    change Integrable (fun x => w x * φ x) (volume.restrict inner.carrier) at hw
    have he : (∫ x in inner.carrier, g x • (v x - w x)) =
        (∫ x in inner.carrier, v x * φ x) - ∫ x in inner.carrier, w x * φ x := by
      rw [← integral_sub hv hw]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [Complex.real_smul]
        change (g x : ℂ) * (v x - w x) = v x * (g x : ℂ) - w x * (g x : ℂ)
        ring
    rw [he]
    exact sub_eq_zero.mpr hp
  have hz := hzero htests
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem (show MeasurableSet inner.carrier from Metric.isOpen_ball.measurableSet)] with x hx hm
  exact sub_eq_zero.mp (hx hm)

theorem localized_difference_quotient {n : ℕ} (inner outer : LocalBall n)
    (hcenter : inner.center = outer.center) (hgap : inner.radius < outer.radius)
    (u : IntegerSobolev outer 1) (k : Fin n) (t : ℝ)
    (ht : t ≠ 0) (hsafe : |t| < outer.radius - inner.radius) :
    ∃ q : IntegerSobolev inner 1,
      (∀ᵐ x ∂volume.restrict inner.carrier,
        value q x = differenceQuotient k t (zeroExtension (value u)) x) ∧
      (∀ j : Fin n, ∀ᵐ x ∂volume.restrict inner.carrier,
        gradient q j x = differenceQuotient k t (zeroExtension (gradient u j)) x) ∧
      ‖value q‖ ≤ ‖gradient u k‖ := by
  have hsub : inner.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hcenter]
    exact Metric.ball_subset_ball hgap.le
  have hshift : ∀ x ∈ inner.carrier,
      x + t • EuclideanSpace.single k 1 ∈ outer.carrier :=
    fun x hx => safe_segment_mem inner outer hcenter k t hsafe hx (le_refl |t|)
  refine ⟨translatedDifferenceSobolev inner outer hsub k t hshift u,
    differenceClass_ae inner (value u) k t,
    fun j => differenceClass_ae inner (gradient u j) k t, ?_⟩
  change ‖differenceClass inner (value u) k t‖ ≤ ‖gradient u k‖
  rw [differenceClass_eq_segmentAverage inner outer hcenter u k t hsafe]
  exact segmentAverage_norm_le inner (gradient u k) k t ht

end DedekindZetaZeroFree.WeakH2

end
