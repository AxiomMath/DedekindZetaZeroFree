module

public import DedekindZetaZeroFree.Analysis.WeakH2.SecondWeakDerivatives

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalDifference

open KPContLocalNorm KPContLocalEnergy

def BoundedFirstDerivatives {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (L : ℝ) : Prop :=
  ∀ x ∈ B.carrier, ∀ i j k : Fin n,
    ‖fderiv ℝ (fun y => D.density y * D.matrix y i j) x
      (EuclideanSpace.single k 1)‖ ≤ L

def WeakH2Estimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ) (M C : ℝ) : Prop :=
  ∀ (z : ℂ), ‖z‖ ≤ M → ∀ (u : IntegerSobolev outer 1) (h : BallL2 outer),
    WeakEquation D z u h → ∃ v : IntegerSobolev inner 2,
      Represents v (fun x => value u x) ∧
      v.sobolevNorm ≤ C * (u.sobolevNorm + ‖h‖)

end DedekindZetaZeroFree.KPContLocalDifference

namespace DedekindZetaZeroFree

open KPContLocalNorm KPContLocalEnergy KPContLocalDifference

theorem kp_cont_local_difference_h2 (n : ℕ) (hn : 0 < n)
    (r R cρ Cρ κ Λ L M : ℝ) (hr : 0 < r) (hrR : r < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (inner outer : LocalBall n),
      inner.center = outer.center → inner.radius = r → outer.radius = R →
      ∀ D : Coefficients outer cρ Cρ κ Λ,
        BoundedFirstDerivatives D L → WeakH2Estimate inner outer D M C := by
  classical
  obtain ⟨K, hK, hest⟩ := WeakH2.coercive_difference_estimate n hn
    r R cρ Cρ κ Λ L M hr hrR hcρ hκ hL hM
  refine ⟨Real.sqrt (1 + (n : ℝ) ^ 2 * K ^ 2), by positivity, ?_⟩
  intro inner outer hc hir hor D hD z hz u h heq
  let mid : LocalBall n := ⟨hn, outer.center, (r + R) / 2, by linarith⟩
  have hgap : inner.radius < outer.radius := by rw [hir, hor]; exact hrR
  have hsub : inner.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hc]
    exact Metric.ball_subset_ball hgap.le
  have hsm : inner.carrier ⊆ mid.carrier := by
    change Metric.ball inner.center inner.radius ⊆ Metric.ball outer.center ((r + R) / 2)
    rw [hc, hir]
    exact Metric.ball_subset_ball (by linarith)
  obtain ⟨η, hηone, hη⟩ := hest inner mid outer hc rfl hir rfl hor
  let Dr : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients outer cρ Cρ κ Λ :=
    { density := D.density
      matrix := D.matrix
      density_smooth := D.density_smooth
      matrix_smooth := D.matrix_smooth
      density_bounds := D.density_bounds
      symmetric := D.symmetric
      ellipticity := D.ellipticity
      upper_bound := D.upper_bound }
  let A : ℝ := K * (u.sobolevNorm + ‖h‖)
  have hA : 0 ≤ A := by dsimp [A, IntegerSobolev.sobolevNorm]; positivity
  have hpair := fun j k => WeakH2.difference_bound_to_test_pairing inner outer hc hgap
    (gradient u j) k ((R - r) / 8) A (by linarith) hA
  have hbound : ∀ (j k : Fin n) (t : ℝ), t ≠ 0 → |t| < (R - r) / 8 →
      MeasureTheory.MemLp (WeakH2.differenceQuotient k t (WeakH2.zeroExtension (gradient u j)))
        2 (MeasureTheory.volume.restrict inner.carrier) ∧
      (∫ x in inner.carrier, ‖WeakH2.differenceQuotient k t
        (WeakH2.zeroExtension (gradient u j)) x‖ ^ 2) ≤ A ^ 2 := by
    intro j k t ht hts
    obtain ⟨hm, hb⟩ := hη Dr hD z hz u h heq k t ht hts
    change (∀ j : Fin n, MeasureTheory.MemLp (fun x => (η x : ℂ) *
      WeakH2.differenceQuotient k t (WeakH2.zeroExtension (gradient u j)) x)
      2 (MeasureTheory.volume.restrict mid.carrier)) at hm
    change (∑ j : Fin n, ∫ x in mid.carrier, ‖(η x : ℂ) *
      WeakH2.differenceQuotient k t (WeakH2.zeroExtension (gradient u j)) x‖ ^ 2)
      ≤ K ^ 2 * (u.sobolevNorm + ‖h‖) ^ 2 at hb
    let f := fun x => (η x : ℂ) * WeakH2.differenceQuotient k t
      (WeakH2.zeroExtension (gradient u j)) x
    have hfe : f =ᵐ[MeasureTheory.volume.restrict inner.carrier]
        WeakH2.differenceQuotient k t (WeakH2.zeroExtension (gradient u j)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      simp [f, hηone x hx]
    refine ⟨((hm j).mono_measure (MeasureTheory.Measure.restrict_mono hsm le_rfl)).ae_eq hfe, ?_⟩
    have hfi : (∫ x in inner.carrier, ‖f x‖ ^ 2) =
        ∫ x in inner.carrier, ‖WeakH2.differenceQuotient k t
          (WeakH2.zeroExtension (gradient u j)) x‖ ^ 2 :=
      MeasureTheory.integral_congr_ae (hfe.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    rw [← hfi]
    calc
      _ ≤ ∫ x in mid.carrier, ‖f x‖ ^ 2 := by
        have hi : MeasureTheory.IntegrableOn (fun x => ‖f x‖ ^ 2) mid.carrier
            MeasureTheory.volume := (hm j).integrable_norm_pow (by decide)
        exact MeasureTheory.setIntegral_mono_set hi
          (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hsm)
      _ ≤ ∑ i : Fin n, ∫ x in mid.carrier,
          ‖(η x : ℂ) * WeakH2.differenceQuotient k t
            (WeakH2.zeroExtension (gradient u i)) x‖ ^ 2 :=
        Finset.single_le_sum (f := fun i : Fin n => ∫ x in mid.carrier,
          ‖(η x : ℂ) * WeakH2.differenceQuotient k t
            (WeakH2.zeroExtension (gradient u i)) x‖ ^ 2)
          (fun i _ => MeasureTheory.integral_nonneg (fun x => sq_nonneg _))
          (Finset.mem_univ j)
      _ ≤ A ^ 2 := by simpa only [A, mul_pow] using hb
  obtain ⟨v, hv, hvn⟩ := WeakH2.assemble_second_weak_derivatives inner outer hsub u A hA
    (fun j k => hpair j k (hbound j k))
  refine ⟨v, hv, ?_⟩
  have hu0 : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v.sobolevNorm := Real.sqrt_nonneg _
  have hs : 0 ≤ 1 + (n : ℝ) ^ 2 * K ^ 2 := by positivity
  apply (sq_le_sq₀ hv0 (mul_nonneg (Real.sqrt_nonneg _) (by positivity))).mp
  rw [v.sobolevNorm_sq, mul_pow, Real.sq_sqrt hs]
  have hu := u.sobolevNorm_sq
  have hsq : u.normSq ≤ (u.sobolevNorm + ‖h‖) ^ 2 := by nlinarith [norm_nonneg h]
  calc
    v.normSq ≤ u.normSq + (n : ℝ) ^ 2 * A ^ 2 := hvn
    _ ≤ (u.sobolevNorm + ‖h‖) ^ 2 + (n : ℝ) ^ 2 * A ^ 2 := add_le_add hsq le_rfl
    _ = (1 + (n : ℝ) ^ 2 * K ^ 2) * (u.sobolevNorm + ‖h‖) ^ 2 := by dsimp [A]; ring

end DedekindZetaZeroFree

noncomputable section
open MeasureTheory
namespace DedekindZetaZeroFree.KPContLocalDifference.WeakRecovery
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

end DedekindZetaZeroFree.KPContLocalDifference.WeakRecovery

noncomputable section
namespace DedekindZetaZeroFree.KPContLocalDifference.WeakRecovery
open MeasureTheory KPContLocalNorm Filter Topology
 theorem weak_derivative_of_bounded_pairing_limit {n k : ℕ} (B : LocalBall n)
    (α : MultiIndex n k) (u : BallL2 B) {C : ℝ} (hC : 0 ≤ C)
    {ι : Type*} (l : Filter ι) [l.NeBot] (w : ι → BallL2 B)
    (hw : ∀ᶠ t in l, ‖w t‖ ≤ C)
    (hlim : ∀ φ : TestFunction B.toOpens ℂ ⊤,
      Tendsto (fun t => ∫ x in B.carrier, w t x * φ x) l
        (𝓝 (∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x))) :
    ∃ v : BallL2 B, IsWeakDerivative B α u v ∧ ‖v‖ ≤ C := by
  apply weak_derivative_of_test_bound B α u hC
  intro φ
  apply le_of_tendsto (hlim φ).norm
  filter_upwards [hw] with t ht
  rw [integral_mul_eq_inner]
  calc
    ‖inner ℂ (star (w t)) (testL2 B φ)‖ ≤ ‖star (w t)‖ * ‖testL2 B φ‖ :=
      norm_inner_le_norm _ _
    _ = ‖w t‖ * ‖testL2 B φ‖ := by rw [norm_star_L2]
    _ ≤ C * ‖testL2 B φ‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
end DedekindZetaZeroFree.KPContLocalDifference.WeakRecovery

end
end
end
