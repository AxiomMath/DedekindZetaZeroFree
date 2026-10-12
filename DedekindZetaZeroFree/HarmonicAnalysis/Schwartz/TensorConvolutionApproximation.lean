module

public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.QuadraticKernelAndPhase

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity

open scoped ContDiff Topology
open Filter

private theorem cutoff_derivative_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : SchwartzMap E ℝ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x => u (a • x) - 1) x‖ ≤
      SchwartzMap.seminorm ℝ 0 i u + 1 := by
  have hu : ContDiff ℝ (i : ℕ∞ω) (fun x => u (a • x)) :=
    (u.smooth i).comp (contDiff_id.const_smul a)
  have hc : ‖iteratedFDeriv ℝ i (fun _ : E => (1 : ℝ)) x‖ ≤ 1 := by
    cases i with
    | zero => simp
    | succ i => simp [iteratedFDeriv_succ_const]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i (fun x => u (a • x)) x‖ +
        ‖iteratedFDeriv ℝ i (fun _ : E => (1 : ℝ)) x‖ := by
      change ‖iteratedFDeriv ℝ i ((fun x => u (a • x)) - (fun _ => (1 : ℝ))) x‖ ≤ _
      rw [iteratedFDeriv_sub_apply hu.contDiffAt (contDiffAt_const (c := (1 : ℝ)))]
      exact norm_sub_le _ _
    _ ≤ SchwartzMap.seminorm ℝ 0 i u + 1 := by
      apply add_le_add _ hc
      rw [iteratedFDeriv_comp_const_smul a (u.smooth i), norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha i)]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha ha') (norm_nonneg _)).trans
        (by simpa using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ u i (a • x))

private theorem cutoff_error_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : SchwartzMap E ℝ)
    (hu : ∀ x : E, ‖x‖ < 1 → (u : E → ℝ) =ᶠ[𝓝 x] (fun _ => 1))
    (f g : SchwartzMap E F) (R : ℝ) (hR : 1 ≤ R)
    (hg : ∀ x, g x = u (R⁻¹ • x) • f x) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (g - f) ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (SchwartzMap.seminorm ℝ 0 i u + 1) *
          SchwartzMap.seminorm ℝ (k + 1) (n - i) f) / R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hs : ContDiff ℝ (n : ℕ∞ω) (fun x => u (R⁻¹ • x) - 1) :=
    ((u.smooth n).comp (contDiff_id.const_smul _)).sub contDiff_const
  have he : (g - f : SchwartzMap E F) =
      (fun x => (u (R⁻¹ • x) - 1) • f x) := by
    ext x
    simp [hg, sub_smul]
  apply SchwartzMap.seminorm_le_bound ℝ k n (g - f) (by positivity)
  intro x
  rw [he]
  by_cases hx : ‖x‖ < R
  · have hx' : ‖R⁻¹ • x‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRp)]
      rw [← div_eq_inv_mul, div_lt_one hRp]
      exact hx
    have hv := (hu (R⁻¹ • x) hx').comp_tendsto
      ((continuous_id.const_smul (R⁻¹)).tendsto x)
    have hz : (fun y => (u (R⁻¹ • y) - 1) • f y) =ᶠ[𝓝 x] (fun _ => 0) :=
      hv.mono (fun y hy => by
        change u (R⁻¹ • y) = 1 at hy
        simp [hy])
    rw [(hz.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
    simp
    positivity
  · have hxR : R ≤ ‖x‖ := le_of_not_gt hx
    have hd (j : ℕ) : ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ ≤
        SchwartzMap.seminorm ℝ (k + 1) j f / R := by
      apply (le_div_iff₀ hRp).mpr
      calc
        _ ≤ (‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) * ‖x‖ := by
          gcongr
        _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j f x‖ := by ring
        _ ≤ _ := SchwartzMap.le_seminorm ℝ (k + 1) j f x
    calc
      _ ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => u (R⁻¹ • y) - 1) x‖ *
            ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        gcongr
        exact norm_iteratedFDeriv_smul_le hs (f.smooth n) x le_rfl
      _ ≤ _ := by
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_le_sum
        intro i hi
        have hb := cutoff_derivative_bound u R⁻¹ (inv_nonneg.mpr hRp.le)
          ((inv_le_one₀ hRp).mpr hR) i x
        calc
          _ = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => u (R⁻¹ • y) - 1) x‖ *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
          _ ≤ (n.choose i : ℝ) * (SchwartzMap.seminorm ℝ 0 i u + 1) *
              (SchwartzMap.seminorm ℝ (k + 1) (n - i) f / R) := by
            gcongr
            exact hd (n - i)
          _ = _ := by ring

theorem compactSupport_dense (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Dense {f : SchwartzMap E F | HasCompactSupport (f : E → F)} := by
  intro f
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let u : SchwartzMap E ℝ := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hu : ∀ x : E, ‖x‖ < 1 → (u : E → ℝ) =ᶠ[𝓝 x] (fun _ => 1) := by
    intro x hx
    exact b.eventuallyEq_one_of_mem_ball (by simpa [b, dist_zero_right] using hx)
  have hc (m : ℕ) : HasCompactSupport (fun x : E => u (((m : ℝ) + 1)⁻¹ • x)) := by
    have hm : ((m : ℝ) + 1)⁻¹ ≠ 0 := by positivity
    exact b.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero _ hm)
  have hs (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      u (((m : ℝ) + 1)⁻¹ • x) • f x) :=
    ((u.smooth ⊤).comp (contDiff_id.const_smul _)).smul (f.smooth ⊤)
  let g (m : ℕ) : SchwartzMap E F := ((hc m).smul_right).toSchwartzMap (hs m)
  have hg (m : ℕ) (x : E) : g m x = u (((m : ℝ) + 1)⁻¹ • x) • f x := rfl
  have ht : Tendsto g atTop (𝓝 f) := by
    apply (schwartz_withSeminorms ℝ E F).tendsto_nhds g f |>.mpr
    rintro ⟨k, n⟩ ε hε
    let C := ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (SchwartzMap.seminorm ℝ 0 i u + 1) *
        SchwartzMap.seminorm ℝ (k + 1) (n - i) f
    have hlim : Tendsto (fun m : ℕ => C / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds (x := C)).mul
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with m hm
    exact (cutoff_error_bound u hu f (g m) ((m : ℝ) + 1) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
      (hg m) k n).trans_lt hm
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun m => (hc m).smul_right)

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity

theorem mem_closure_of_fixedSupport_derivative_approximation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set (SchwartzMap E F)) (f : SchwartzMap E F)
    (R : ℝ) (hR : 1 ≤ R)
    (hf : Function.support (f : E → F) ⊆ Metric.closedBall 0 R)
    (happrox : ∀ (N : ℕ) (ε : ℝ), 0 < ε →
      ∃ t : SchwartzMap E F, t ∈ S ∧
        Function.support (t : E → F) ⊆ Metric.closedBall 0 R ∧
        ∀ n ≤ N, ∀ x : E,
          ‖iteratedFDeriv ℝ n (fun z => t z - f z) x‖ < ε) :
    f ∈ closure S := by
  classical
  refine (mem_closure_iff_nhds_basis
    (schwartz_withSeminorms ℝ E F).hasBasis_ball).2 ?_
  rintro ⟨s, δ⟩ hδ
  let K := s.sup (fun i : ℕ × ℕ => i.1)
  let N := s.sup (fun i : ℕ × ℕ => i.2)
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hC : 0 < R ^ K := pow_pos hRp _
  let ε := δ / (2 * R ^ K)
  have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hC)
  obtain ⟨t, ht, htR, htapprox⟩ := happrox N ε hε
  refine ⟨t, ht, ?_⟩
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hδ]
  simp only [Set.mem_iInter]
  intro i hi
  rw [Seminorm.mem_ball]
  change SchwartzMap.seminorm ℝ i.1 i.2 (t - f) < δ
  have hiK : i.1 ≤ K := Finset.le_sup hi
  have hiN : i.2 ≤ N := Finset.le_sup hi
  have hsupp : Function.support (fun z => t z - f z) ⊆ Metric.closedBall 0 R := by
    intro x hx
    by_contra hxR
    have htx : t x = 0 := Function.notMem_support.mp (fun h => hxR (htR h))
    have hfx : f x = 0 := Function.notMem_support.mp (fun h => hxR (hf h))
    exact hx (by simp [htx, hfx])
  have hdsupp : Function.support (iteratedFDeriv ℝ i.2 (fun z => t z - f z)) ⊆
      Metric.closedBall 0 R :=
    (support_iteratedFDeriv_subset i.2).trans (closure_minimal hsupp Metric.isClosed_closedBall)
  have hbound : SchwartzMap.seminorm ℝ i.1 i.2 (t - f) ≤ R ^ K * ε := by
    apply SchwartzMap.seminorm_le_bound ℝ _ _ _ (le_of_lt (mul_pos hC hε))
    intro x
    change ‖x‖ ^ i.1 * ‖iteratedFDeriv ℝ i.2 (fun z => t z - f z) x‖ ≤ R ^ K * ε
    by_cases hx : x ∈ Metric.closedBall 0 R
    · have hxR : ‖x‖ ≤ R := by simpa using hx
      have hp : ‖x‖ ^ i.1 ≤ R ^ K :=
        (pow_le_pow_left₀ (norm_nonneg _) hxR _).trans (pow_le_pow_right₀ hR hiK)
      exact mul_le_mul hp (le_of_lt (htapprox i.2 hiN x)) (norm_nonneg _) (le_of_lt hC)
    · have hd : iteratedFDeriv ℝ i.2 (fun z => t z - f z) x = 0 :=
        Function.notMem_support.mp (fun h => hx (hdsupp h))
      simp only [hd, norm_zero, mul_zero]
      exact le_of_lt (mul_pos hC hε)
  have hsmall : R ^ K * ε < δ := by
    dsimp [ε]
    field_simp
    linarith
  exact lt_of_le_of_lt hbound hsmall

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity

end

end

section

noncomputable section
open scoped Classical Convolution
open ContinuousLinearMap
open MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution.JetQuadrature

set_option maxHeartbeats 1000000 in

theorem convolution_jet_integral
    (ι : Type*) [Fintype ι] (f k s : SchwartzMap (ι → ℂ) ℂ)
    (hf : HasCompactSupport (f : (ι → ℂ) → ℂ))
    (hk : HasCompactSupport (k : (ι → ℂ) → ℂ))
    (hs : ∀ x, s x = ∫ y : ι → ℂ, f y * k (x - y))
    (n : ℕ) (x : ι → ℂ) :
    iteratedFDeriv ℝ n (s : (ι → ℂ) → ℂ) x =
      ∫ y : ι → ℂ, f y • iteratedFDeriv ℝ n (k : (ι → ℂ) → ℂ) (x - y) := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hs]
    calc
      _ = ∫ y : ι → ℂ, (continuousMultilinearCurryFin0 ℝ (ι → ℂ) ℂ).symm
          (f y * k (x-y)) :=
        ((continuousMultilinearCurryFin0 ℝ (ι → ℂ) ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with y
        ext m
        simp
  | succ n ih =>
    let L : ℂ →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin n => ι → ℂ) ℂ) →L[ℝ]
        (ContinuousMultilinearMap ℝ (fun _ : Fin n => ι → ℂ) ℂ) := lsmul ℝ ℂ
    have heq : iteratedFDeriv ℝ n (s : (ι → ℂ) → ℂ) =
        ((f : (ι → ℂ) → ℂ) ⋆[L] iteratedFDeriv ℝ n (k : (ι → ℂ) → ℂ)) := by
      funext z
      exact ih z
    have hg : ContDiff ℝ 1 (iteratedFDeriv ℝ n (k : (ι → ℂ) → ℂ)) :=
      (k.smooth (n+1)).iteratedFDeriv_right (by norm_cast; omega)
    have hd := ((hk.iteratedFDeriv n).hasFDerivAt_convolution_right (μ := volume) L
      f.continuous.locallyIntegrable hg x).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq, hd]
    rw [convolution]
    calc
      _ = ∫ y : ι → ℂ, (continuousMultilinearCurryLeftEquiv ℝ (n := n)
          (fun _ : Fin (n+1) => ι → ℂ) ℂ).symm
          ((L.precompR (ι → ℂ)) (f y) (fderiv ℝ (iteratedFDeriv ℝ n (k : (ι → ℂ) → ℂ)) (x-y))) :=
        by
          convert ((continuousMultilinearCurryLeftEquiv ℝ (n := n)
            (fun _ : Fin (n+1) => ι → ℂ) ℂ).symm.toLinearIsometry.integral_comp_comm
            (μ := volume) (fun y : ι → ℂ => (L.precompR (ι → ℂ)) (f y)
              (fderiv ℝ (iteratedFDeriv ℝ n (k : (ι → ℂ) → ℂ)) (x-y)))).symm <;> rfl
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with y
        ext m
        simp [iteratedFDeriv_succ_apply_left, L]

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution.JetQuadrature

end

end

section

noncomputable section
open scoped Classical Topology BoundedContinuousFunction
open MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution

namespace JetQuadrature

private theorem integral_approx_span {E V : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {f : E → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    {S : Set E} (hfS : Function.support f ⊆ S)
    {T : E → V} (hT : Continuous T) {ε : ℝ} (hε : 0 < ε)
    [IsFiniteMeasureOnCompacts (volume : Measure E)] :
    ∃ (m : ℕ) (c : Fin m → ℂ) (y : Fin m → S),
      ‖(∑ j, c j • T (y j)) - ∫ z, f z • T z‖ < ε := by
  let P := Submodule.span ℂ (Set.range (fun z : S => T z))
  let Q := P.topologicalClosure
  have hmem : ∀ z, f z • T z ∈ Q := by
    intro z
    by_cases hz : f z = 0
    · simp [hz]
    · exact Q.smul_mem _ (P.le_topologicalClosure
        (Submodule.subset_span ⟨⟨z, hfS hz⟩, rfl⟩))
  let g : E → Q := fun z => ⟨f z • T z, hmem z⟩
  have hgc : Continuous g := (hfc.smul hT).subtype_mk _
  have hgs : HasCompactSupport g := hfs.mono (by
    intro z hz
    by_contra hz'
    apply hz
    apply Subtype.ext
    simp only [g, not_not, Function.mem_support] at hz' ⊢
    simp [hz'])
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hI : (∫ z, f z • T z) ∈ Q := by
    have he := Q.subtypeL.integral_comp_comm hgi
    change (∫ z, Q.subtypeL (g z)) ∈ Q
    rw [he]
    exact (∫ z, g z).property
  have hc : (∫ z, f z • T z) ∈ closure (P : Set V) := hI
  obtain ⟨v, hv, hvε⟩ := Metric.mem_closure_iff.mp hc ε hε
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  let e := (Fintype.equivFin a.support).symm
  refine ⟨Fintype.card a.support, (fun j => a (e j)), (fun j => e j), ?_⟩
  have heq : (∑ j, a (e j) • T (e j)) = v := by
    rw [← ha]
    change (∑ j, a (e j) • T (e j)) = ∑ z ∈ a.support, a z • T z
    calc
      _ = ∑ z : a.support, a z • T z := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := Finset.sum_coe_sort a.support (fun z => a z • T z)
  rw [heq]
  simpa [dist_eq_norm, norm_sub_rev] using hvε

 def translatedJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : SchwartzMap E ℂ) (n : ℕ) (y : E) :
    E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => iteratedFDeriv ℝ n k (x - y))
    ((k.smooth ⊤).continuous_iteratedFDeriv (by simp) |>.comp (continuous_id.sub continuous_const))
    (SchwartzMap.seminorm ℝ 0 n k)
    (fun x => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ k n (x-y))

private theorem translatedJet_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : SchwartzMap E ℂ) (hk : HasCompactSupport (k : E → ℂ)) (n : ℕ) :
    Continuous (translatedJet k n) := by
  have hu := (hk.iteratedFDeriv n).uniformContinuous_of_continuous
    ((k.smooth ⊤).continuous_iteratedFDeriv (by simp))
  apply Metric.continuous_iff.mpr
  intro y ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).mpr ?_) (half_lt_self hε)
  intro x
  apply (hd ?_).le
  simpa [dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev] using hz

theorem uniform_translated_jet_quadrature
    (ι : Type*) [Fintype ι] (f k : SchwartzMap (ι → ℂ) ℂ)
    (r : ℝ) (hr : 0 ≤ r)
    (hf : Function.support (f : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 r)
    (hk : HasCompactSupport (k : (ι → ℂ) → ℂ))
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (y : Fin m → ι → ℂ),
      (∀ j, y j ∈ Metric.closedBall 0 r) ∧
      ∀ n ≤ N, ∀ x : ι → ℂ,
        ‖(∑ j, c j • iteratedFDeriv ℝ n (k : (ι → ℂ) → ℂ) (x - y j)) -
          ∫ y : ι → ℂ, f y • iteratedFDeriv ℝ n (k : (ι → ℂ) → ℂ) (x - y)‖ < ε := by
  let E := ι → ℂ
  let V := (n : Fin (N+1)) → E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin n.val => E) ℂ
  letI : NormedAddCommGroup V := Pi.normedAddCommGroup
  letI : NormedSpace ℂ V := Pi.normedSpace
  let T : E → V := fun y n => translatedJet k n y
  have hT : Continuous T := continuous_pi (fun n => translatedJet_continuous k hk n)
  have hfs : HasCompactSupport (f : E → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 r) hf
  obtain ⟨m, c, y, hq⟩ := integral_approx_span (T := T) f.continuous hfs hf hT hε
  refine ⟨m, c, (fun j => y j), (fun j => (y j).property), ?_⟩
  intro n hn x
  let nn : Fin (N+1) := ⟨n, by omega⟩
  let L : V →L[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ x).comp (ContinuousLinearMap.proj nn)
  have hi : Integrable (fun z : E => (f z • T z : V)) :=
    (f.continuous.smul hT).integrable_of_hasCompactSupport hfs.smul_right
  have he := L.integral_comp_comm hi
  have hbound := (BoundedContinuousFunction.norm_coe_le_norm
    (((∑ j, c j • T (y j)) - ∫ z, f z • T z) nn) x).trans
    (norm_le_pi_norm ((∑ j, c j • T (y j)) - ∫ z, f z • T z) nn)
  have hs : L (∑ j, c j • T (y j)) =
      ∑ j, c j • iteratedFDeriv ℝ n k (x - (y j : E)) := by
    simp only [map_sum, map_smul]
    rfl
  have hint : L (∫ z, f z • T z) =
      ∫ z, f z • iteratedFDeriv ℝ n k (x-z) := by
    rw [← he]
    congr 1
  change ‖L ((∑ j, c j • T (y j)) - ∫ z, f z • T z)‖ ≤ _ at hbound
  rw [map_sub, hs, hint] at hbound
  exact hbound.trans_lt hq

end JetQuadrature

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution

end

end

section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution.JetQuadrature

theorem finite_translate_sum_jet
    (ι : Type*) [Fintype ι] (k s t : SchwartzMap (ι → ℂ) ℂ)
    (m : ℕ) (c : Fin m → ℂ) (y : Fin m → ι → ℂ)
    (ht : ∀ x, t x = ∑ j, c j * k (x - y j))
    (n : ℕ) (x : ι → ℂ) :
    iteratedFDeriv ℝ n (fun z => t z - s z) x =
      (∑ j, c j • iteratedFDeriv ℝ n (k : (ι → ℂ) → ℂ) (x - y j)) -
        iteratedFDeriv ℝ n (s : (ι → ℂ) → ℂ) x := by
  have hfun : (fun z => t z - s z) =
      fun z => (∑ j, c j • k (z - y j)) - s z := by
    funext z
    rw [ht z]
    simp [smul_eq_mul]
  rw [hfun]
  change iteratedFDeriv ℝ n ((fun z => ∑ j, c j • (k : (ι → ℂ) → ℂ) (z - y j)) -
      (s : (ι → ℂ) → ℂ)) x = _
  have hsum_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∑ j, c j • (k : (ι → ℂ) → ℂ) (z - y j)) := by
    apply ContDiff.sum
    intro j _
    exact (contDiff_const_smul (c j)).comp
      ((k.smooth (⊤ : ℕ∞)).comp (contDiff_id.sub contDiff_const))
  rw [iteratedFDeriv_sub_apply (hsum_smooth.of_le (by simp)).contDiffAt
    ((s.smooth (⊤ : ℕ∞)).of_le (by simp)).contDiffAt]
  congr 1
  rw [iteratedFDeriv_fun_sum_apply]
  · apply Finset.sum_congr rfl
    intro j _
    have hkj : ContDiffAt ℝ n (fun z => (k : (ι → ℂ) → ℂ) (z - y j)) x :=
      (((k.smooth (⊤ : ℕ∞)).comp (contDiff_id.sub contDiff_const)).of_le (by simp)).contDiffAt
    change iteratedFDeriv ℝ n (c j • (fun z => (k : (ι → ℂ) → ℂ) (z - y j))) x = _
    rw [iteratedFDeriv_const_smul_apply (a := c j)
      (f := fun z => (k : (ι → ℂ) → ℂ) (z - y j)) hkj]
    rw [iteratedFDeriv_comp_sub]
  · intro j _
    exact ((contDiff_const_smul (c j) |>.comp
      ((k.smooth (⊤ : ℕ∞)).comp (contDiff_id.sub contDiff_const))).of_le (by simp)).contDiffAt

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution.JetQuadrature

end

end

section

noncomputable section
open scoped Classical Convolution
open ContinuousLinearMap
open MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution

set_option maxHeartbeats 2000000 in

theorem product_mollification_uniform_derivative_approximation
    (ι : Type*) [Fintype ι] (f : SchwartzMap (ι → ℂ) ℂ)
    (r : ℝ) (hr : 1 ≤ r)
    (hf : Function.support (f : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 r)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : ι → SchwartzMap ℂ ℂ) (s : SchwartzMap (ι → ℂ) ℂ),
      (∀ i, HasCompactSupport (g i : ℂ → ℂ)) ∧
      (∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1) ∧
      (∀ i, ∫ z : ℂ, g i z = 1) ∧
      (∀ x, s x = ∫ y : ι → ℂ, f y * ∏ i, g i (x i - y i)) ∧
      Function.support (s : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 (r + 1) ∧
      ∀ n ≤ N, ∀ x : ι → ℂ,
        ‖iteratedFDeriv ℝ n (fun z => s z - f z) x‖ < ε := by
  let E := ι → ℂ
  have hfc : HasCompactSupport (f : E → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 r) hf
  let V := (n : Fin (N+1)) → ContinuousMultilinearMap ℝ (fun _ : Fin n.val => E) ℂ
  let J : E → V := fun x n => iteratedFDeriv ℝ n.val f x
  have hu : UniformContinuous J := uniformContinuous_pi.mpr (fun n =>
    (hfc.iteratedFDeriv n.val).uniformContinuous_of_continuous
      ((f.smooth ⊤).continuous_iteratedFDeriv (by simp)))
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hu (ε/2) (half_pos hε)
  let a := min 1 (δ/2)
  have ha : 0 < a := lt_min zero_lt_one (half_pos hδ)
  let b : ContDiffBump (0 : ℂ) := ⟨a/2, a, half_pos ha, half_lt_self ha⟩
  let q : ℂ → ℝ := b.normed volume
  have hqc : HasCompactSupport q := b.hasCompactSupport_normed
  have hqs : ContDiff ℝ (⊤ : ℕ∞) q := b.contDiff_normed
  let g0 : SchwartzMap ℂ ℂ :=
    (hqc.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hqs)
  have hg : ∀ z, g0 z = (q z : ℂ) := fun _ => rfl
  have hgi : ∫ z, g0 z = 1 := by
    change ∫ z, Complex.ofRealCLM (q z) = 1
    rw [Complex.ofRealCLM.integral_comp_comm b.integrable_normed, b.integral_normed]
    rfl
  let K : E → ℝ := fun x => ∏ i, q (x i)
  have hKs : ContDiff ℝ (⊤ : ℕ∞) K :=
    contDiff_prod (fun i _ => hqs.comp (contDiff_apply ℝ ℂ i))
  have hKR : Function.support K ⊆ Metric.closedBall 0 a := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg ha.le).mpr
    intro i
    have hi : x i ∈ Function.support q :=
      (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
    rw [b.support_normed_eq] at hi
    exact (by simpa [Metric.mem_ball, dist_zero_right] using hi : ‖x i‖ < a).le
  have hKc : HasCompactSupport K :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 a) hKR
  have hKI : ∫ x, K x = 1 := by
    change (∫ x : ι → ℂ, ∏ i, q (x i)) = 1
    rw [integral_fintype_prod_volume_eq_prod]
    simpa only [q, b.integral_normed, Finset.prod_const_one]
  let k : SchwartzMap E ℂ :=
    (hKc.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hKs)
  have hk : ∀ x, k x = (K x : ℂ) := fun _ => rfl
  have hkc : HasCompactSupport (k : E → ℂ) :=
    hKc.comp_left Complex.ofReal_zero
  let S : E → ℂ := (k : E → ℂ) ⋆[ContinuousLinearMap.mul ℝ ℂ] (f : E → ℂ)
  have hSs : ContDiff ℝ (⊤ : ℕ∞) S :=
    hfc.contDiff_convolution_right _ k.continuous.locallyIntegrable f.smooth'
  have hSR : Function.support S ⊆ Metric.closedBall 0 (r+1) := by
    intro x hx
    obtain ⟨u, hu, v, hv, he⟩ := support_convolution_subset _ hx
    have hu' : ‖u‖ ≤ 1 := by
      have : u ∈ Function.support K := by simpa [Function.mem_support, hk] using hu
      exact (by simpa [Metric.mem_closedBall, dist_zero_right] using hKR this : ‖u‖ ≤ a).trans (min_le_left _ _)
    have hv' : ‖v‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hf hv
    rw [Metric.mem_closedBall, dist_zero_right, ← he]
    exact (norm_add_le _ _).trans (add_le_add hu' hv') |>.trans_eq (add_comm 1 r)
  let s := (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (r+1)) hSR).toSchwartzMap hSs
  have hs : ∀ x, s x = ∫ y : E, k y * f (x-y) := fun _ => rfl
  refine ⟨fun _ => g0, s, ?_, ?_, fun _ => hgi, ?_, hSR, ?_⟩
  · intro i
    exact hqc.comp_left Complex.ofReal_zero
  · intro i z hz
    have hz' : z ∈ Function.support q := by simpa [Function.mem_support, hg] using hz
    rw [b.support_normed_eq] at hz'
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (by simpa [Metric.mem_ball, dist_zero_right] using hz' : ‖z‖ < a).le.trans (min_le_left _ _)
  · intro x
    change S x = _
    rw [show S = (k : E → ℂ) ⋆[ContinuousLinearMap.mul ℝ ℂ] (f : E → ℂ) from rfl, convolution_eq_swap]
    apply integral_congr_ae
    filter_upwards with y
    change k (x-y) * f y = f y * ∏ i, g0 (x i - y i)
    rw [hk, mul_comm]
    congr 1
    change ((∏ i, q (x i - y i) : ℝ) : ℂ) = ∏ i, g0 (x i - y i)
    simp only [Complex.ofReal_prod, hg]
  · intro n hn x
    change ‖iteratedFDeriv ℝ n ((s : E → ℂ) - (f : E → ℂ)) x‖ < ε
    rw [iteratedFDeriv_sub (s.smooth n) (f.smooth n)]
    change ‖iteratedFDeriv ℝ n (s : E → ℂ) x - iteratedFDeriv ℝ n (f : E → ℂ) x‖ < ε
    rw [JetQuadrature.convolution_jet_integral ι k f s hkc hfc hs n x]
    have hball : Function.support K ⊆ Metric.ball 0 δ := by
      intro z hz
      have hz' : ‖z‖ ≤ a := by simpa [Metric.mem_closedBall, dist_zero_right] using hKR hz
      simpa [Metric.mem_ball, dist_zero_right] using hz'.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hδ))
    have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ n (f : E → ℂ)) volume :=
      ((f.smooth ⊤).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    have hclose : ∀ z ∈ Metric.ball x δ,
        dist (iteratedFDeriv ℝ n (f : E → ℂ) z) (iteratedFDeriv ℝ n (f : E → ℂ) x) ≤ ε/2 := by
      intro z hz
      have hdist := (hd (by simpa [Metric.mem_ball] using hz)).le
      let nn : Fin (N+1) := ⟨n, by omega⟩
      have hb := norm_le_pi_norm (J z - J x) nn
      change ‖iteratedFDeriv ℝ n (f : E → ℂ) z - iteratedFDeriv ℝ n (f : E → ℂ) x‖ ≤ ‖J z - J x‖ at hb
      rw [dist_eq_norm] at hdist ⊢
      exact hb.trans hdist
    have hbound := dist_convolution_le (μ := volume) (f := K) (g := iteratedFDeriv ℝ n (f : E → ℂ))
      (x₀ := x) (z₀ := iteratedFDeriv ℝ n (f : E → ℂ) x) (half_pos hε).le hball
      (fun z => Finset.prod_nonneg (fun i _ => b.nonneg_normed (z i))) hKI
      hmeas hclose
    have he : (∫ y : E, k y • iteratedFDeriv ℝ n (f : E → ℂ) (x-y)) =
        (K ⋆[lsmul ℝ ℝ] iteratedFDeriv ℝ n (f : E → ℂ)) x := by
      apply integral_congr_ae
      filter_upwards with y
      simp [hk, Complex.real_smul]
    rw [he]
    exact (by simpa [dist_eq_norm] using hbound : ‖_ - _‖ ≤ ε/2).trans_lt (half_lt_self hε)

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution

end

end

section

noncomputable section
open scoped Classical
open MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution

theorem translated_product_support (ι : Type*) [Fintype ι] (r : ℝ) (hr : 0 ≤ r)
    (g : ι → SchwartzMap ℂ ℂ)
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (y : ι → ℂ) (hy : y ∈ Metric.closedBall 0 r) :
    Function.support (fun x : ι → ℂ => ∏ i, g i (x i - y i)) ⊆
      Metric.closedBall 0 (r + 1) := by
  intro x hx
  have hprod : (∏ i, g i (x i - y i)) ≠ 0 := hx
  have hxy : ‖x - y‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    have hi : x i - y i ∈ Function.support (g i : ℂ → ℂ) := by
      exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    simpa [Metric.mem_closedBall, dist_zero_right] using hgR i hi
  have hy' : ‖y‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
  have he : x = (x - y) + y := by simp
  rw [Metric.mem_closedBall, dist_zero_right, he]
  exact (norm_add_le _ _).trans (add_le_add hxy hy') |>.trans_eq (add_comm 1 r)

def translatedProduct (ι : Type*) [Fintype ι]
    (g : ι → SchwartzMap ℂ ℂ)
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (y : ι → ℂ) : SchwartzMap (ι → ℂ) ℂ :=
  (HasCompactSupport.intro (f := fun x : ι → ℂ => ∏ i, g i (x i - y i))
    (isCompact_closedBall y 1) (by
    intro x hx
    by_contra h
    apply hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    have hi : x i - y i ∈ Function.support (g i : ℂ → ℂ) :=
      (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
    simpa [Metric.mem_closedBall, dist_zero_right] using hgR i hi)).toSchwartzMap
    (contDiff_prod fun i _ => (g i).smooth'.comp ((contDiff_apply ℝ ℂ i).sub contDiff_const))

theorem translatedProduct_apply (ι : Type*) [Fintype ι]
    (g : ι → SchwartzMap ℂ ℂ)
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (y x : ι → ℂ) : translatedProduct ι g hgR y x = ∏ i, g i (x i - y i) := rfl

theorem translatedProduct_mem_span (ι : Type*) [Fintype ι]
    (g : ι → SchwartzMap ℂ ℂ)
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (y : ι → ℂ) : translatedProduct ι g hgR y ∈ Submodule.span ℂ
      {u : SchwartzMap (ι → ℂ) ℂ | ∃ k : ι → SchwartzMap ℂ ℂ,
        ∀ z, u z = ∏ i, k i (z i)} := by
  apply Submodule.subset_span
  exact ⟨fun i => (g i).compSubConstCLM ℂ (y i), fun z => rfl⟩

theorem quadrature_tensor_support (ι : Type*) [Fintype ι] (r : ℝ) (hr : 0 ≤ r)
    (g : ι → SchwartzMap ℂ ℂ)
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (m : ℕ) (c : Fin m → ℂ) (y : Fin m → ι → ℂ)
    (hy : ∀ j, y j ∈ Metric.closedBall 0 r) :
    (∑ j, c j • translatedProduct ι g hgR (y j)) ∈ Submodule.span ℂ
      {u : SchwartzMap (ι → ℂ) ℂ | ∃ k : ι → SchwartzMap ℂ ℂ,
        ∀ z, u z = ∏ i, k i (z i)} ∧
    Function.support (fun x => (∑ j, c j • translatedProduct ι g hgR (y j)) x) ⊆
      Metric.closedBall 0 (r + 1) := by
  constructor
  · exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (translatedProduct_mem_span ι g hgR (y j))
  · intro x hx
    by_contra hball
    apply hx
    simp only [SchwartzMap.sum_apply, SchwartzMap.smul_apply]
    apply Finset.sum_eq_zero
    intro j _
    have hz : translatedProduct ι g hgR (y j) x = 0 := by
      by_contra hn
      exact hball (translated_product_support ι r hr g hgR (y j) (hy j) hn)
    simp [hz]

theorem finite_tensor_approximation_of_quadrature
    (ι : Type*) [Fintype ι] (r : ℝ) (hr : 0 ≤ r)
    (g : ι → SchwartzMap ℂ ℂ)
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (s : SchwartzMap (ι → ℂ) ℂ) (N : ℕ) (ε : ℝ)
    (hq : ∃ (m : ℕ) (c : Fin m → ℂ) (y : Fin m → ι → ℂ),
      (∀ j, y j ∈ Metric.closedBall 0 r) ∧
      ∀ n ≤ N, ∀ x : ι → ℂ,
        ‖iteratedFDeriv ℝ n (fun z =>
          (∑ j, c j • translatedProduct ι g hgR (y j)) z - s z) x‖ < ε) :
    ∃ t : SchwartzMap (ι → ℂ) ℂ,
      t ∈ Submodule.span ℂ
        {u : SchwartzMap (ι → ℂ) ℂ |
          ∃ k : ι → SchwartzMap ℂ ℂ, ∀ z, u z = ∏ i, k i (z i)} ∧
      Function.support (t : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 (r + 1) ∧
      ∀ n ≤ N, ∀ x : ι → ℂ,
        ‖iteratedFDeriv ℝ n (fun z => t z - s z) x‖ < ε := by
  obtain ⟨m, c, y, hy, hjet⟩ := hq
  obtain ⟨ht, hsupp⟩ := quadrature_tensor_support ι r hr g hgR m c y hy
  exact ⟨∑ j, c j • translatedProduct ι g hgR (y j), ht, hsupp, hjet⟩
namespace KernelAux

variable {ι : Type*} [Fintype ι]

lemma translated_product_support (g : ι → SchwartzMap ℂ ℂ)
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (y : ι → ℂ) :
    Function.support (fun x : ι → ℂ => ∏ i, g i (x i - y i)) ⊆
      Metric.closedBall y 1 := by
  intro x hx
  have hx' : ∏ i, g i (x i - y i) ≠ 0 := hx
  have hne : ∀ i, g i (x i - y i) ≠ 0 := by
    simpa using (Finset.prod_ne_zero_iff.mp hx')
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro i
  simpa [Metric.mem_closedBall, dist_eq_norm] using hgR i (hne i)

lemma translated_product_compact (g : ι → SchwartzMap ℂ ℂ)
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (y : ι → ℂ) : HasCompactSupport (fun x : ι → ℂ => ∏ i, g i (x i - y i)) := by
  apply HasCompactSupport.intro (isCompact_closedBall y 1)
  intro x hx
  by_contra h
  exact hx (translated_product_support g hgR y h)

end KernelAux

theorem product_convolution_finite_tensor_approximation
    (ι : Type*) [Fintype ι] (f : SchwartzMap (ι → ℂ) ℂ)
    (r : ℝ) (hr : 0 ≤ r)
    (hf : Function.support (f : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 r)
    (g : ι → SchwartzMap ℂ ℂ)
    (hg : ∀ i, HasCompactSupport (g i : ℂ → ℂ))
    (hgR : ∀ i, Function.support (g i : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (s : SchwartzMap (ι → ℂ) ℂ)
    (hs : ∀ x, s x = ∫ y : ι → ℂ, f y * ∏ i, g i (x i - y i))
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : SchwartzMap (ι → ℂ) ℂ,
      t ∈ Submodule.span ℂ
        {u : SchwartzMap (ι → ℂ) ℂ |
          ∃ k : ι → SchwartzMap ℂ ℂ, ∀ z, u z = ∏ i, k i (z i)} ∧
      Function.support (t : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 (r + 1) ∧
      ∀ n ≤ N, ∀ x : ι → ℂ,
        ‖iteratedFDeriv ℝ n (fun z => t z - s z) x‖ < ε := by
  apply finite_tensor_approximation_of_quadrature ι r hr g hgR s N ε
  let k := translatedProduct ι g hgR 0
  have hk : HasCompactSupport (k : (ι → ℂ) → ℂ) := by
    exact KernelAux.translated_product_compact g hgR 0
  have hfcompact : HasCompactSupport (f : (ι → ℂ) → ℂ) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) r)
    intro x hx
    by_contra h
    exact hx (hf h)
  have hs' : ∀ x, s x = ∫ y : ι → ℂ, f y * k (x - y) := by
    intro x
    simpa [k, translatedProduct_apply] using hs x
  obtain ⟨m, c, y, hy, hjet⟩ :=
    JetQuadrature.uniform_translated_jet_quadrature ι f k r hr hf hk N ε hε
  refine ⟨m, c, y, hy, ?_⟩
  intro n hn x
  have ht : ∀ z, (∑ j, c j • translatedProduct ι g hgR (y j)) z =
      ∑ j, c j * k (z - y j) := by
    intro z
    simp [k, SchwartzMap.sum_apply, SchwartzMap.smul_apply, translatedProduct_apply]
  rw [JetQuadrature.finite_translate_sum_jet ι k s
    (∑ j, c j • translatedProduct ι g hgR (y j)) m c y ht n x,
    JetQuadrature.convolution_jet_integral ι f k s hfcompact hk hs' n x]
  exact hjet n hn x

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity.ProductConvolution

end

end

section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity

theorem compactSupport_support_radius (ι : Type*) [Fintype ι]
    (f : SchwartzMap (ι → ℂ) ℂ) (hf : HasCompactSupport (f : (ι → ℂ) → ℂ)) :
    ∃ R : ℝ, 1 ≤ R ∧ Function.support (f : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 R := by
  obtain ⟨R, hR, hs⟩ := hf.isCompact.isBounded.subset_closedBall_lt 1 0
  exact ⟨R, hR.le, Set.Subset.trans (subset_closure) hs⟩

theorem compact_tensor_uniform_approximation (ι : Type*) [Fintype ι]
    (f : SchwartzMap (ι → ℂ) ℂ) (hf : HasCompactSupport (f : (ι → ℂ) → ℂ)) :
    ∃ R : ℝ, 1 ≤ R ∧
      Function.support (f : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 R ∧
      ∀ (N : ℕ) (ε : ℝ), 0 < ε →
        ∃ t : SchwartzMap (ι → ℂ) ℂ,
          t ∈ Submodule.span ℂ
            {u : SchwartzMap (ι → ℂ) ℂ |
              ∃ g : ι → SchwartzMap ℂ ℂ, ∀ z, u z = ∏ i, g i (z i)} ∧
          Function.support (t : (ι → ℂ) → ℂ) ⊆ Metric.closedBall 0 R ∧
          ∀ n ≤ N, ∀ x : ι → ℂ,
            ‖iteratedFDeriv ℝ n (fun z => t z - f z) x‖ < ε := by
  classical
  obtain ⟨r, hr, hfr⟩ := compactSupport_support_radius ι f hf
  have hrr : r ≤ r + 1 := by linarith
  refine ⟨r + 1, by linarith, hfr.trans
    (Metric.closedBall_subset_closedBall hrr), ?_⟩
  intro N ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨g, s, hg, hgR, hunit, hs, hsR, hsapprox⟩ :=
    ProductConvolution.product_mollification_uniform_derivative_approximation
      ι f r hr hfr N (ε / 2) hhalf
  obtain ⟨t, ht, htR, htapprox⟩ :=
    ProductConvolution.product_convolution_finite_tensor_approximation
      ι f r (by linarith) hfr g hg hgR s hs N (ε / 2) hhalf
  refine ⟨t, ht, htR, ?_⟩
  intro n hn x
  have hsplit :
      iteratedFDeriv ℝ n (fun z => t z - f z) x =
        iteratedFDeriv ℝ n (fun z => t z - s z) x +
          iteratedFDeriv ℝ n (fun z => s z - f z) x := by
    rw [fun_iteratedFDeriv_sub_apply (t.smooth n).contDiffAt (f.smooth n).contDiffAt,
      fun_iteratedFDeriv_sub_apply (t.smooth n).contDiffAt (s.smooth n).contDiffAt,
      fun_iteratedFDeriv_sub_apply (s.smooth n).contDiffAt (f.smooth n).contDiffAt]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans_lt
    (by have h₁ := htapprox n hn x
        have h₂ := hsapprox n hn x
        linarith)

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps.TensorDensity

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical

namespace DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

variable {ι : Type*} [Fintype ι]

def productFourier (f : (ι → ℂ) → ℂ) (y : ι → ℂ) : ℂ :=
  ∫ z, f z * ∏ i, ComplexWeil.psi 2 (-z i * y i)
    ∂Measure.pi (fun _ : ι => ComplexWeil.mu 2)

def productChirp (b : ι → ℂ) (f : (ι → ℂ) → ℂ) (z : ι → ℂ) : ℂ :=
  (∏ i, ComplexWeil.psi 2 (b i * z i ^ 2)) * f z

def productDilation (c : ι → ℂ) (f : (ι → ℂ) → ℂ) (z : ι → ℂ) : ℂ :=
  f (fun i => c i * z i)

def tensorCore (ι : Type*) [Fintype ι] : Submodule ℂ (SchwartzMap (ι → ℂ) ℂ) :=
  Submodule.span ℂ {f | ∃ g : ι → SchwartzMap ℂ ℂ, ∀ z, f z = ∏ i, g i (z i)}

theorem tensorCore_dense (ι : Type*) [Fintype ι] :
    Dense (tensorCore ι : Set (SchwartzMap (ι → ℂ) ℂ)) := by
  have hcompact :
      {f : SchwartzMap (ι → ℂ) ℂ | HasCompactSupport (f : (ι → ℂ) → ℂ)} ⊆
        closure (tensorCore ι : Set (SchwartzMap (ι → ℂ) ℂ)) := by
    intro f hf
    obtain ⟨R, hR, hsupport, happrox⟩ :=
      TensorDensity.compact_tensor_uniform_approximation ι f hf
    exact TensorDensity.mem_closure_of_fixedSupport_derivative_approximation
      (tensorCore ι : Set (SchwartzMap (ι → ℂ) ℂ)) f R hR hsupport happrox
  exact ((TensorDensity.compactSupport_dense (ι → ℂ) ℂ).mono hcompact).of_closure

end DedekindZetaZeroFree.QuadraticRawProduct.ArchimedeanSteps

end

end
