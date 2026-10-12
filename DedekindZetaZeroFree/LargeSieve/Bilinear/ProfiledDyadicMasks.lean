module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.OrientedHeckeRows
public import DedekindZetaZeroFree.Moments.Reflected.LocalizedFourierProfiles

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

namespace RMMaskedDyadic
open MeasureTheory

theorem finite_integral_l2 {I : Type*} [Fintype I]
    (g : ℝ → I → ℂ) (hg : ∀ i, Integrable (fun t => g t i)) :
    Real.sqrt (∑ i, ‖∫ t, g t i‖ ^ 2) ≤
      ∫ t, Real.sqrt (∑ i, ‖g t i‖ ^ 2) := by
  let G : ℝ → EuclideanSpace ℂ I := fun t => WithLp.toLp 2 (g t)
  have hG : Integrable G := integrable_piLp_iff.mpr hg
  have he : (∫ t, G t) = WithLp.toLp 2 (fun i => ∫ t, g t i) := by
    ext i
    exact eval_integral_piLp hg i
  have hb := norm_integral_le_integral_norm (μ := volume) G
  rw [he, EuclideanSpace.norm_eq] at hb
  simpa only [EuclideanSpace.norm_eq, G, PiLp.toLp_apply] using hb

theorem finite_integral_l2_bound {I : Type*} [Fintype I]
    (g : ℝ → I → ℂ) (hg : ∀ i, Integrable (fun t => g t i))
    (W : ℝ → ℂ) (hW : Integrable W) (B : ℝ)
    (hbound : ∀ t, Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤ ‖W t‖ * B) :
    Real.sqrt (∑ i, ‖∫ t, g t i‖ ^ 2) ≤ (∫ t, ‖W t‖) * B := by
  apply (finite_integral_l2 g hg).trans
  rw [← integral_mul_const]
  apply integral_mono
  · exact (integrable_piLp_iff.mpr hg : Integrable
      (fun t => (WithLp.toLp 2 (g t) : EuclideanSpace ℂ I))).norm.congr
      (Filter.Eventually.of_forall fun t => EuclideanSpace.norm_eq _)
  · exact hW.norm.mul_const B
  · exact hbound

set_option maxHeartbeats 1000000 in
theorem finite_separated_sieve {I U : Type*} [Fintype I] [Fintype U]
    (a : U → I → ℂ) (P : U → I → ℂ) (W : ℝ → ℂ)
    (cp : ℝ → U → ℂ) (rp : ℝ → I → ℂ) (B : ℝ)
    (hW : Integrable W)
    (hpair : ∀ c d, Integrable (fun t => W t * cp t c * rp t d))
    (hP : ∀ c d, P c d = ∫ t, W t * cp t c * rp t d)
    (hrp : ∀ t d, ‖rp t d‖ = 1)
    (hbound : ∀ t, Real.sqrt (∑ d, ‖∑ c, a c d * cp t c‖ ^ 2) ≤ B) :
    Real.sqrt (∑ d, ‖∑ c, a c d * P c d‖ ^ 2) ≤ (∫ t, ‖W t‖) * B := by
  let g : ℝ → I → ℂ := fun t d => ∑ c, a c d * (W t * cp t c * rp t d)
  have hg : ∀ d, Integrable (fun t => g t d) := by
    intro d
    exact integrable_finset_sum _ (fun c _ => (hpair c d).const_mul (a c d))
  have he : ∀ d, (∑ c, a c d * P c d) = ∫ t, g t d := by
    intro d
    rw [integral_finset_sum _ (fun c _ => (hpair c d).const_mul (a c d))]
    apply Finset.sum_congr rfl
    intro c hc
    rw [integral_const_mul, ← hP c d]
  simp_rw [he]
  apply finite_integral_l2_bound g hg W hW B
  intro t
  have hvec : WithLp.toLp 2 (g t) = W t •
      (WithLp.toLp 2 (fun d => rp t d * ∑ c, a c d * cp t c) : EuclideanSpace ℂ I) := by
    ext d
    simp only [g, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  calc
    Real.sqrt (∑ d, ‖g t d‖ ^ 2) = ‖(WithLp.toLp 2 (g t) : EuclideanSpace ℂ I)‖ :=
      by simpa only [PiLp.toLp_apply] using
        (EuclideanSpace.norm_eq (WithLp.toLp 2 (g t) : EuclideanSpace ℂ I)).symm
    _ = ‖W t‖ * Real.sqrt (∑ d, ‖∑ c, a c d * cp t c‖ ^ 2) := by
      rw [hvec, norm_smul, EuclideanSpace.norm_eq]
      simp only [PiLp.toLp_apply, norm_mul, hrp, one_mul]
    _ ≤ ‖W t‖ * B := mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)

 theorem finite_dyadic_harmonic_bound (F : Type) [Field F] [NumberField F] :
    ∃ H : ℝ, 0 < H ∧ ∀ (C : ℝ) (u : Finset (Ideal (𝓞 F))), 1 ≤ C →
      (∀ c ∈ u, C ≤ (Ideal.absNorm c : ℝ) ∧ (Ideal.absNorm c : ℝ) < 2 * C) →
      ∑ c ∈ u, (Ideal.absNorm c : ℝ)⁻¹ ≤ H := by
  obtain ⟨K, K', hK, hK', hcount⟩ := ideal_counting_harmonic_bounds F
  refine ⟨2 * K, by positivity, ?_⟩
  intro C u hC hu
  have hc0 : 0 < C := by linarith
  have hne (c) (hc : c ∈ u) : c ≠ ⊥ := by
    intro he
    have h := (hu c hc).1
    simp [he] at h
    linarith
  let f : ↥u → ↥(normBoundedIdeals F (2 * C)) := fun c =>
    ⟨⟨c.val, hne c.val c.property⟩, (hu c.val c.property).2.le⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    exact congrArg (fun x : ↥(normBoundedIdeals F (2 * C)) => x.val.val) he
  haveI := (normBoundedIdeals_finite F (2 * C)).fintype
  have hcard : (u.card : ℝ) ≤ K * (2 * C) := by
    have hn := Fintype.card_le_of_injective f hf
    have hn' : u.card ≤ (normBoundedIdeals F (2 * C)).ncard := by
      rw [Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hn
      exact hn
    have hk := (hcount Set.univ).1 (2 * C) (by linarith)
    simp only [Set.univ_inter] at hk
    exact (Nat.cast_le.mpr hn').trans hk
  calc
    ∑ c ∈ u, (Ideal.absNorm c : ℝ)⁻¹ ≤ ∑ c ∈ u, C⁻¹ := by
      apply Finset.sum_le_sum
      intro c hc
      exact (inv_le_inv₀ (hc0.trans_le (hu c hc).1) hc0).mpr (hu c hc).1
    _ = (u.card : ℝ) * C⁻¹ := by simp
    _ ≤ K * (2 * C) * C⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * K := by field_simp

set_option maxHeartbeats 1000000 in

theorem finite_masked_hgl
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (qS : Ideal (𝓞 F)) (𝓕 : QuadraticHeckeFamily F qS)
    (b : ℝ) (hb : 0 < b) :
    ∃ L : ℝ, 0 < L ∧ ∀ (X Y : ℝ) (u r : Finset (Ideal (𝓞 F)))
      (a ρ : Ideal (𝓞 F) → ℂ), 1 ≤ X → 1 ≤ Y →
      (∀ c ∈ u, Squarefree c ∧ c ⊔ qS = ⊤ ∧ (Ideal.absNorm c : ℝ) ≤ Y) →
      (∀ d ∈ r, Squarefree d ∧ d ⊔ qS = ⊤ ∧ (Ideal.absNorm d : ℝ) ≤ X) →
      (∀ d, ‖ρ d‖ ≤ 1) →
      (∑ d ∈ r, ‖ρ d * ∑ c ∈ u, a c * (𝓕.χ c) d‖ ^ 2) ≤
        L * (X * Y) ^ b * (X + Y) * ∑ c ∈ u, ‖a c‖ ^ 2 := by
  obtain ⟨L, hL, hbound⟩ := rm_hgl_oriented_masked F ζ12 hζ12 qS 𝓕 b hb
  refine ⟨L, hL, ?_⟩
  intro X Y u r a ρ hX hY hu hr hρ
  let z : Ideal (𝓞 F) →₀ ℂ := Finsupp.onFinset u (fun c => if c ∈ u then a c else 0)
    (by intro c hc; by_contra hn; simp [hn] at hc)
  have hz : z.support ⊆ u := Finsupp.support_onFinset_subset
  have hzc : ∀ c ∈ u, z c = a c := by intro c hc; simp [z, hc]
  have he (d) : ∑ c ∈ z.support, z c * (𝓕.χ c) d =
      ∑ c ∈ u, a c * (𝓕.χ c) d := by
    change z.sum (fun c w => w * (𝓕.χ c) d) = _
    rw [Finsupp.sum_of_support_subset z hz]
    · exact Finset.sum_congr rfl (fun c hc => by rw [hzc c hc])
    · intro c; simp
  have hm : ∑ c ∈ z.support, ‖z c‖ ^ 2 = ∑ c ∈ u, ‖a c‖ ^ 2 := by
    change z.sum (fun _ w => ‖w‖ ^ 2) = _
    rw [Finsupp.sum_of_support_subset z hz]
    · exact Finset.sum_congr rfl (fun c hc => by rw [hzc c hc])
    · intro c; simp
  have hb := hbound X Y z (fun d => d ∈ r) ρ hX hY
    (fun c hc => hu c (hz hc)) hρ
  rw [hm] at hb
  simp_rw [he] at hb
  have heq : (∑ᶠ d : Ideal (𝓞 F),
      if Squarefree d ∧ d ⊔ qS = ⊤ ∧ (Ideal.absNorm d : ℝ) ≤ X ∧ d ∈ r then
        ‖ρ d * ∑ c ∈ u, a c * (𝓕.χ c) d‖ ^ 2 else 0) =
      ∑ d ∈ r, ‖ρ d * ∑ c ∈ u, a c * (𝓕.χ c) d‖ ^ 2 := by
    rw [finsum_eq_sum_of_support_subset _ (s := r)]
    · apply Finset.sum_congr rfl
      intro d hd
      have hd' : Squarefree d ∧ d ⊔ qS = ⊤ ∧ (Ideal.absNorm d : ℝ) ≤ X ∧ d ∈ r :=
        ⟨(hr d hd).1, (hr d hd).2.1, (hr d hd).2.2, hd⟩
      rw [if_pos hd']
    · intro d hd
      by_contra hn
      have hn' : d ∉ r := hn
      simp [Function.mem_support, hn'] at hd
  rwa [heq] at hb

open RMFourierProfile
 theorem phased_coeff_sq_le (q : ℝ) (hq : 0 < q) (a p : ℂ)
    (ha : ‖a‖ ≤ 1) (hp : ‖p‖ = 1) :
    ‖a * Complex.ofReal (q ^ (-(1 / 2 : ℝ))) * p‖ ^ 2 ≤ q⁻¹ := by
  rw [norm_mul, norm_mul, hp, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq.le _), mul_pow]
  have he : (q ^ (-(1 / 2 : ℝ))) ^ 2 = q⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num [Real.rpow_neg_one]
  rw [he]
  have ha2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ha2 (by positivity : 0 ≤ q⁻¹)

 theorem sqrt_hgl_dyadic (L H C D b : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hC : 0 < C) (hD : 0 < D) :
    Real.sqrt (L * ((2 * D) * (2 * C)) ^ b * (2 * D + 2 * C) * H) =
      Real.sqrt (L * 4 ^ b * 2 * H) * (D * C) ^ (b / 2) * Real.sqrt (D + C) := by
  have hprod : (2 * D) * (2 * C) = 4 * (D * C) := by ring
  rw [hprod, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : 0 ≤ D*C)]
  have hs : (D * C) ^ b = ((D * C) ^ (b / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ D*C)]
    congr 1
    ring
  rw [hs]
  have he : L * (4 ^ b * ((D * C) ^ (b / 2)) ^ 2) * (2 * D + 2 * C) * H =
      (L * 4 ^ b * 2 * H) * ((D * C) ^ (b / 2)) ^ 2 * (D + C) := by ring
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_sq (Real.rpow_nonneg (by positivity) _)]
set_option maxHeartbeats 1000000 in
theorem finite_row_column_phased_hgl
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (qS : Ideal (𝓞 F)) (𝓕 : QuadraticHeckeFamily F qS)
    (b : ℝ) (hb : 0 < b) :
    ∃ A : ℝ, 0 < A ∧ ∀ (C D t : ℝ) (u r : Finset (Ideal (𝓞 F)))
      (lam ρ : Ideal (𝓞 F) → ℂ), 1 ≤ C → 1 ≤ D →
      (∀ c ∈ u, Squarefree c ∧ c ⊔ qS = ⊤ ∧ C ≤ (Ideal.absNorm c : ℝ) ∧
        (Ideal.absNorm c : ℝ) < 2 * C) →
      (∀ d ∈ r, Squarefree d ∧ d ⊔ qS = ⊤ ∧ D ≤ (Ideal.absNorm d : ℝ) ∧
        (Ideal.absNorm d : ℝ) < 2 * D) →
      (∀ c, ‖lam c‖ ≤ 1) → (∀ d, ‖ρ d‖ ≤ 1) →
      Real.sqrt (∑ d ∈ r, ‖ρ d * ∑ c ∈ u,
        (lam c * Complex.ofReal ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ))) *
          normPhase t ((Ideal.absNorm c : ℝ) / C)) * (𝓕.χ c) d‖ ^ 2) ≤
      A * (D * C) ^ (b / 2) * Real.sqrt (D + C) := by
  obtain ⟨L, hL, hbound⟩ := finite_masked_hgl F ζ12 hζ12 qS 𝓕 b hb
  obtain ⟨H, hH, hmass⟩ := finite_dyadic_harmonic_bound F
  refine ⟨Real.sqrt (L * 4 ^ b * 2 * H), by positivity, ?_⟩
  intro C D t u r lam ρ hC hD hu hr hlam hρ
  have hCp : 0 < C := by linarith
  have hDp : 0 < D := by linarith
  let a : Ideal (𝓞 F) → ℂ := fun c => lam c *
    Complex.ofReal ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ))) *
      normPhase t ((Ideal.absNorm c : ℝ) / C)
  have hms : ∑ c ∈ u, ‖a c‖ ^ 2 ≤ H := by
    apply le_trans _ (hmass C u hC (fun c hc => ⟨(hu c hc).2.2.1, (hu c hc).2.2.2⟩))
    apply Finset.sum_le_sum
    intro c hc
    apply phased_coeff_sq_le _ (hCp.trans_le (hu c hc).2.2.1) _ _ (hlam c)
    exact norm_normPhase _ _ (div_pos (hCp.trans_le (hu c hc).2.2.1) hCp)
  have hbnd := hbound (2 * D) (2 * C) u r a ρ (by linarith) (by linarith)
    (fun c hc => ⟨(hu c hc).1, (hu c hc).2.1, (hu c hc).2.2.2.le⟩)
    (fun d hd => ⟨(hr d hd).1, (hr d hd).2.1, (hr d hd).2.2.2.le⟩) hρ
  have hm' := mul_le_mul_of_nonneg_left hms
    (by positivity : 0 ≤ L * ((2 * D) * (2 * C)) ^ b * (2 * D + 2 * C))
  have hs := Real.sqrt_le_sqrt (hbnd.trans hm')
  rw [sqrt_hgl_dyadic L H C D b hL.le hH.le hCp hDp] at hs
  exact hs

 theorem exists_cutoff : ∃ ξ : ℝ → ℝ, IsCutoff ξ := by
  let l := Real.log 2
  have hl : 0 < l := Real.log_pos (by norm_num)
  let f : ContDiffBump (0 : ℝ) := ⟨3 * l, 4 * l, by positivity, by dsimp [l]; linarith [hl]⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_⟩
  intro x hx
  apply f.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by dsimp [f, l] at *; linarith [hx.1], by dsimp [f, l] at *; linarith [hx.2]⟩

 theorem min_decay_le_one (v : ℝ) (hv : 0 < v) :
    min (v ^ (1 / 8 : ℝ)) (v ^ (-1 : ℝ)) ≤ 1 := by
  by_cases h : v ≤ 1
  · exact (min_le_left _ _).trans (Real.rpow_le_one hv.le h (by norm_num))
  · exact (min_le_right _ _).trans (Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge h) (by norm_num))

set_option maxHeartbeats 1500000 in
theorem finite_profiled_hgl
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (qS : Ideal (𝓞 F)) (𝓕 : QuadraticHeckeFamily F qS)
    (J : Type) [Fintype J] (Φ : J → ℝ → ℂ) (hΦ : UniformLogBounds Φ)
    (b : ℝ) (hb : 0 < b) :
    ∃ A : ℝ, 0 < A ∧ ∀ (j : J) (C D v : ℝ) (u r : Finset (Ideal (𝓞 F)))
      (lam ρ : Ideal (𝓞 F) → ℂ), 1 ≤ C → 1 ≤ D → 0 < v →
      (∀ c ∈ u, Squarefree c ∧ c ⊔ qS = ⊤ ∧ C ≤ (Ideal.absNorm c : ℝ) ∧
        (Ideal.absNorm c : ℝ) < 2 * C) →
      (∀ d ∈ r, Squarefree d ∧ d ⊔ qS = ⊤ ∧ D ≤ (Ideal.absNorm d : ℝ) ∧
        (Ideal.absNorm d : ℝ) < 2 * D) →
      (∀ c, ‖lam c‖ ≤ 1) → (∀ d, ‖ρ d‖ ≤ 1) →
      Real.sqrt (∑ d ∈ r, ‖ρ d * ∑ c ∈ u,
        lam c * Complex.ofReal ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ))) *
          (𝓕.χ c) d * Φ j (v * ((Ideal.absNorm c : ℝ) / C) *
            ((Ideal.absNorm d : ℝ) / D) ^ (-2 : ℤ))‖ ^ 2) ≤
      A * (D * C) ^ (b / 2) * Real.sqrt (D + C) := by
  obtain ⟨ξ, hξ⟩ := exists_cutoff
  obtain ⟨K, hK, hk⟩ := uniform_fourier_l1 ξ hξ Φ hΦ 1 (by norm_num)
  obtain ⟨A, hA, ha⟩ := finite_row_column_phased_hgl F ζ12 hζ12 qS 𝓕 b hb
  refine ⟨K * A, mul_pos hK hA, ?_⟩
  intro j C D v u r lam ρ hC hD hv hu hr hlam hρ
  have hCp : 0 < C := by linarith
  have hDp : 0 < D := by linarith
  let W := FourierTransform.fourier (localizedProfile ξ (Φ j) v)
  let a : ↥u → ↥r → ℂ := fun c d => ρ d *
    (lam c * Complex.ofReal ((Ideal.absNorm c.val : ℝ) ^ (-(1 / 2 : ℝ))) * (𝓕.χ c) d)
  let P : ↥u → ↥r → ℂ := fun c d => Φ j (v * ((Ideal.absNorm c.val : ℝ) / C) *
    ((Ideal.absNorm d.val : ℝ) / D) ^ (-2 : ℤ))
  let cp : ℝ → ↥u → ℂ := fun t c => normPhase t ((Ideal.absNorm c.val : ℝ) / C)
  let rp : ℝ → ↥r → ℂ := fun t d => normPhase (-2 * t) ((Ideal.absNorm d.val : ℝ) / D)
  have hsep (c : ↥u) (d : ↥r) := dyadic_separation ξ hξ Φ hΦ j v C D
    (Ideal.absNorm c.val : ℝ) (Ideal.absNorm d.val : ℝ) hv hCp hDp
    ⟨(hu c c.property).2.2.1, (hu c c.property).2.2.2⟩
    ⟨(hr d d.property).2.2.1, (hr d d.property).2.2.2⟩
  have hp : ∀ c d, P c d = ∫ t, W t * cp t c * rp t d := by
    intro c d
    simpa only [P, W, cp, rp, zpow_neg, zpow_ofNat, div_eq_mul_inv] using (hsep c d).2
  have hpint : ∀ c d, Integrable (fun t => W t * cp t c * rp t d) :=
    fun c d => (hsep c d).1
  have hrp : ∀ t d, ‖rp t d‖ = 1 := by
    intro t d
    exact norm_normPhase _ _ (div_pos (hDp.trans_le (hr d d.property).2.2.1) hDp)
  have hphase : ∀ t, Real.sqrt (∑ d : ↥r, ‖∑ c : ↥u, a c d * cp t c‖ ^ 2) ≤
      A * (D * C) ^ (b / 2) * Real.sqrt (D + C) := by
    intro t
    have he : ∀ d : ↥r, (∑ c : ↥u, a c d * cp t c) = ρ d * ∑ c ∈ u,
        (lam c * Complex.ofReal ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ))) *
          normPhase t ((Ideal.absNorm c : ℝ) / C)) * (𝓕.χ c) d := by
      intro d
      rw [← Finset.sum_coe_sort u, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      dsimp [a, cp]
      ring
    simp_rw [he]
    rw [Finset.sum_coe_sort r (fun d => ‖ρ d * ∑ c ∈ u,
      (lam c * Complex.ofReal ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ))) *
        normPhase t ((Ideal.absNorm c : ℝ) / C)) * (𝓕.χ c) d‖ ^ 2)]
    exact ha C D t u r lam ρ hC hD hu hr hlam hρ
  have hh := finite_separated_sieve a P W cp rp
    (A * (D * C) ^ (b / 2) * Real.sqrt (D + C)) (hk j v hv).2.1 hpint hp hrp hphase
  have he : ∀ d : ↥r, (∑ c : ↥u, a c d * P c d) = ρ d * ∑ c ∈ u,
      lam c * Complex.ofReal ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ))) *
        (𝓕.χ c) d * Φ j (v * ((Ideal.absNorm c : ℝ) / C) *
          ((Ideal.absNorm d.val : ℝ) / D) ^ (-2 : ℤ)) := by
    intro d
    rw [← Finset.sum_coe_sort u, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    dsimp [a, P]
    ring
  simp_rw [he] at hh
  rw [Finset.sum_coe_sort r (fun d => ‖ρ d * ∑ c ∈ u,
    lam c * Complex.ofReal ((Ideal.absNorm c : ℝ) ^ (-(1 / 2 : ℝ))) *
      (𝓕.χ c) d * Φ j (v * ((Ideal.absNorm c : ℝ) / C) *
        ((Ideal.absNorm d : ℝ) / D) ^ (-2 : ℤ))‖ ^ 2)] at hh
  apply hh.trans
  have hw : (∫ t, ‖W t‖) ≤ K :=
    (hk j v hv).2.2.trans (by
      have h := mul_le_mul_of_nonneg_left (min_decay_le_one v hv) hK.le
      rw [mul_one] at h
      exact h)
  calc
    (∫ t, ‖W t‖) * (A * (D * C) ^ (b / 2) * Real.sqrt (D + C)) ≤
      K * (A * (D * C) ^ (b / 2) * Real.sqrt (D + C)) :=
        mul_le_mul_of_nonneg_right hw (by positivity)
    _ = K * A * (D * C) ^ (b / 2) * Real.sqrt (D + C) := by ring

end RMMaskedDyadic

end
end DedekindZetaZeroFree
