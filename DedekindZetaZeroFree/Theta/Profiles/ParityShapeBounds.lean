module

public import DedekindZetaZeroFree.Theta.Profiles.RayParityKernels
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.RayLatticePeriodization
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitHalfOpenDomain
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitTorsionFibers

@[expose] public section

noncomputable section

open Classical NumberField
open NumberField.mixedEmbedding
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree

variable (K : Type) [Field K] [NumberField K]

private theorem parityContinuous (δ : Finset (RayCoset.RealPlaces K)) :
    Continuous (RayParity.gδ K δ) := by
  unfold RayParity.gδ Theta.latticeGaussian
  fun_prop

private theorem parityPolynomialBound (δ : Finset (RayCoset.RealPlaces K)) (y : euclidean.mixedSpace K) :
 ‖RayParity.gδ K δ y‖ ≤ (1 + ‖y‖) ^ δ.card * Real.exp (-Real.pi * ‖y‖ ^ 2) := by
  rw [RayParity.gδ, norm_mul, Theta.norm_latticeGaussian]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [norm_prod]
  calc
    _ ≤ ∏ v ∈ δ, (1 + ‖y‖) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v hv => by
      rw [Complex.norm_real, Real.norm_eq_abs, Theta.traceRealCoordinateCLM_apply]
      have hb := PiLp.norm_apply_le (Theta.traceCoordinates K y) (Sum.inl v)
      rw [LinearIsometryEquiv.norm_map] at hb
      exact hb.trans (by linarith [norm_nonneg y]))
    _ = _ := by simp

private theorem parityScaleRadial (q : NumberField.InfinitePlace K → ℝ) (x : euclidean.mixedSpace K) (r : ℝ) :
 RayParity.Q K (fun v => r * q v) x = r • RayParity.Q K q x := by
  unfold RayParity.Q
  have he : (fun v => r * q v) = r • q := rfl
  rw [he, map_smul, smul_mul_assoc, map_smul]
private theorem parityCompactLower (S : Set (RayCoset.logHyperplane K)) (hS : IsCompact S) :
 ∃ m : ℝ, 0 < m ∧ ∀ h ∈ S, ∀ x : euclidean.mixedSpace K,
   m * ‖x‖ ≤ ‖RayParity.Q K (fun v => Real.exp (h.val v)) x‖ := by
  let T := S ×ˢ Metric.sphere (0 : euclidean.mixedSpace K) 1
  have hT : IsCompact T := hS.prod (isCompact_sphere 0 1)
  have hc : Continuous (fun hx : RayCoset.logHyperplane K × euclidean.mixedSpace K =>
      ‖RayParity.Q K (fun v => Real.exp (hx.1.val v)) hx.2‖) := by
    apply Continuous.norm
    unfold RayParity.Q
    apply (Theta.traceToMixed K).symm.continuous.comp
    apply Continuous.mul
    · apply mixedSpaceOfRealSpace.continuous.comp
      apply continuous_pi
      intro v
      exact Real.continuous_exp.comp ((continuous_apply v).comp (continuous_subtype_val.comp continuous_fst))
    · exact (Theta.traceToMixed K).continuous.comp continuous_snd
  obtain ⟨m, hm, hb⟩ := hT.exists_forall_le' hc.continuousOn (a := 0) (by
    rintro ⟨h,x⟩ ⟨hh,hx⟩
    apply norm_pos_iff.mpr
    rw [RayParity.Q_eq_traceRadialScale K _ (fun v => (Real.exp_pos _).ne')]
    intro hz
    have hx0 : x = 0 := (Theta.traceRadialScale K (fun v => Real.exp (h.val v))
      (fun v => (Real.exp_pos _).ne')).injective (by simpa using hz)
    simpa [hx0] using hx)
  refine ⟨m, hm, ?_⟩
  intro h hh x
  by_cases hx : x = 0
  · simp [hx, RayParity.Q]
  · have hunit : (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : euclidean.mixedSpace K) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using (norm_smul_inv_norm (𝕜 := ℝ) hx)
    have hb' := hb (h, (‖x‖⁻¹ : ℝ) • x) ⟨hh, hunit⟩
    have he : RayParity.Q K (fun v => Real.exp (h.val v)) ((‖x‖⁻¹ : ℝ) • x) =
       (‖x‖⁻¹ : ℝ) • RayParity.Q K (fun v => Real.exp (h.val v)) x := by
      unfold RayParity.Q
      rw [map_smul, mul_smul_comm, map_smul]
    rw [he, _root_.norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))] at hb'
    have := mul_le_mul_of_nonneg_left hb' (norm_nonneg x)
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    field_simp at this
    nlinarith

theorem thetaParityShapeBounds
    (δ : Finset (RayCoset.RealPlaces K))
    (S : Set (RayCoset.logHyperplane K)) (hS : IsCompact S) :
    ∃ P c : ℝ, 0 < P ∧ 0 < c ∧
      ∀ t : ℝ, 0 < t → ∀ h ∈ S, ∀ x : euclidean.mixedSpace K,
        ‖RayParity.gδ K δ
          (RayParity.Q K
            (fun v => t ^ (1 / (Module.finrank ℚ K : ℝ)) * Real.exp (h.val v)) x)‖ ≤
          P * Real.exp (-c * t ^ (2 / (Module.finrank ℚ K : ℝ)) * ‖x‖ ^ 2) ∧
        ‖RayParity.gδ K δ
          (RayParity.Q K
            (fun v => t ^ (1 / (Module.finrank ℚ K : ℝ)) * Real.exp ((-h).val v)) x)‖ ≤
          P * Real.exp (-c * t ^ (2 / (Module.finrank ℚ K : ℝ)) * ‖x‖ ^ 2) := by
  let T := S ∪ Neg.neg '' S
  have hT : IsCompact T := hS.union (hS.image continuous_neg)
  obtain ⟨m, hm, hb⟩ := parityCompactLower K T hT
  obtain ⟨P, hP, hpoly⟩ := thetaPolynomialGaussianAbsorption δ.card Real.pi Real.pi_pos
  refine ⟨P, (Real.pi / 2) * m ^ 2, hP, mul_pos (by positivity) (sq_pos_of_pos hm), ?_⟩
  have hbound : ∀ t : ℝ, 0 < t → ∀ h ∈ T, ∀ x : euclidean.mixedSpace K,
        ‖RayParity.gδ K δ
          (RayParity.Q K
            (fun v => t ^ (1 / (Module.finrank ℚ K : ℝ)) * Real.exp (h.val v)) x)‖ ≤
          P * Real.exp (-((Real.pi / 2) * m ^ 2) * t ^ (2 / (Module.finrank ℚ K : ℝ)) * ‖x‖ ^ 2) := by
    intro t ht h hh x
    let r := t ^ (1 / (Module.finrank ℚ K : ℝ))
    let y := RayParity.Q K (fun v => t ^ (1 / (Module.finrank ℚ K : ℝ)) * Real.exp (h.val v)) x
    have hr : 0 < r := Real.rpow_pos_of_pos ht _
    have hy : y = r • RayParity.Q K (fun v => Real.exp (h.val v)) x := parityScaleRadial K _ _ _
    have hlower : r * (m * ‖x‖) ≤ ‖y‖ := by
      rw [hy, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left (hb h hh x) hr.le
    have hsquare : m ^ 2 * r ^ 2 * ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      have : (r * (m * ‖x‖)) ^ 2 ≤ ‖y‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlower 2
      nlinarith
    have hrpow : r ^ 2 = t ^ (2 / (Module.finrank ℚ K : ℝ)) := by
      dsimp [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1
      ring
    calc
      _ ≤ (1 + ‖y‖) ^ δ.card * Real.exp (-Real.pi * ‖y‖ ^ 2) := parityPolynomialBound K δ y
      _ ≤ P * Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2) := hpoly _ (norm_nonneg y)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hP.le
        apply Real.exp_le_exp.mpr
        rw [← hrpow]
        nlinarith [Real.pi_pos]
  intro t ht h hh x
  exact ⟨hbound t ht h (Or.inl hh) x,
    hbound t ht (-h) (Or.inr ⟨h, hh, rfl⟩) x⟩

theorem continuousOn_thetaParityShape
    (δ : Finset (RayCoset.RealPlaces K)) :
    ContinuousOn
      (fun thx : ℝ × (RayCoset.logHyperplane K × euclidean.mixedSpace K) =>
        RayParity.gδ K δ
          (RayParity.Q K
            (fun v => thx.1 ^ (1 / (Module.finrank ℚ K : ℝ)) *
              Real.exp (thx.2.1.val v)) thx.2.2))
      {thx | 0 < thx.1} := by
  apply (parityContinuous K δ).comp_continuousOn
  unfold RayParity.Q
  apply (Theta.traceToMixed K).symm.continuous.comp_continuousOn
  apply ContinuousOn.mul
  · apply mixedSpaceOfRealSpace.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro v
    apply ContinuousOn.mul
    · exact continuousOn_fst.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    · exact (Real.continuous_exp.comp ((continuous_apply v).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).continuousOn
  · exact (Theta.traceToMixed K).continuous.comp_continuousOn
      (continuous_snd.comp continuous_snd).continuousOn

theorem continuousOn_thetaParityShape_neg
    (δ : Finset (RayCoset.RealPlaces K)) :
    ContinuousOn
      (fun thx : ℝ × (RayCoset.logHyperplane K × euclidean.mixedSpace K) =>
        RayParity.gδ K δ
          (RayParity.Q K
            (fun v => thx.1 ^ (1 / (Module.finrank ℚ K : ℝ)) *
              Real.exp ((-thx.2.1).val v)) thx.2.2))
      {thx | 0 < thx.1} := by
  apply (parityContinuous K δ).comp_continuousOn
  unfold RayParity.Q
  apply (Theta.traceToMixed K).symm.continuous.comp_continuousOn
  apply ContinuousOn.mul
  · apply mixedSpaceOfRealSpace.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro v
    apply ContinuousOn.mul
    · exact continuousOn_fst.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    · exact (Real.continuous_exp.comp ((continuous_apply v).comp
        (continuous_subtype_val.comp (continuous_neg.comp (continuous_fst.comp continuous_snd))))).continuousOn
  · exact (Theta.traceToMixed K).continuous.comp_continuousOn
      (continuous_snd.comp continuous_snd).continuousOn

theorem thetaParity_zero (δ : Finset (RayCoset.RealPlaces K)) :
    RayParity.gδ K δ (0 : euclidean.mixedSpace K) =
      if δ = ∅ then (1 : ℂ) else 0 := by
  by_cases h : δ = ∅
  · simp [h, RayParity.gδ, Theta.latticeGaussian]
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr h
    simp only [h, if_false, RayParity.gδ, map_zero, Complex.ofReal_zero]
    rw [Finset.prod_eq_zero hv (by simp), zero_mul]

end DedekindZetaZeroFree

end
