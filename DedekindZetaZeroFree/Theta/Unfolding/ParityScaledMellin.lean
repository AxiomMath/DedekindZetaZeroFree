module

public import DedekindZetaZeroFree.Adeles.Lattices.NormalizedRayCosetLattice
public import DedekindZetaZeroFree.Theta.Profiles.RayParityFourierMellin
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.RayLatticePeriodization
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitHalfOpenDomain
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitTorsionFibers

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.ScaledMellin

variable {K : Type} [Field K] [NumberField K]

def integrand (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (q : InfinitePlace K → ℝ) : ℂ :=
  if ∀ v, 0 < q v then
    RayParity.gδ K δ
      (RayParity.Q K q (RayCoset.normalizedEmbedding D α.val)) *
      (RayParity.J K q : ℂ) ^ s
  else 0

private theorem representative_ne_zero (D : RayCoset.Data K) (α : RayCoset.Cx D) :
    (α.val : K) ≠ 0 := by
  intro h
  have := (RayCoset.mem_Cnonzero_iff D α.val).mp α.property
  exact this.2 (RingOfIntegers.coe_injective h)

private theorem normalized_real_coordinate (D : RayCoset.Data K) (α : RayCoset.Cx D)
    (v : RayCoset.RealPlaces K) :
    (Theta.traceToMixed K (RayCoset.normalizedEmbedding D α.val)).1 v =
      RayCoset.normalizationScale D * RayCoset.realEmbedding K v (α.val : K) := by
  simp only [RayCoset.normalizedEmbedding_apply, map_smul, Theta.traceEmbedding,
    ContinuousLinearEquiv.apply_symm_apply, Prod.smul_fst, Pi.smul_apply,
    smul_eq_mul, mixedEmbedding_apply_isReal, RayCoset.realEmbedding]

private theorem normalized_real_ne_zero (D : RayCoset.Data K) (α : RayCoset.Cx D) :
    ∀ v : RayCoset.RealPlaces K,
      (Theta.traceToMixed K (RayCoset.normalizedEmbedding D α.val)).1 v ≠ 0 := by
  intro v
  rw [normalized_real_coordinate]
  exact mul_ne_zero (RayCoset.normalizationScale_pos D).ne'
    ((map_ne_zero _).mpr (representative_ne_zero D α))

private theorem normalized_complex_ne_zero (D : RayCoset.Data K) (α : RayCoset.Cx D) :
    ∀ v : {w : InfinitePlace K // IsComplex w},
      (Theta.traceToMixed K (RayCoset.normalizedEmbedding D α.val)).2 v ≠ 0 := by
  intro v
  simp only [RayCoset.normalizedEmbedding_apply, map_smul, Theta.traceEmbedding,
    ContinuousLinearEquiv.apply_symm_apply, Prod.smul_snd, Pi.smul_apply,
    mixedEmbedding_apply_isComplex]
  exact smul_ne_zero (RayCoset.normalizationScale_pos D).ne'
    ((map_ne_zero _).mpr (representative_ne_zero D α))

private theorem sign_pos_mul (r a : ℝ) (hr : 0 < r) :
    Real.sign (r * a) = Real.sign a := by
  rcases lt_trichotomy a 0 with hn | hz | hp
  · rw [Real.sign_of_neg hn, Real.sign_of_neg (mul_neg_of_pos_of_neg hr hn)]
  · simp [hz]
  · rw [Real.sign_of_pos hp, Real.sign_of_pos (mul_pos hr hp)]

private theorem integrand_ae (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D) (s : ℂ) :
    integrand D δ α s =ᵐ[μ K] fun q =>
      gδ K δ (Q K q (RayCoset.normalizedEmbedding D α.val)) * (J K q : ℂ) ^ s := by
  filter_upwards [ae_positiveShape K] with q hq
  simp [integrand, hq]

theorem integrable (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (integrand D δ α s) (RayParity.μ K) := by
  exact (integrable_gδ_mellin K δ _ (normalized_real_ne_zero D α)
    (normalized_complex_ne_zero D α) s hs).congr (integrand_ae D δ α s).symm

theorem integral (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ q, integrand D δ α s q ∂(RayParity.μ K)) =
      RayParity.κδ K δ s *
        (RayCoset.signδ D δ (RayCoset.orbitMk D α) : ℂ) *
        (RayCoset.normWeight D (RayCoset.orbitMk D α) : ℂ) ^ (-s) := by
  rw [integral_congr_ae (integrand_ae D δ α s),
    integral_gδ_mellin K δ _ (normalized_real_ne_zero D α)
      (normalized_complex_ne_zero D α) s hs,
    RayCoset.normWeight_eq_archimedeanNorm]
  congr 2
  simp only [RayCoset.signδ_orbitMk, RayCoset.representativeSign, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro v hv
  rw [normalized_real_coordinate, sign_pos_mul _ _ (RayCoset.normalizationScale_pos D)]

theorem integrable_norm (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun q => ‖integrand D δ α s q‖) (RayParity.μ K) := by
  exact (integrable D δ α s hs).norm

private theorem normWeight_pos (D : RayCoset.Data K) (α : RayCoset.Cx D) :
    0 < RayCoset.normWeight D (RayCoset.orbitMk D α) := by
  rw [RayCoset.normWeight_orbitMk]
  unfold RayCoset.representativeNormWeight
  apply div_pos
  · apply abs_pos.mpr
    exact_mod_cast (Algebra.norm_eq_zero_iff.not.mpr (representative_ne_zero D α))
  · exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.ideal_ne_bot)

private theorem abs_sign_one (a : ℝ) (ha : a ≠ 0) : |Real.sign a| = 1 := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · simp [Real.sign_of_neg hn]
  · simp [Real.sign_of_pos hp]

private theorem sign_norm_one (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D) :
    ‖(RayCoset.signδ D δ (RayCoset.orbitMk D α) : ℂ)‖ = 1 := by
  simp only [RayCoset.signδ_orbitMk, RayCoset.representativeSign,
    Complex.ofReal_prod, norm_prod, Complex.norm_real, Real.norm_eq_abs]
  apply Finset.prod_eq_one
  intro v hv
  exact abs_sign_one _ ((map_ne_zero _).mpr (representative_ne_zero D α))

private theorem scaled_coordinate (D : RayCoset.Data K) (α : RayCoset.Cx D)
    (q : InfinitePlace K → ℝ) (v : RayCoset.RealPlaces K) :
    Theta.traceRealCoordinateCLM K v (Q K q (RayCoset.normalizedEmbedding D α.val)) =
      q v * (RayCoset.normalizationScale D * RayCoset.realEmbedding K v (α.val : K)) := by
  rw [traceRealCoordinateCLM_eq_traceToMixed]
  simp only [Q, ContinuousLinearEquiv.apply_symm_apply, mixedSpaceOfRealSpace_apply,
    Prod.fst_mul, Pi.mul_apply, normalized_real_coordinate]

private theorem sign_mul_abs (r a : ℝ) (hr : 0 < r) :
    Real.sign a * |r * a| = r * a := by
  rcases lt_trichotomy a 0 with hn | hz | hp
  · rw [Real.sign_of_neg hn, abs_of_neg (mul_neg_of_pos_of_neg hr hn)]
    ring
  · simp [hz]
  · rw [Real.sign_of_pos hp, abs_of_pos (mul_pos hr hp), one_mul]

private theorem gaussian_norm (x : euclidean.mixedSpace K) :
    (‖Theta.latticeGaussian Real.pi x‖ : ℂ) = Theta.latticeGaussian Real.pi x := by
  have he : -(Real.pi : ℂ) * (‖x‖ : ℂ) ^ 2 =
      ((-Real.pi * ‖x‖ ^ 2 : ℝ) : ℂ) := by norm_cast
  rw [Theta.latticeGaussian, he, Complex.norm_exp, Complex.ofReal_re, Complex.ofReal_exp]

private theorem kernel_norm (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    (RayCoset.signδ D δ (RayCoset.orbitMk D α) : ℂ) *
      (‖gδ K δ (Q K q (RayCoset.normalizedEmbedding D α.val))‖ : ℂ) =
      gδ K δ (Q K q (RayCoset.normalizedEmbedding D α.val)) := by
  simp only [gδ, norm_mul, Complex.ofReal_mul, gaussian_norm]
  rw [← mul_assoc]
  congr 1
  simp only [RayCoset.signδ_orbitMk, RayCoset.representativeSign,
    Complex.ofReal_prod, norm_prod, Complex.norm_real, Real.norm_eq_abs,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  rw [scaled_coordinate, ← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc]
  exact sign_mul_abs _ _ (mul_pos (hq v) (RayCoset.normalizationScale_pos D))

private theorem integrand_norm_ae (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D) (s : ℂ) :
    (fun q => (RayCoset.signδ D δ (RayCoset.orbitMk D α) : ℂ) *
      (‖integrand D δ α s q‖ : ℂ)) =ᵐ[μ K] integrand D δ α (s.re : ℂ) := by
  filter_upwards [ae_positiveShape K] with q hq
  have hj : 0 < J K q := Finset.prod_pos fun v hv => pow_pos (hq v) _
  simp only [integrand, if_pos hq, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hj, Complex.ofReal_mul,
    Complex.ofReal_cpow hj.le, ← mul_assoc]
  rw [kernel_norm D δ α q hq]

theorem integral_norm (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ q, ‖integrand D δ α s q‖ ∂(RayParity.μ K)) =
      ‖RayParity.κδ K δ (s.re : ℂ)‖ *
        RayCoset.normWeight D (RayCoset.orbitMk D α) ^ (-s.re) := by
  have he := integral_congr_ae (integrand_norm_ae D δ α s)
  rw [integral_const_mul,
    integral_complex_ofReal (μ := μ K) (f := fun q => ‖integrand D δ α s q‖),
    integral D δ α (s.re : ℂ) hs] at he
  have hn := congrArg norm he
  rw [norm_mul, sign_norm_one D δ α, one_mul,
    Complex.norm_of_nonneg (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)),
    norm_mul, norm_mul, sign_norm_one D δ α, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (normWeight_pos D α)] at hn
  simpa only [Complex.neg_re, Complex.ofReal_re] using hn

end DedekindZetaZeroFree.AbelianQuotient.RayParity.ScaledMellin

end
