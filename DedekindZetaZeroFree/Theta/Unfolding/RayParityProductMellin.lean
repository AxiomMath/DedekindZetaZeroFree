module

public import DedekindZetaZeroFree.Theta.Profiles.RayParityKernels
public import DedekindZetaZeroFree.Nonvanishing.Mellin.RealParityGaussian

@[expose] public section

noncomputable section

open Classical MeasureTheory NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity

def «μ₊» : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity (fun q : ℝ ↦ ENNReal.ofReal q⁻¹)

instance sigmaFinite_positiveHaar : SigmaFinite «μ₊» := by
  unfold «μ₊»
  infer_instance

 theorem ae_positiveHaar_pos : ∀ᵐ q ∂«μ₊», 0 < q := by
  unfold «μ₊»
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ioi)
private theorem multiplicative_density_kernel (f : ℝ → ℂ) (s : ℂ)
    (q : ℝ) (hq : 0 < q) :
    (ENNReal.ofReal q⁻¹).toReal • (f q * (q : ℂ) ^ s) =
      f q * (q : ℂ) ^ (s - 1) := by
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hq.le), Complex.real_smul,
    Complex.ofReal_inv, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hq.ne'),
    Complex.cpow_one]
  ring

theorem integrable_multiplicative_mellin_iff (f : ℝ → ℂ) (s : ℂ) :
    Integrable (fun q : ℝ ↦ f q * (q : ℂ) ^ s) «μ₊» ↔
      IntegrableOn (fun q : ℝ ↦ f q * (q : ℂ) ^ (s - 1)) (Set.Ioi 0) volume := by
  unfold «μ₊» IntegrableOn
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall fun q ↦ ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact multiplicative_density_kernel f s q hq

theorem integral_multiplicative_mellin (f : ℝ → ℂ) (s : ℂ) :
    (∫ q : ℝ, f q * (q : ℂ) ^ s ∂«μ₊») =
      ∫ q : ℝ in Set.Ioi 0, f q * (q : ℂ) ^ (s - 1) := by
  unfold «μ₊»
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun q ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact multiplicative_density_kernel f s q hq

theorem integrable_real_multiplicative_mellin
    (s : ℂ) (hs : 0 < s.re) (a : ℝ) (ha : a ≠ 0) (e : Bool) :
    Integrable (fun q : ℝ ↦
      ((if e then ((q * a : ℝ) : ℂ) else 1) *
        Complex.exp (-((Real.pi * a ^ 2 * q ^ 2 : ℝ) : ℂ))) * (q : ℂ) ^ s)
      «μ₊» := by
  rw [integrable_multiplicative_mellin_iff]
  convert real_parityGaussian_integrableOn s hs a ha e using 1
  ext q
  ring

theorem integral_real_multiplicative_mellin
    (s : ℂ) (hs : 0 < s.re) (a : ℝ) (ha : a ≠ 0) (e : Bool) :
    (∫ q : ℝ,
      ((if e then ((q * a : ℝ) : ℂ) else 1) *
        Complex.exp (-((Real.pi * a ^ 2 * q ^ 2 : ℝ) : ℂ))) * (q : ℂ) ^ s ∂«μ₊») =
      (2 : ℂ)⁻¹ * Complex.Gammaℝ (s + if e then 1 else 0) *
        (if e then (Real.sign a : ℂ) else 1) * ((|a| : ℝ) : ℂ) ^ (-s) := by
  rw [integral_multiplicative_mellin]
  convert real_parityGaussian_mellin s hs a ha e using 1
  congr 1
  ext q
  ring

theorem integrable_complex_multiplicative_mellin
    (s : ℂ) (hs : 0 < s.re) (a : ℝ) (ha : 0 < a) :
    Integrable (fun q : ℝ ↦
      Complex.exp (-((2 * Real.pi * a * q ^ 2 : ℝ) : ℂ)) * (q : ℂ) ^ (2 * s))
      «μ₊» := by
  rw [integrable_multiplicative_mellin_iff]
  convert integrableOn_gaussian_complex_place_mellin s a hs ha using 1
  ext q
  ring

theorem integral_complex_multiplicative_mellin
    (s : ℂ) (hs : 0 < s.re) (a : ℝ) (ha : 0 < a) :
    (∫ q : ℝ, Complex.exp (-((2 * Real.pi * a * q ^ 2 : ℝ) : ℂ)) *
      (q : ℂ) ^ (2 * s) ∂«μ₊») =
      (4 : ℂ)⁻¹ * Complex.Gammaℂ s * (a : ℂ) ^ (-s) := by
  rw [integral_multiplicative_mellin]
  calc
    _ = ∫ q : ℝ in Set.Ioi 0,
        (q : ℂ) ^ (2 * s - 1) *
          Complex.exp (-((2 * Real.pi * a * q ^ 2 : ℝ) : ℂ)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q ↦ mul_comm _ _
    _ = _ := by rw [gaussian_complex_place_mellin s a hs ha]; ring

variable (K : Type) [Field K] [NumberField K]

def μ : Measure (InfinitePlace K → ℝ) :=
  Measure.pi (fun _ : InfinitePlace K ↦ «μ₊»)

 theorem ae_positiveShape (K : Type) [Field K] [NumberField K] :
    ∀ᵐ q ∂μ K, ∀ v, 0 < q v := by
  rw [Filter.eventually_all]
  intro v
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : InfinitePlace K ↦ «μ₊»)).eventually
    ae_positiveHaar_pos

def J (q : InfinitePlace K → ℝ) : ℝ := ∏ v, (q v) ^ v.mult

 theorem J_cpow_eq_prod (K : Type) [Field K] [NumberField K]
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) (s : ℂ) :
    (J K q : ℂ) ^ s = ∏ v, (q v : ℂ) ^ ((v.mult : ℂ) * s) := by
  have hprod : ∀ t : Finset (InfinitePlace K),
      ((∏ v ∈ t, q v ^ v.mult : ℝ) : ℂ) ^ s =
        ∏ v ∈ t, (q v : ℂ) ^ ((v.mult : ℂ) * s) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert v t hv ih =>
      rw [Finset.prod_insert hv, Finset.prod_insert hv,
        Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
          (pow_nonneg (hq v).le _) (Finset.prod_nonneg fun w hw ↦ pow_nonneg (hq w).le _), ih]
      congr 1
      rw [Complex.ofReal_pow, Complex.cpow_nat_mul' (by simp [Complex.arg_ofReal_of_nonneg (hq v).le, Real.pi_pos])
        (by simp [Complex.arg_ofReal_of_nonneg (hq v).le, Real.pi_pos.le])]
  exact hprod Finset.univ

theorem norm_sq_traceToMixed (x : euclidean.mixedSpace K) :
    ‖x‖ ^ 2 = (∑ v : RayCoset.RealPlaces K, ((Theta.traceToMixed K x).1 v) ^ 2) +
      ∑ v : {w : InfinitePlace K // IsComplex w}, 2 * ‖(Theta.traceToMixed K x).2 v‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  change ‖((euclidean.toMixed K x).2 v)‖ ^ 2 = _
  have hh : (euclidean.toMixed K x).2 v =
      Real.sqrt 2 • (Theta.traceToMixed K x).2 v := by
    change _ = Real.sqrt 2 • (Theta.divideBySqrtTwo ((euclidean.toMixed K x).2 v))
    rw [← Theta.divideBySqrtTwo_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [hh, _root_.norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
theorem norm_sq_Q (q : InfinitePlace K → ℝ) (x : euclidean.mixedSpace K) :
    ‖Q K q x‖ ^ 2 =
      (∑ v : RayCoset.RealPlaces K, q v.1 ^ 2 * ((Theta.traceToMixed K x).1 v) ^ 2) +
      ∑ v : {w : InfinitePlace K // IsComplex w},
        2 * q v.1 ^ 2 * ‖(Theta.traceToMixed K x).2 v‖ ^ 2 := by
  rw [norm_sq_traceToMixed]
  simp only [Q, ContinuousLinearEquiv.apply_symm_apply,
    mixedSpaceOfRealSpace_apply, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    exact mul_pow _ _ _
  · apply Finset.sum_congr rfl
    intro v hv
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
theorem gδ_Q_eq_prod (δ : Finset (RayCoset.RealPlaces K))
    (q : InfinitePlace K → ℝ) (x : euclidean.mixedSpace K) :
    gδ K δ (Q K q x) =
      (∏ v : RayCoset.RealPlaces K,
        (if v ∈ δ then ((q v.1 * (Theta.traceToMixed K x).1 v : ℝ) : ℂ) else 1) *
          Complex.exp (-((Real.pi * ((Theta.traceToMixed K x).1 v) ^ 2 * q v.1 ^ 2 : ℝ) : ℂ))) *
      ∏ v : {w : InfinitePlace K // IsComplex w},
        Complex.exp (-((2 * Real.pi * ‖(Theta.traceToMixed K x).2 v‖ ^ 2 * q v.1 ^ 2 : ℝ) : ℂ)) := by
  have hp : (∏ v ∈ δ, (Theta.traceRealCoordinateCLM K v (Q K q x) : ℂ)) =
      ∏ v : RayCoset.RealPlaces K,
        (if v ∈ δ then ((q v.1 * (Theta.traceToMixed K x).1 v : ℝ) : ℂ) else 1) := by
    simp only [traceRealCoordinateCLM_eq_traceToMixed, Q,
      ContinuousLinearEquiv.apply_symm_apply, mixedSpaceOfRealSpace_apply,
      Prod.fst_mul, Pi.mul_apply]
    rw [Fintype.prod_ite_mem]
  rw [gδ, hp, Theta.latticeGaussian, ← Complex.ofReal_pow,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, norm_sq_Q,
    Finset.prod_mul_distrib]
  have hr : (-((Real.pi *
      ((∑ v : RayCoset.RealPlaces K, q v.1 ^ 2 * ((Theta.traceToMixed K x).1 v) ^ 2) +
       ∑ v : {w : InfinitePlace K // IsComplex w},
         2 * q v.1 ^ 2 * ‖(Theta.traceToMixed K x).2 v‖ ^ 2) : ℝ) : ℂ)) =
      (∑ v : RayCoset.RealPlaces K,
         -((Real.pi * ((Theta.traceToMixed K x).1 v) ^ 2 * q v.1 ^ 2 : ℝ) : ℂ)) +
      ∑ v : {w : InfinitePlace K // IsComplex w},
         -((2 * Real.pi * ‖(Theta.traceToMixed K x).2 v‖ ^ 2 * q v.1 ^ 2 : ℝ) : ℂ) := by
    simp only [mul_add, Finset.mul_sum, Complex.ofReal_add,
      Complex.ofReal_sum, neg_add_rev, Finset.sum_neg_distrib]
    rw [add_comm]
    congr 1 <;> congr 1 <;> apply Finset.sum_congr rfl <;> intro v hv <;> congr 1 <;> ring
  rw [neg_mul, Complex.ofReal_neg, hr, Complex.exp_add, Complex.exp_sum, Complex.exp_sum]
  ring

def «N∞» (x : euclidean.mixedSpace K) : ℝ :=
  mixedEmbedding.norm (Theta.traceToMixed K x)

 theorem NInfty_eq_prod (x : euclidean.mixedSpace K) :
    «N∞» K x =
      (∏ v : RayCoset.RealPlaces K, |(Theta.traceToMixed K x).1 v|) *
      ∏ v : {w : InfinitePlace K // IsComplex w}, ‖(Theta.traceToMixed K x).2 v‖ ^ 2 := by
  rw [«N∞», mixedEmbedding.norm_apply, ← Fintype.prod_subtype_mul_prod_subtype
    (p := fun v : InfinitePlace K ↦ IsReal v)]
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    rw [normAtPlace_apply_of_isReal v.prop, mult_isReal v, pow_one, Real.norm_eq_abs]
  · rw [← Equiv.prod_comp (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex)).symm]
    apply Finset.prod_congr rfl
    intro v hv
    change normAtPlace v.1 (Theta.traceToMixed K x) ^ v.1.mult = _
    rw [normAtPlace_apply_of_isComplex v.prop, mult_isComplex v]
 theorem cpow_prod_nonneg {ι : Type*} (t : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ t, 0 ≤ f i) (s : ℂ) :
    ((∏ i ∈ t, f i : ℝ) : ℂ) ^ s = ∏ i ∈ t, (f i : ℂ) ^ s := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert v t hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf v (by simp))
        (Finset.prod_nonneg fun w hw ↦ hf w (by simp [hw])),
      ih (fun w hw ↦ hf w (by simp [hw]))]
 theorem NInfty_cpow_eq_prod (x : euclidean.mixedSpace K) (s : ℂ) :
    («N∞» K x : ℂ) ^ (-s) =
      (∏ v : RayCoset.RealPlaces K, ((|(Theta.traceToMixed K x).1 v| : ℝ) : ℂ) ^ (-s)) *
      ∏ v : {w : InfinitePlace K // IsComplex w},
        ((‖(Theta.traceToMixed K x).2 v‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  rw [NInfty_eq_prod, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg
      (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _)
      (Finset.prod_nonneg fun _ _ ↦ sq_nonneg _),
    cpow_prod_nonneg _ _ (fun _ _ ↦ abs_nonneg _),
    cpow_prod_nonneg _ _ (fun _ _ ↦ sq_nonneg _)]

theorem collect_place_mellin_factors (δ : Finset (RayCoset.RealPlaces K))
    (x : euclidean.mixedSpace K) (s : ℂ) :
    (∏ v : RayCoset.RealPlaces K,
      (2 : ℂ)⁻¹ * Complex.Gammaℝ (s + if v ∈ δ then 1 else 0) *
        (if v ∈ δ then (Real.sign ((Theta.traceToMixed K x).1 v) : ℂ) else 1) *
          ((|(Theta.traceToMixed K x).1 v| : ℝ) : ℂ) ^ (-s)) *
      (∏ v : {w : InfinitePlace K // IsComplex w},
        (4 : ℂ)⁻¹ * Complex.Gammaℂ s *
          ((‖(Theta.traceToMixed K x).2 v‖ ^ 2 : ℝ) : ℂ) ^ (-s)) =
      κδ K δ s *
        (∏ v ∈ δ, (Real.sign ((Theta.traceToMixed K x).1 v) : ℂ)) *
        («N∞» K x : ℂ) ^ (-s) := by
  rw [κδ, NInfty_cpow_eq_prod]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.prod_ite_mem, inv_pow]
  change ((2 : ℂ) ^ nrRealPlaces K)⁻¹ *
      (∏ v : RayCoset.RealPlaces K, Complex.Gammaℝ (s + if v ∈ δ then 1 else 0)) *
      (∏ v ∈ δ, (Real.sign ((Theta.traceToMixed K x).1 v) : ℂ)) *
      (∏ v : RayCoset.RealPlaces K, ((|(Theta.traceToMixed K x).1 v| : ℝ) : ℂ) ^ (-s)) *
      (((4 : ℂ) ^ nrComplexPlaces K)⁻¹ * Complex.Gammaℂ s ^ nrComplexPlaces K *
        ∏ v : {w : InfinitePlace K // IsComplex w},
          ((‖(Theta.traceToMixed K x).2 v‖ ^ 2 : ℝ) : ℂ) ^ (-s)) = _
  ring

def localKernel (δ : Finset (RayCoset.RealPlaces K))
    (x : euclidean.mixedSpace K) (s : ℂ) (v : InfinitePlace K) (q : ℝ) : ℂ :=
  if h : IsReal v then
    ((if (⟨v,h⟩ : RayCoset.RealPlaces K) ∈ δ then
        ((q * (Theta.traceToMixed K x).1 ⟨v,h⟩ : ℝ) : ℂ) else 1) *
      Complex.exp (-((Real.pi * ((Theta.traceToMixed K x).1 ⟨v,h⟩) ^ 2 * q ^ 2 : ℝ) : ℂ))) * (q : ℂ) ^ s
  else
    Complex.exp (-((2 * Real.pi * ‖(Theta.traceToMixed K x).2 ⟨v,not_isReal_iff_isComplex.mp h⟩‖ ^ 2 * q ^ 2 : ℝ) : ℂ)) * (q : ℂ) ^ (2 * s)
 theorem prod_places_split (f : InfinitePlace K → ℂ) :
    (∏ v, f v) = (∏ v : RayCoset.RealPlaces K, f v.1) *
      ∏ v : {w : InfinitePlace K // IsComplex w}, f v.1 := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun v : InfinitePlace K ↦ IsReal v)]
  congr 1
  exact (Equiv.prod_comp (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex)).symm _).symm
 theorem kernel_eq_local_prod (δ : Finset (RayCoset.RealPlaces K))
    (x : euclidean.mixedSpace K) (s : ℂ) (q : InfinitePlace K → ℝ)
    (hq : ∀ v, 0 < q v) :
    gδ K δ (Q K q x) * (J K q : ℂ) ^ s = ∏ v, localKernel K δ x s v (q v) := by
  rw [gδ_Q_eq_prod, J_cpow_eq_prod K q hq, prod_places_split, prod_places_split]
  simp only [localKernel, dif_pos (Subtype.prop _), mult_isReal, Nat.cast_one, one_mul,
    dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _)), mult_isComplex, Nat.cast_ofNat,
    Finset.prod_mul_distrib]
  ring
 theorem integrable_localKernel (δ : Finset (RayCoset.RealPlaces K))
    (x : euclidean.mixedSpace K)
    (hr : ∀ v : RayCoset.RealPlaces K, (Theta.traceToMixed K x).1 v ≠ 0)
    (hc : ∀ v : {w : InfinitePlace K // IsComplex w}, (Theta.traceToMixed K x).2 v ≠ 0)
    (s : ℂ) (hs : 0 < s.re) (v : InfinitePlace K) :
    Integrable (localKernel K δ x s v) «μ₊» := by
  change Integrable (fun q ↦ localKernel K δ x s v q) «μ₊»
  by_cases hv : IsReal v
  · simpa [localKernel, hv] using
      integrable_real_multiplicative_mellin s hs ((Theta.traceToMixed K x).1 ⟨v,hv⟩)
        (hr ⟨v,hv⟩) (decide ((⟨v,hv⟩ : RayCoset.RealPlaces K) ∈ δ))
  · simpa [localKernel, hv] using
      integrable_complex_multiplicative_mellin s hs
        (‖(Theta.traceToMixed K x).2 ⟨v,not_isReal_iff_isComplex.mp hv⟩‖ ^ 2)
        (sq_pos_of_pos (norm_pos_iff.mpr (hc _)))

theorem integrable_gδ_mellin (δ : Finset (RayCoset.RealPlaces K))
    (x : euclidean.mixedSpace K)
    (hxReal : ∀ v : RayCoset.RealPlaces K, (Theta.traceToMixed K x).1 v ≠ 0)
    (hxComplex : ∀ v : {w : InfinitePlace K // IsComplex w},
      (Theta.traceToMixed K x).2 v ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun q ↦ gδ K δ (Q K q x) * (J K q : ℂ) ^ s) (μ K) := by
  refine (Integrable.fintype_prod_dep (integrable_localKernel K δ x hxReal hxComplex s hs)).congr ?_
  filter_upwards [ae_positiveShape K] with q hq
  exact (kernel_eq_local_prod K δ x s q hq).symm

theorem integral_gδ_mellin (δ : Finset (RayCoset.RealPlaces K))
    (x : euclidean.mixedSpace K)
    (hxReal : ∀ v : RayCoset.RealPlaces K, (Theta.traceToMixed K x).1 v ≠ 0)
    (hxComplex : ∀ v : {w : InfinitePlace K // IsComplex w},
      (Theta.traceToMixed K x).2 v ≠ 0)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ q, gδ K δ (Q K q x) * (J K q : ℂ) ^ s ∂μ K) =
      κδ K δ s *
        (∏ v ∈ δ, (Real.sign ((Theta.traceToMixed K x).1 v) : ℂ)) *
        («N∞» K x : ℂ) ^ (-s) := by
  calc
    _ = ∫ q, ∏ v, localKernel K δ x s v (q v) ∂μ K := by
      apply integral_congr_ae
      filter_upwards [ae_positiveShape K] with q hq
      exact kernel_eq_local_prod K δ x s q hq
    _ = ∏ v, ∫ q, localKernel K δ x s v q ∂«μ₊» :=
      integral_fintype_prod_eq_prod _
    _ = _ := by
      rw [prod_places_split]
      rw [← collect_place_mellin_factors K δ x s]
      congr 1
      · apply Finset.prod_congr rfl
        intro v hv
        simpa only [localKernel, dif_pos v.prop, decide_eq_true_eq] using
          integral_real_multiplicative_mellin s hs ((Theta.traceToMixed K x).1 v)
            (hxReal v) (decide (v ∈ δ))
      · apply Finset.prod_congr rfl
        intro v hv
        simpa only [localKernel, dif_neg (not_isReal_iff_isComplex.mpr v.prop)] using
          integral_complex_multiplicative_mellin s hs
            (‖(Theta.traceToMixed K x).2 v‖ ^ 2)
            (sq_pos_of_pos (norm_pos_iff.mpr (hxComplex v)))

end DedekindZetaZeroFree.AbelianQuotient.RayParity

end
