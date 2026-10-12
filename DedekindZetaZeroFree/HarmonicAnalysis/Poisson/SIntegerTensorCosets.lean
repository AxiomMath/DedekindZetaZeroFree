module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.TracePhaseScalarAction
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.Lattices.EuclideanSummation
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SIntegers.BallVolumesAndCovolumes

@[expose] public section

noncomputable section
open scoped Classical nonZeroDivisors SchwartzMap FourierTransform
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.ScaleShift

 theorem adapter_mem_dual (F : Type) [Field F] [NumberField F]
    (I : PoissonArch.NonzeroFractionalIdeal F) (y : PoissonArch.Space F) :
    PoissonArch.traceAdapter F y ∈ PoissonArch.dualLattice (PoissonArch.idealLattice F I) ↔
      y ∈ PoissonArch.idealTraceDual F I := by
  rw [PoissonArch.dualLattice, LinearMap.BilinForm.mem_dualSubmodule]
  simp only [innerₗ_apply_apply, Submodule.mem_one]
  constructor
  · intro h x hx
    have hh := h (PoissonArch.minkowskiEmbedding F x)
      ((PoissonArch.mem_idealLattice F I _).mpr ⟨x, hx, rfl⟩)
    change ∃ n : ℤ, (n : ℝ) = _ at hh
    change ∃ n : ℤ, (n : ℝ) = _
    simpa only [real_inner_comm, ← PoissonArch.tracePairing_eq_inner] using hh
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := (PoissonArch.mem_idealLattice F I z).mp hz
    change ∃ n : ℤ, (n : ℝ) = _
    simpa only [real_inner_comm, ← PoissonArch.tracePairing_eq_inner] using (show ∃ n : ℤ, (n : ℝ) = PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F x) y from h x hx)

 def adapterDualEquiv (F : Type) [Field F] [NumberField F]
    (I : PoissonArch.NonzeroFractionalIdeal F) :
    PoissonArch.idealLattice F (PoissonArch.codifferentIdeal F * I⁻¹) ≃
      PoissonArch.dualLattice (PoissonArch.idealLattice F I) where
  toFun y := ⟨PoissonArch.traceAdapter F y, (adapter_mem_dual F I y).mpr
    (by rw [PoissonArch.idealTraceDual_eq]; exact y.property)⟩
  invFun w := ⟨(PoissonArch.traceAdapter F).symm w, by
    change (PoissonArch.traceAdapter F).symm (w : PoissonArch.Space F) ∈
      (PoissonArch.idealLattice F (PoissonArch.codifferentIdeal F * I⁻¹) :
        Set (PoissonArch.Space F))
    rw [← PoissonArch.idealTraceDual_eq, ← adapter_mem_dual]
    simpa using w.property⟩
  left_inv y := by ext; simp
  right_inv w := by ext; simp

theorem trace_ideal_coset_poisson (F : Type) [Field F] [NumberField F]
    (I : PoissonArch.NonzeroFractionalIdeal F)
    (f : 𝓢(PoissonArch.Space F, ℂ)) (a : PoissonArch.Space F) :
    (∑' x : PoissonArch.idealLattice F I, f (a + x)) =
      (PoissonArch.covolume F I : ℂ)⁻¹ *
        ∑' y : PoissonArch.idealLattice F (PoissonArch.codifferentIdeal F * I⁻¹),
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            (PoissonArch.tracePairing F a y : ℂ)) *
              PoissonArch.traceFourier F f y := by
  have h := PoissonArch.poisson_summation_lattice_shift (PoissonArch.idealLattice F I) f a
  rw [← (adapterDualEquiv F I).tsum_eq] at h
  have hphase (y : PoissonArch.Space F) :
      ((𝐞 (inner ℝ a (PoissonArch.traceAdapter F y)) : Circle) : ℂ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (PoissonArch.tracePairing F a y : ℂ)) := by
    rw [← PoissonArch.tracePairing_eq_inner, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  simp only [adapterDualEquiv, Equiv.coe_fn_mk, Subtype.coe_mk, Circle.smul_def, hphase] at h
  rw [h, PoissonArch.covolume_eq_haarScalar_mul_euclidean]
  simp only [Complex.ofReal_mul, mul_inv_rev]
  simp_rw [PoissonArch.traceFourier_eq_euclidean]
  simp only [SchwartzMap.fourier_coe, smul_eq_mul]
  simp_rw [mul_left_comm _ (PoissonArch.haarScalar F : ℂ), tsum_mul_left]
  have hn : (PoissonArch.haarScalar F : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (PoissonArch.haarScalar_pos F)
  field_simp

theorem local_valuation_ball_fourier (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : AddChar (v.adicCompletion F) Circle)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hconductor : ∀ y, (∀ z : v.adicCompletion F, ‖z‖ ≤ 1 → e (z * y) = 1) ↔
      ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v)
    (hnorm : μ {z | ‖z‖ ≤ 1} = ENNReal.ofReal (integerVolume F v))
    (k : ℤ) (b y : v.adicCompletion F) :
    (∫ z, (if ‖z - b‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k) then (1 : ℂ) else 0) *
      (e (-z * y) : ℂ) ∂μ) =
    (e (-b * y) : ℂ) *
      (if ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (k + differentExponent F v) then
        (((v.asIdeal.absNorm : ℝ) ^ (-k) * integerVolume F v : ℝ) : ℂ) else 0) := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-k))
  have han : a ≠ 0 := by
    intro hz
    rw [hz, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  have hna : ‖a‖ = (v.asIdeal.absNorm : ℝ) ^ (-k) := by
    rw [FinitePlace.norm_def, ha, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
      WithZero.log_exp, NNReal.coe_zpow]
    rfl
  have hq : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v))
  have heq : (v.asIdeal.absNorm : ℝ) ^ (-k) * ‖y‖ ≤
      (v.asIdeal.absNorm : ℝ) ^ differentExponent F v ↔
      ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (k + differentExponent F v) := by
    rw [mul_comm ((v.asIdeal.absNorm : ℝ) ^ (-k)), ← le_div_iff₀ (zpow_pos hq _), ← zpow_sub₀ (ne_of_gt hq)]
    congr 1 <;> ring_nf
  have h := Covolume.finite_translated_ball_fourier F v e μ hconductor a han b y
  change (∫ z, (if ‖z - b‖ ≤ ‖a‖ then (1 : ℂ) else 0) * (e (-z * y) : ℂ) ∂μ) =
    (e (-b * y) : ℂ) * (if ‖a‖ * ‖y‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExponent F v
      then ((μ {z | ‖z‖ ≤ ‖a‖}).toReal : ℂ) else 0) at h
  rw [hna] at h
  simp only [heq] at h
  rw [h]
  congr 1
  split_ifs
  · congr 1
    exact local_ball_volume F v μ hnorm k
  · rfl

theorem tensor_ball_fourier (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (hconductor : TraceConductor F S e) (hnorm : LocalNormalization F S μ)
    (f : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (b : PoissonFinite.Space F S)
    (y : Space F S) :
    fourierIntegral F S e μ
      (tensorFunction F S f (fun v z =>
        if ‖z - b v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0)) y =
      PoissonArch.traceFourier F f y.1 * (∏ v : S, (e v (-b v * y.2 v) : ℂ)) *
        (if y.2 ∈ finiteBall F S (fun v => -k v - differentExponent F v.val) then
          (finiteBallVolume F S k μ : ℂ) else 0) := by
  change fourierIntegral F S e μ (fun z => f z.1 * ∏ v : S,
    if ‖z.2 v - b v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0) y = _
  rw [fourierIntegral_tensor_factorization F S e μ hnorm (f : PoissonArch.Space F → ℂ)
    (fun v z => if ‖z - b v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0) y]
  simp_rw [local_valuation_ball_fourier F _ _ _ (hconductor _) (hnorm _)]
  rw [Finset.prod_mul_distrib]
  have hm : (finiteBallVolume F S k μ : ℂ) =
      ∏ v : S, (((v.val.asIdeal.absNorm : ℝ) ^ (-k v) * integerVolume F v.val : ℝ) : ℂ) := by
    rw [finiteBallVolume_eq_prod F S k μ hnorm]
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro v _
    exact congrArg (fun r : ℝ => (r : ℂ)) (local_ball_volume F v.val (μ v) (hnorm v) (k v))
  have hi : (∏ v : S, if ‖y.2 v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^
      (k v + differentExponent F v.val) then
        (((v.val.asIdeal.absNorm : ℝ) ^ (-k v) * integerVolume F v.val : ℝ) : ℂ) else 0) =
      if y.2 ∈ finiteBall F S (fun v => -k v - differentExponent F v.val) then
        (finiteBallVolume F S k μ : ℂ) else 0 := by
    have he (v : S) : -(-k v - differentExponent F v.val) = k v + differentExponent F v.val := by omega
    simp only [finiteBall, Set.mem_setOf_eq, he]
    by_cases hh : ∀ v : S, ‖y.2 v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (k v + differentExponent F v.val)
    · simp only [hh, if_true]
      simp only [implies_true, ↓reduceIte]
      exact hm.symm
    · rw [if_neg hh]
      push Not at hh
      obtain ⟨v, hv⟩ := hh
      exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg (not_le.mpr hv))
  rw [hi]
  ring

 def kernel (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y : Space F S) : ℂ :=
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
        ∏ v : S, (e v (-x.2 v * y.2 v) : ℂ)
private theorem kernel_norm (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y : Space F S) : ‖kernel F S e x y‖ = 1 := by
  simp only [kernel, norm_mul, norm_prod, Circle.norm_coe, Finset.prod_const_one, mul_one]
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]
private theorem kernel_continuous (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (y : Space F S) :
    Continuous (fun x => kernel F S e x y) := by
  unfold kernel
  apply Continuous.mul
  · rw [show (fun x : Space F S => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F x.1 y.1 : ℂ))) = fun x =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (inner ℝ x.1 (PoissonArch.traceAdapter F y.1) : ℂ)) by
        funext x; rw [PoissonArch.tracePairing_eq_inner]]
    fun_prop
  · apply continuous_finset_prod
    intro v _
    exact continuous_subtype_val.comp ((he v).comp
      ((continuous_apply v |>.comp continuous_snd).neg.mul continuous_const))

theorem fourierIntegral_finset_sum (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    (he : ∀ v, Continuous (e v))
    {ι : Type*} (T : Finset ι) (c : ι → ℂ) (f : ι → Space F S → ℂ)
    (hf : ∀ i ∈ T, Integrable (f i) (productMeasure F S μ)) (y : Space F S) :
    fourierIntegral F S e μ (fun x => ∑ i ∈ T, c i * f i x) y =
      ∑ i ∈ T, c i * fourierIntegral F S e μ (f i) y := by
  letI : MeasurableSpace (Space F S) := Prod.instMeasurableSpace
  have hker : AEStronglyMeasurable (fun x => kernel F S e x y)
      (productMeasure F S μ) := (kernel_continuous F S e he y).aestronglyMeasurable
  have hi (i : ι) (h : i ∈ T) :
      Integrable (fun x => c i * (f i x * kernel F S e x y)) (productMeasure F S μ) :=
    ((hf i h).mul_bdd hker (Filter.Eventually.of_forall fun x => le_of_eq
      (kernel_norm F S e x y))).const_mul _
  have hk (g : Space F S → ℂ) : fourierIntegral F S e μ g y =
      ∫ x, g x * kernel F S e x y ∂productMeasure F S μ := by
    unfold fourierIntegral kernel
    simp only [mul_assoc]
  simp only [hk]
  simp_rw [Finset.sum_mul]
  simp_rw [mul_assoc]
  rw [integral_finset_sum T hi]
  simp_rw [integral_const_mul]

theorem poisson_finset_sum (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    (he : ∀ v, Continuous (e v))
    {ι : Type*} (T : Finset ι) (c : ι → ℂ) (f : ι → Space F S → ℂ)
    (hf : ∀ i ∈ T, Integrable (f i) (productMeasure F S μ))
    (hs : ∀ i ∈ T, Summable (fun m : lattice F S 1 => f i m))
    (hfs : ∀ i ∈ T, Summable (fun h : lattice F S 1 => fourierIntegral F S e μ (f i) h))
    (hp : ∀ i ∈ T, (∑' m : lattice F S 1, f i m) =
      ∑' h : lattice F S 1, fourierIntegral F S e μ (f i) h) :
    (∑' m : lattice F S 1, ∑ i ∈ T, c i * f i m) =
      ∑' h : lattice F S 1,
        fourierIntegral F S e μ (fun x => ∑ i ∈ T, c i * f i x) h := by
  simp_rw [fourierIntegral_finset_sum F S e μ he T c f hf]
  rw [Summable.tsum_finsetSum (fun i hi => (hs i hi).mul_left (c i)),
    Summable.tsum_finsetSum (fun i hi => (hfs i hi).mul_left (c i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tsum_mul_left, tsum_mul_left, hp i hi]

theorem tensor_uniform_ball_expansion (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (f : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) :
    ∃ (k : S → ℤ) (n : ℕ) (b : Fin n → PoissonFinite.Space F S) (c : Fin n → ℂ),
      ∀ x : Space F S, tensorFunction F S f φ x =
        ∑ j, c j * (f x.1 *
          (if ∀ v : S, (Valued.v (x.2 v - b j v) : WithZero (Multiplicative ℤ)) ≤
            WithZero.exp (-k v) then (1 : ℂ) else 0)) := by
  let ψ : PoissonFinite.Space F S → ℂ := fun x => ∏ v : S, φ v (x v)
  have hl : IsLocallyConstant ψ := by
    apply (IsLocallyConstant.iff_eventually_eq ψ).mpr
    intro x
    have h : ∀ v : S, ∀ᶠ y in nhds x, φ v (y v) = φ v (x v) := by
      intro v
      exact ((hlocal v).comp_continuous (continuous_apply v)).eventually_eq x
    filter_upwards [Filter.eventually_all.mpr h] with y hy
    exact Finset.prod_congr rfl (fun v _ => hy v)
  have hc : HasCompactSupport ψ := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_pi_infinite (fun v : S => (hsupport v).isCompact))
    intro x hx v
    apply subset_tsupport
    exact (Finset.prod_ne_zero_iff.mp hx) v (Finset.mem_univ v)
  obtain ⟨k, n, b, c, hψ⟩ := PoissonFinite.BallExpansion.exists_uniform_ball_expansion F S ψ hl hc
  refine ⟨k, n, b, c, fun x => ?_⟩
  change f x.1 * ψ x.2 = _
  rw [hψ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem ideal_le_of_counts (F : Type) [Field F] [NumberField F]
    (I J : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v, FractionalIdeal.count F v J ≤ FractionalIdeal.count F v I) : I ≤ J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hJ]
  have hs (A : FractionalIdeal (RingOfIntegers F)⁰ F) :
      Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (RingOfIntegers F) =>
        (FractionalIdeal.coeIdeal v.asIdeal : FractionalIdeal (RingOfIntegers F)⁰ F) ^
          FractionalIdeal.count F v A) := by
    apply Set.Finite.subset (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors A))
    intro v hv hz
    exact hv (by simp [hz])
  apply finprod_le_finprod (hs I) (hs J)
  intro v
  apply zpow_le_zpow_right_of_le_one₀ _ _ (h v)
  · exact bot_lt_iff_ne_bot.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  · exact FractionalIdeal.coeIdeal_le_one

theorem fractionalIdeal_mem_iff_valuations (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0) (x : F) :
    x ∈ I ↔ ∀ v, v.valuation F x ≤ WithZero.exp (-FractionalIdeal.count F v I) := by
  by_cases hx : x = 0
  · subst x
    simp only [FractionalIdeal.zero_mem, true_iff]
    intro v
    simp
  let P := FractionalIdeal.spanSingleton (RingOfIntegers F)⁰ x
  have hP : P ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
  have hv (v : HeightOneSpectrum (RingOfIntegers F)) :
      v.valuation F x = WithZero.exp (-FractionalIdeal.count F v P) :=
    SUnitGroup.valuation_eq_exp_neg_count (Units.mk0 x hx) v
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  constructor
  · intro h v
    rw [hv, WithZero.exp_le_exp, neg_le_neg_iff]
    exact FractionalIdeal.count_mono F v hP h
  · intro h
    apply ideal_le_of_counts F P I hP hI
    intro v
    simpa only [hv, WithZero.exp_le_exp, neg_le_neg_iff] using h v

theorem count_ballFractionalIdeal (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : S → ℤ)
    (w : HeightOneSpectrum (RingOfIntegers F)) :
    FractionalIdeal.count F w (ballFractionalIdeal F S k) =
      if h : w ∈ S then k ⟨w, h⟩ else 0 := by
  rw [ballFractionalIdeal, FractionalIdeal.count_prod]
  · simp only [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal,
      mul_ite, mul_one, mul_zero]
    by_cases h : w ∈ S
    · rw [dif_pos h]
      have he (v : S) : (v.val = w) ↔ v = ⟨w, h⟩ := by simp [Subtype.ext_iff]
      simp_rw [he]
      simp
    · rw [dif_neg h]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg]
      intro he
      exact h (he ▸ v.property)
  · intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot)

theorem ballFractionalIdeal_le_sIntegers (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : S → ℤ)
    {x : F} (hx : x ∈ ballFractionalIdeal F S k) :
    x ∈ (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F := by
  intro w hw
  have h := (fractionalIdeal_mem_iff_valuations F _ (ballFractionalIdeal_ne_zero F S k) x).mp hx w
  have hw' : w ∉ S := hw
  simpa [count_ballFractionalIdeal, hw'] using h

theorem dual_ballFractionalIdeal (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (k : S → ℤ) :
    (PoissonArch.codifferentIdeal F : FractionalIdeal (RingOfIntegers F)⁰ F) *
        (ballFractionalIdeal F S k)⁻¹ =
      ballFractionalIdeal F S (fun v => -k v - differentExponent F v.val) := by
  have hD : differentIdeal ℤ (RingOfIntegers F) ≠ 0 := differentIdeal_ne_bot
  have hd : ∀ v, v ∉ S → differentExponent F v = 0 := by
    intro v hv
    rw [differentExponent, FractionalIdeal.count_coe F v hD]
    norm_cast
    by_contra hc
    exact hv (hS v ((Associates.count_ne_zero_iff_dvd hD v.irreducible).mp hc))
  have hfactor : (∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal) ^
      differentExponent F v.val) =
      (FractionalIdeal.coeIdeal (differentIdeal ℤ (RingOfIntegers F)) :
        FractionalIdeal (RingOfIntegers F)⁰ F) := by
    rw [show (∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal :
      FractionalIdeal (RingOfIntegers F)⁰ F) ^ differentExponent F v.val) =
      ∏ v ∈ S, (FractionalIdeal.coeIdeal v.asIdeal :
      FractionalIdeal (RingOfIntegers F)⁰ F) ^ differentExponent F v from
      Finset.prod_coe_sort S (fun v => (FractionalIdeal.coeIdeal v.asIdeal :
        FractionalIdeal (RingOfIntegers F)⁰ F) ^ differentExponent F v)]
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hD)]
    symm
    apply finprod_eq_finsetProd_of_mulSupport_subset
    intro v hv
    by_contra h
    exact hv (by change (_ : FractionalIdeal (RingOfIntegers F)⁰ F) ^ differentExponent F v = 1; rw [hd v h, zpow_zero])
  rw [PoissonArch.codifferentIdeal_eq_inv_different, ← hfactor]
  simp only [ballFractionalIdeal, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot)]
  congr 1
  ring

 theorem embedding_injective (F : Type) [Field F] [NumberField F] :
    Function.Injective (PoissonArch.minkowskiEmbedding F) :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).symm.injective.comp
    (NumberField.mixedEmbedding_injective F)

theorem norm_ball_iff_valuation (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (k : ℤ) (x : v.adicCompletion F) :
    ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k) ↔ Valued.v x ≤ WithZero.exp (-k) := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-k))
  have hna : ‖a‖ = (v.asIdeal.absNorm : ℝ) ^ (-k) := by
    rw [FinitePlace.norm_def, ha, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
      WithZero.log_exp, NNReal.coe_zpow]
    rfl
  rw [← hna, ← ha]
  exact Valued.toNormedField.norm_le_iff

theorem finiteBall_diagonal_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : S → ℤ)
    (m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F) :
    PoissonFinite.diagonal F S (m : F) ∈ finiteBall F S k ↔
      (m : F) ∈ ballFractionalIdeal F S k := by
  rw [fractionalIdeal_mem_iff_valuations F _ (ballFractionalIdeal_ne_zero F S k)]
  simp only [finiteBall, PoissonFinite.diagonal, Set.mem_setOf_eq,
    norm_ball_iff_valuation, HeightOneSpectrum.adicCompletion.valued_coe]
  have hv (v : S) : (Valued.v (FinitePlace.embedding v.val (m : F)) :
      WithZero (Multiplicative ℤ)) = v.val.valuation F (m : F) :=
    HeightOneSpectrum.adicCompletion.valued_coe _ _ _
  simp_rw [hv]
  constructor
  · intro h w
    by_cases hw : w ∈ S
    · simpa [count_ballFractionalIdeal, hw] using h ⟨w, hw⟩
    · have hh := m.property w hw
      simpa [count_ballFractionalIdeal, hw] using hh
  · intro h v
    simpa [count_ballFractionalIdeal, v.property] using h v.val

def diagonalLatticeEquiv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F ≃ lattice F S 1 :=
  Equiv.ofBijective (fun m => ⟨diagonalHom F S (m : F), by
    change ∃ x : F, x ∈ (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F ∧
      diagonalHom F S (1 * x) = diagonalHom F S (m : F)
    exact ⟨m, m.property, by rw [one_mul]⟩⟩) (by
    constructor
    · intro m n h
      apply Subtype.ext
      apply embedding_injective F
      exact congrArg (fun z : lattice F S 1 => (z : Space F S).1) h
    · intro m
      obtain ⟨x, hx, he⟩ := m.property
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      change diagonalHom F S (1 * x) = (m : Space F S) at he
      simpa only [one_mul] using he)

def idealEmbeddingEquiv (F : Type) [Field F] [NumberField F]
    (I : PoissonArch.NonzeroFractionalIdeal F) :
    {x : F // x ∈ (I : FractionalIdeal (RingOfIntegers F)⁰ F)} ≃ PoissonArch.idealLattice F I :=
  Equiv.ofBijective (fun x => ⟨PoissonArch.minkowskiEmbedding F x,
    (PoissonArch.mem_idealLattice F I _).mpr ⟨x, x.property, rfl⟩⟩) (by
    constructor
    · intro x y h
      exact Subtype.ext (embedding_injective F (congrArg Subtype.val h))
    · intro x
      obtain ⟨a, ha, he⟩ := (PoissonArch.mem_idealLattice F I x).mp x.property
      exact ⟨⟨a, ha⟩, Subtype.ext he⟩)

def idealCosetEquiv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : S → ℤ)
    (t : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F) :
    {x : F // x ∈ ballFractionalIdeal F S k} ≃
      {m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F //
        (m : F) - (t : F) ∈ ballFractionalIdeal F S k} where
  toFun x := ⟨⟨(t : F) + (x : F), (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F |>.add_mem
    t.property (ballFractionalIdeal_le_sIntegers F S k x.property)⟩, by simpa using x.property⟩
  invFun m := ⟨(m : F) - (t : F), m.property⟩
  left_inv x := by ext; simp
  right_inv m := by ext; simp

 abbrev R (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F

theorem tsum_ideal_coset (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : S → ℤ)
    (t : R F S) (f : F → ℂ) :
    (∑' m : R F S, f m * (if (m : F) - (t : F) ∈ ballFractionalIdeal F S k then 1 else 0)) =
      ∑' x : {x : F // x ∈ ballFractionalIdeal F S k}, f ((t : F) + (x : F)) := by
  let A := {m : R F S | (m : F) - (t : F) ∈ ballFractionalIdeal F S k}
  have ht := tsum_subtype A (fun m : R F S => f m)
  simp only [Set.indicator_apply, A, Set.mem_setOf_eq] at ht
  have he := (idealCosetEquiv F S k t).tsum_eq (fun m : A => f m.val)
  change (∑' x : {x : F // x ∈ ballFractionalIdeal F S k}, f ((t : F) + (x : F))) = _ at he
  rw [he]
  change _ = ∑' x : A, f x.val
  rw [tsum_subtype A (fun m : R F S => f m)]
  apply tsum_congr
  intro m
  split_ifs with hm <;> simp [A, hm]

theorem trace_field_coset_poisson (F : Type) [Field F] [NumberField F]
    (I : PoissonArch.NonzeroFractionalIdeal F)
    (f : 𝓢(PoissonArch.Space F, ℂ)) (a : PoissonArch.Space F) :
    (∑' x : {x : F // x ∈ (I : FractionalIdeal (RingOfIntegers F)⁰ F)},
      f (a + PoissonArch.minkowskiEmbedding F x)) =
    (PoissonArch.covolume F I : ℂ)⁻¹ *
      ∑' y : {y : F // y ∈ ((PoissonArch.codifferentIdeal F * I⁻¹) :
          FractionalIdeal (RingOfIntegers F)⁰ F)},
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (PoissonArch.tracePairing F a (PoissonArch.minkowskiEmbedding F y) : ℂ)) *
            PoissonArch.traceFourier F f (PoissonArch.minkowskiEmbedding F y) := by
  have h := trace_ideal_coset_poisson F I f a
  rw [← (idealEmbeddingEquiv F I).tsum_eq,
    ← (idealEmbeddingEquiv F (PoissonArch.codifferentIdeal F * I⁻¹)).tsum_eq] at h
  exact h

theorem rawPhase_diagonal_mul (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle) (a b : F) :
    rawPhase F S e (diagonalHom F S a) (diagonalHom F S b) =
      rawPhase F S e (diagonalHom F S (a*b)) (diagonalHom F S 1) := by
  unfold rawPhase
  congr 1
  · congr 1
    congr 1
    change (PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F a)
      (PoissonArch.minkowskiEmbedding F b) : ℂ) =
      (PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F (a*b))
        (PoissonArch.minkowskiEmbedding F 1) : ℂ)
    simp [PoissonArch.tracePairing, PoissonArch.minkowskiEmbedding, mixedEmbedding,
      map_mul, map_one]
  · apply Finset.prod_congr rfl
    intro v _
    congr 2
    change algebraMap F (v.val.adicCompletion F) a * algebraMap F (v.val.adicCompletion F) b =
      algebraMap F (v.val.adicCompletion F) (a*b) * algebraMap F (v.val.adicCompletion F) 1
    simp

 abbrev RR (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F

theorem diagonal_phase_cancel (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (hd : ∀ r : sIntegerRing F S,
      rawPhase F S e (diagonalHom F S (r : F)) (diagonalHom F S 1) = 1)
    (t m : RR F S) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F t)
        (PoissonArch.minkowskiEmbedding F m) : ℂ)) =
      ∏ v : S, (e v (-FinitePlace.embedding v.val (t : F) * FinitePlace.embedding v.val (m : F)) : ℂ) := by
  have h := hd (t*m)
  change rawPhase F S e (diagonalHom F S ((t : F)*(m : F))) (diagonalHom F S 1) = 1 at h
  rw [← rawPhase_diagonal_mul F S e (t : F) (m : F)] at h
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    (PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F t)
      (PoissonArch.minkowskiEmbedding F m) : ℂ)) *
      (∏ v : S, (e v (FinitePlace.embedding v.val (t : F) * FinitePlace.embedding v.val (m : F)) : ℂ)) = 1 at h
  simp_rw [neg_mul, AddChar.map_neg_eq_inv, Circle.coe_inv]
  rw [Finset.prod_inv_distrib]
  exact eq_inv_of_mul_eq_one_left h

theorem ball_trace_covolume_inv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (k : S → ℤ) (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ) :
    (PoissonArch.covolume F (Units.mk0 (ballFractionalIdeal F S k)
      (ballFractionalIdeal_ne_zero F S k)) : ℂ)⁻¹ = (finiteBallVolume F S k μ : ℂ) := by
  have h := (ball_measure_balance F S hS k μ hnorm).2.2.2
  rw [ballArchCovolume, ballArchLattice_eq] at h
  simpa only [PoissonArch.covolume, Complex.ofReal_inv] using
    (congrArg (fun r : ℝ => (r : ℂ)) h).symm

theorem centered_ball_poisson (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F)) [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (hconductor : TraceConductor F S e) (hnorm : LocalNormalization F S μ)
    (hd : ∀ r : sIntegerRing F S,
      rawPhase F S e (diagonalHom F S (r : F)) (diagonalHom F S 1) = 1)
    (f : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (t : RR F S) :
    (∑' m : lattice F S 1, tensorFunction F S f (fun v z =>
      if ‖z - FinitePlace.embedding v.val (t : F)‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0) m) =
    ∑' m : lattice F S 1, fourierIntegral F S e μ
      (tensorFunction F S f (fun v z =>
      if ‖z - FinitePlace.embedding v.val (t : F)‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0)) m := by
  let I : PoissonArch.NonzeroFractionalIdeal F := Units.mk0 (ballFractionalIdeal F S k)
    (ballFractionalIdeal_ne_zero F S k)
  let l : S → ℤ := fun v => -k v - differentExponent F v.val
  have hJ : ((PoissonArch.codifferentIdeal F * I⁻¹) : FractionalIdeal (RingOfIntegers F)⁰ F) =
      ballFractionalIdeal F S l := by
    simpa [I, l] using dual_ballFractionalIdeal F S hS k
  have hb (m : RR F S) : (∀ v : S, ‖FinitePlace.embedding v.val (m : F) -
      FinitePlace.embedding v.val (t : F)‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)) ↔
      (m : F) - (t : F) ∈ ballFractionalIdeal F S k := by
    simpa only [PoissonFinite.diagonal, finiteBall, Set.mem_setOf_eq, map_sub,
      Subalgebra.coe_sub] using finiteBall_diagonal_mem F S k (m-t)
  rw [← (diagonalLatticeEquiv F S).tsum_eq,
    ← (diagonalLatticeEquiv F S).tsum_eq]
  have horig (m : RR F S) : tensorFunction F S f (fun v z =>
      if ‖z - FinitePlace.embedding v.val (t : F)‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0)
      (diagonalLatticeEquiv F S m) =
      f (PoissonArch.minkowskiEmbedding F m) * (if (m : F) - (t : F) ∈ ballFractionalIdeal F S k then 1 else 0) := by
    change f (PoissonArch.minkowskiEmbedding F m) * (∏ v : S,
      if ‖FinitePlace.embedding v.val (m : F) - FinitePlace.embedding v.val (t : F)‖ ≤
        (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then (1 : ℂ) else 0) = _
    rw [Finset.prod_ite_zero]
    simp only [Finset.prod_const_one, Finset.mem_univ, forall_const, hb]
  simp_rw [horig]
  rw [tsum_ideal_coset F S k t (fun x => f (PoissonArch.minkowskiEmbedding F x))]
  have hP := trace_field_coset_poisson F I f (PoissonArch.minkowskiEmbedding F t)
  simp only [← map_add] at hP
  change (∑' x : {x : F // x ∈ ballFractionalIdeal F S k},
    f (PoissonArch.minkowskiEmbedding F ((t : F) + (x : F)))) = _ at hP
  rw [hP, ball_trace_covolume_inv F S hS k μ hnorm]
  simp_rw [tensor_ball_fourier F S e μ hconductor hnorm]

  change (finiteBallVolume F S k μ : ℂ) *
    (∑' y : {y : F // y ∈ ((PoissonArch.codifferentIdeal F * I⁻¹) :
        FractionalIdeal (RingOfIntegers F)⁰ F)},
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F t)
          (PoissonArch.minkowskiEmbedding F y) : ℂ)) *
        PoissonArch.traceFourier F f (PoissonArch.minkowskiEmbedding F y)) =
    ∑' m : RR F S,
      (PoissonArch.traceFourier F f (PoissonArch.minkowskiEmbedding F m) *
        ∏ v : S, (e v (-FinitePlace.embedding v.val (t : F) * FinitePlace.embedding v.val (m : F)) : ℂ)) *
        (if PoissonFinite.diagonal F S m ∈ finiteBall F S l then
          (finiteBallVolume F S k μ : ℂ) else 0)
  rw [hJ]
  simp_rw [finiteBall_diagonal_mem F S l, ← diagonal_phase_cancel F S e hd t]
  let g : F → ℂ := fun m =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F t)
        (PoissonArch.minkowskiEmbedding F m) : ℂ)) *
      PoissonArch.traceFourier F f (PoissonArch.minkowskiEmbedding F m)
  have hg (m : RR F S) :
      (PoissonArch.traceFourier F f (PoissonArch.minkowskiEmbedding F m) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F t)
            (PoissonArch.minkowskiEmbedding F m) : ℂ))) *
        (if (m : F) ∈ ballFractionalIdeal F S l then (finiteBallVolume F S k μ : ℂ) else 0) =
      (finiteBallVolume F S k μ : ℂ) *
        (g m * (if (m : F) - (0 : F) ∈ ballFractionalIdeal F S l then 1 else 0)) := by
    simp only [sub_zero]
    split_ifs <;> simp [g] <;> ring
  simp_rw [hg]
  rw [tsum_mul_left]
  congr 1
  simpa only [Subalgebra.coe_zero, zero_add] using (tsum_ideal_coset F S l 0 g).symm

theorem local_ball_test (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (k : ℤ) (b : v.adicCompletion F) :
    IsLocallyConstant (fun z => if ‖z-b‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k) then (1 : ℂ) else 0) ∧
    HasCompactSupport (fun z => if ‖z-b‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k) then (1 : ℂ) else 0) := by
  have hq : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast
    (lt_trans Nat.zero_lt_one (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v))
  have hp := zpow_pos hq (-k)
  have he : {z : v.adicCompletion F | ‖z-b‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)} =
      Metric.closedBall b ((v.asIdeal.absNorm : ℝ) ^ (-k)) := by ext z; simp [dist_eq_norm]
  constructor
  · apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    by_cases hz : ‖z-b‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)
    · have hn : {w : v.adicCompletion F | ‖w-b‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)} ∈ nhds z := by
        rw [he]
        exact (IsUltrametricDist.isOpen_closedBall b (ne_of_gt hp)).mem_nhds (by simpa [dist_eq_norm] using hz)
      filter_upwards [hn] with w hw
      simp only [hw, hz, if_true, if_false]
    · have hn : {w : v.adicCompletion F | ¬ ‖w-b‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)} ∈ nhds z := by
        exact (isClosed_le (continuous_id.sub continuous_const |>.norm) continuous_const).isOpen_compl.mem_nhds hz
      filter_upwards [hn] with w hw
      simp only [hw, hz, if_true, if_false]
  · apply HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall b ((v.asIdeal.absNorm : ℝ) ^ (-k)))
      (isCompact_closedBall _ _)
    intro z hz
    have hh : ‖z-b‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k) := by
      by_contra h
      exact hz (if_neg h)
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hh

theorem traceConductor_nontrivial (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (hc : TraceConductor F S e) : ∀ v, ∃ x, e v x ≠ 1 := by
  intro v
  by_contra h
  push Not at h
  have hh : ∀ y : v.val.adicCompletion F, ‖y‖ ≤
      (v.val.asIdeal.absNorm : ℝ) ^ differentExponent F v.val := fun y =>
    (hc v y).mp (fun z _ => h _)

  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v.val
    (WithZero.exp (differentExponent F v.val + 1))
  have hna : ‖a‖ = (v.val.asIdeal.absNorm : ℝ) ^ (differentExponent F v.val + 1) := by
    rw [FinitePlace.norm_def, ha, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
      WithZero.log_exp, NNReal.coe_zpow]
    rfl
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by exact_mod_cast
    NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v.val
  have hp := zpow_pos (lt_trans zero_lt_one hq) (differentExponent F v.val)
  have hl := hh a
  rw [hna, zpow_add₀ (ne_of_gt (lt_trans zero_lt_one hq)), zpow_one] at hl
  nlinarith

theorem exists_rational_ball_center (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : S → ℤ)
    (b : PoissonFinite.Space F S) :
    ∃ t : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F,
      ∀ v : S, ∀ z : v.val.adicCompletion F,
        (‖z - b v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)) ↔
          (‖z - FinitePlace.embedding v.val (t : F)‖ ≤
            (v.val.asIdeal.absNorm : ℝ) ^ (-k v)) := by
  obtain ⟨t, ht⟩ := PoissonFinite.BallExpansion.valuation_ball_fiber_eq_ideal_coset F S k b
  have hc := (ht t).mpr (by simp only [sub_self]; exact FractionalIdeal.zero_mem _)
  refine ⟨t, fun v z => ?_⟩
  rw [norm_ball_iff_valuation, norm_ball_iff_valuation]
  constructor
  · intro hz
    have he : z - FinitePlace.embedding v.val (t : F) =
        (z - b v) - (FinitePlace.embedding v.val (t : F) - b v) := by ring
    rw [he]
    exact Valuation.map_sub_le _ hz (hc v)
  · intro hz
    have he : z - b v = (z - FinitePlace.embedding v.val (t : F)) +
        (FinitePlace.embedding v.val (t : F) - b v) := by ring
    rw [he]
    exact Valuation.map_add_le _ hz (hc v)

theorem translated_ball_poisson (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F)) [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (hconductor : TraceConductor F S e) (hnorm : LocalNormalization F S μ)
    (hd : ∀ r : sIntegerRing F S,
      rawPhase F S e (diagonalHom F S (r : F)) (diagonalHom F S 1) = 1)
    (f : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (b : PoissonFinite.Space F S) :
    (∑' m : lattice F S 1, tensorFunction F S f (fun v z =>
      if ‖z - b v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0) m) =
    ∑' m : lattice F S 1, fourierIntegral F S e μ
      (tensorFunction F S f (fun v z =>
      if ‖z - b v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0)) m := by
  obtain ⟨t, ht⟩ := exists_rational_ball_center F S k b
  have he : (fun v : S => fun z : v.val.adicCompletion F =>
      if ‖z - b v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then (1 : ℂ) else 0) =
      fun v : S => fun z : v.val.adicCompletion F =>
        if ‖z - FinitePlace.embedding v.val (t : F)‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0 := by
    funext v z
    simp only [ht]
  rw [he]
  exact centered_ball_poisson F S hS e μ hconductor hnorm hd f k t

theorem tensor_ball_expansion (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (f : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) :
    ∃ (k : S → ℤ) (n : ℕ) (b : Fin n → PoissonFinite.Space F S) (c : Fin n → ℂ),
      ∀ x : Space F S, tensorFunction F S f φ x =
        ∑ j, c j * tensorFunction F S f (fun v z =>
          if ‖z-b j v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0) x := by
  obtain ⟨k, n, b, c, hexp⟩ := tensor_uniform_ball_expansion F S f φ hlocal hsupport
  refine ⟨k, n, b, c, fun x => ?_⟩
  rw [hexp x]
  apply Finset.sum_congr rfl
  intro j _
  simp only [tensorFunction, norm_ball_iff_valuation, Finset.prod_ite_zero,
    Finset.prod_const_one, Finset.mem_univ, forall_const]

theorem normalized_tensor_poisson
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (hS : ContainsDifferent F S)
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v))
    (hconductor : TraceConductor F S e)
    (hnorm : LocalNormalization F S μ)
    (hdiagonal : ∀ r : sIntegerRing F S,
      rawPhase F S e (diagonalHom F S (r : F)) (diagonalHom F S 1) = 1)
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) :
    (∑' m : lattice F S 1, tensorFunction F S fArch φ m) =
      ∑' h : lattice F S 1,
        fourierIntegral F S e μ (tensorFunction F S fArch φ) h := by
  obtain ⟨k, n, b, c, hexp⟩ := tensor_ball_expansion F S fArch φ hlocal hsupport
  let ψ (j : Fin n) (v : S) (z : v.val.adicCompletion F) : ℂ :=
    if ‖z-b j v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0
  let g (j : Fin n) : Space F S → ℂ := tensorFunction F S fArch (ψ j)
  have htest (j : Fin n) (v : S) : IsLocallyConstant (ψ j v) ∧ HasCompactSupport (ψ j v) :=
    local_ball_test F v.val (k v) (b j v)
  have hg (j : Fin n) : Integrable (g j) (productMeasure F S μ) :=
    tensorFunction_integrable F S μ fArch (ψ j) (fun v => (htest j v).1) (fun v => (htest j v).2)
  have hs (j : Fin n) : Summable (fun m : lattice F S 1 => g j m) :=
    (summable_norm_tensorFunction_lattice F S fArch (ψ j) (fun v => (htest j v).1)
      (fun v => (htest j v).2) 1 one_ne_zero).of_norm
  have hfs (j : Fin n) : Summable (fun h : lattice F S 1 => fourierIntegral F S e μ (g j) h) :=
    by
      have h := (summable_norm_fourierIntegral_tensorFunction_lattice F S e μ he
        (traceConductor_nontrivial F S e hconductor) fArch (ψ j)
        (fun v => (htest j v).1) (fun v => (htest j v).2) 1 one_ne_zero).of_norm
      change Summable (fun h : lattice F S ((1 : F)⁻¹) =>
        fourierIntegral F S e μ (g j) h) at h
      have hone : ((1 : F)⁻¹) = 1 := inv_one
      rw [hone] at h
      exact h
  have hp (j : Fin n) : (∑' m : lattice F S 1, g j m) =
      ∑' h : lattice F S 1, fourierIntegral F S e μ (g j) h :=
    translated_ball_poisson F S hS e μ hconductor hnorm hdiagonal fArch k (b j)
  have heq : tensorFunction F S fArch φ = fun x => ∑ j : Fin n, c j * g j x := by
    funext x
    exact hexp x
  rw [heq]
  exact poisson_finset_sum F S e μ he Finset.univ c g
    (fun j _ => hg j) (fun j _ => hs j) (fun j _ => hfs j) (fun j _ => hp j)

end DedekindZetaZeroFree.PoissonS.ScaleShift

end
