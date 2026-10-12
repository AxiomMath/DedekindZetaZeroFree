module

public import DedekindZetaZeroFree.Theta.Profiles.RayClasses.AffineResiduePackets

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open Classical NumberField DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

def principalNormalizedLogVector (γ : Fˣ) : InfinitePlace F → ℝ :=
  fun v => Real.log (v (γ : F)) -
    Real.log |(Algebra.norm ℚ (γ : F) : ℝ)| / (Module.finrank ℚ F : ℝ)

theorem principalNormalizedLogVector_mem
    (hF : NumberField.IsTotallyComplex F) (γ : Fˣ) :
    principalNormalizedLogVector γ ∈ RayCoset.logHyperplane F := by
  classical
  have hp := InfinitePlace.prod_eq_abs_norm (γ : F)
  have hl := congrArg Real.log hp
  rw [Real.log_prod (fun v _ => pow_ne_zero _
    (InfinitePlace.pos_iff.mpr (Units.ne_zero γ)).ne')] at hl
  simp only [Real.log_pow] at hl
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hm : (∑ v : InfinitePlace F, (v.mult : ℝ)) = (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast (InfinitePlace.sum_mult_eq (K := F))
  change RayCoset.weightedLogSum F (principalNormalizedLogVector γ) = 0
  simp only [RayCoset.weightedLogSum, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, principalNormalizedLogVector, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hm]
  push_cast at hl
  rw [← hl]
  field_simp
  ring

def principalNormalizedLogShift (hF : NumberField.IsTotallyComplex F) (γ : Fˣ) :
    RayCoset.logHyperplane F :=
  ⟨principalNormalizedLogVector γ, principalNormalizedLogVector_mem hF γ⟩

theorem affineResidueScale_principal_mul
    (hF : NumberField.IsTotallyComplex F)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F)) (v : InfinitePlace F) :
    affineResidueScale J * v (γ : F) =
      affineResidueScale I * Real.exp ((principalNormalizedLogShift hF γ : InfinitePlace F → ℝ) v) := by
  have hi : 0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _)
      (Ne.symm (fun h => Units.ne_zero I (FractionalIdeal.absNorm_eq_zero_iff.mp h)))
  have hg : 0 < |(Algebra.norm ℚ (γ : F) : ℝ)| := by
    exact abs_pos.mpr (by exact_mod_cast
      (Algebra.norm_ne_zero_iff.mpr (Units.ne_zero γ)))
  have hv : 0 < v (γ : F) := InfinitePlace.pos_iff.mpr (Units.ne_zero γ)
  have hnorm : (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) : ℝ) =
      |(Algebra.norm ℚ (γ : F) : ℝ)| *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) := by
    rw [hJ, map_mul, FractionalIdeal.absNorm_span_singleton]
    push_cast
    rfl
  change _ = affineResidueScale I * Real.exp (principalNormalizedLogVector γ v)
  unfold affineResidueScale principalNormalizedLogVector
  rw [hnorm, Real.rpow_def_of_pos (mul_pos hg hi), Real.rpow_def_of_pos hi,
    Real.log_mul hg.ne' hi.ne', ← Real.exp_log hv, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_exp]
  ring

private theorem Q_smul (q : InfinitePlace F → ℝ) (s : ℝ)
    (x : mixedEmbedding.euclidean.mixedSpace F) :
    RayParity.Q F q (s • x) = s • RayParity.Q F q x := by
  apply (Theta.traceToMixed F).injective
  simp [RayParity.Q, map_smul, mul_smul_comm]
private theorem norm_kernel (q : InfinitePlace F → ℝ)
    (hq : ∀ v, q v ≠ 0) (s : ℝ) (x : F) :
    ‖RayParity.Q F q (s • Theta.traceEmbedding F x)‖ ^ 2 =
      ∑ v : InfinitePlace F, (v.mult : ℝ) * (q v * s * v x) ^ 2 := by
  rw [Q_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    RayParity.Q_eq_traceRadialScale F q hq, Theta.norm_sq_traceRadialScale_traceEmbedding,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring
private theorem norm_dual (q : InfinitePlace F → ℝ)
    (hq : ∀ v, q v ≠ 0) (s : ℝ) (x : F) :
    ‖RayParity.Q F q (s • Theta.traceConjugation F (Theta.traceEmbedding F x))‖ ^ 2 =
      ∑ v : InfinitePlace F, (v.mult : ℝ) * (q v * s * v x) ^ 2 := by
  rw [← map_smul, RayParity.Q_eq_traceRadialScale F q hq,
    ← Theta.traceConjugation_traceRadialScale, (Theta.traceConjugation F).norm_map,
    ← RayParity.Q_eq_traceRadialScale F q hq]
  exact norm_kernel q hq s x

private theorem q_nonzero (u : ℝ) (hu : 0 < u) (h : RayCoset.logHyperplane F) :
    ∀ v, RayTheta.q F u h v ≠ 0 := by
  intro v
  exact (mul_pos (Real.rpow_pos_of_pos hu _) (Real.exp_pos _)).ne'

private theorem empty_kernel_congr
    (a b : mixedEmbedding.euclidean.mixedSpace F) (hab : ‖a‖ ^ 2 = ‖b‖ ^ 2) :
    RayParity.gδ F ∅ a = RayParity.gδ F ∅ b := by
  simp only [RayParity.gδ, Finset.prod_empty, one_mul, Theta.latticeGaussian,
    ← Complex.ofReal_pow, hab]

theorem affineResidueKernel_principal_mul
    (hF : NumberField.IsTotallyComplex F)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (u : ℝ) (hu : 0 < u) (h : RayCoset.logHyperplane F) (x : F) :
    RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
      (affineResidueScale J • Theta.traceEmbedding F ((γ : F) * x))) =
    RayParity.gδ F ∅ (RayParity.Q F
      (RayTheta.q F u (h + principalNormalizedLogShift hF γ))
      (affineResidueScale I • Theta.traceEmbedding F x)) := by
  apply empty_kernel_congr
  rw [norm_kernel _ (q_nonzero u hu h),
    norm_kernel _ (q_nonzero u hu (h + principalNormalizedLogShift hF γ))]
  apply Finset.sum_congr rfl
  intro v _
  have hs := affineResidueScale_principal_mul hF I J γ hJ v
  simp only [map_mul, RayTheta.q, Submodule.coe_add, Pi.add_apply, Real.exp_add]
  congr 2
  calc
    u ^ (Module.finrank ℚ F : ℝ)⁻¹ * Real.exp (h.val v) *
        affineResidueScale J * (v (γ : F) * v x) =
        u ^ (Module.finrank ℚ F : ℝ)⁻¹ * Real.exp (h.val v) *
          (affineResidueScale J * v (γ : F)) * v x := by ring
    _ = _ := by rw [hs]; ring

theorem affineResidueDualKernel_principal_mul
    (hF : NumberField.IsTotallyComplex F)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (u : ℝ) (hu : 0 < u) (h : RayCoset.logHyperplane F) (β : F) :
    RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h))
      ((affineResidueScale J)⁻¹ • Theta.traceConjugation F
        (Theta.traceEmbedding F (((γ⁻¹ : Fˣ) : F) * β)))) =
    RayParity.gδ F ∅ (RayParity.Q F
      (RayTheta.q F u (-(h + principalNormalizedLogShift hF γ)))
      ((affineResidueScale I)⁻¹ • Theta.traceConjugation F
        (Theta.traceEmbedding F β))) := by
  apply empty_kernel_congr
  rw [norm_dual _ (q_nonzero u hu (-h)),
    norm_dual _ (q_nonzero u hu (-(h + principalNormalizedLogShift hF γ)))]
  apply Finset.sum_congr rfl
  intro v _
  have hs := congrArg (fun r : ℝ => r⁻¹)
    (affineResidueScale_principal_mul hF I J γ hJ v)
  simp only [mul_inv_rev, ← Real.exp_neg] at hs
  simp only [map_mul, Units.val_inv_eq_inv_val, map_inv₀, RayTheta.q,
    Submodule.coe_add, Submodule.coe_neg, Pi.add_apply, Pi.neg_apply,
    neg_add, Real.exp_add]
  congr 2
  calc
    u ^ (Module.finrank ℚ F : ℝ)⁻¹ * Real.exp (-h.val v) *
        (affineResidueScale J)⁻¹ * ((v (γ : F))⁻¹ * v β) =
        u ^ (Module.finrank ℚ F : ℝ)⁻¹ * Real.exp (-h.val v) *
          ((v (γ : F))⁻¹ * (affineResidueScale J)⁻¹) * v β := by ring
    _ = _ := by rw [hs]; ring

end DedekindZetaZeroFree.Hecke.Theta

end
