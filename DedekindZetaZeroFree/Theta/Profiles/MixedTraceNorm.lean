module

public import DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

theorem mixed_norm_sq
    (K : Type*) [Field K] [NumberField K]
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) (x : K) :
    ‖traceRadialScale K q hq (traceEmbedding K x)‖ ^ 2 =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * (q v) ^ 2 * (v x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [traceRadialScale, traceEmbedding, traceToMixed, unscaleComplexCoordinates,
    mixedEmbedding.euclidean.toMixed, mixedSpaceOfRealSpace_apply,
    radialMixedSpaceUnit, WithLp.prod_inner_apply, PiLp.inner_apply,
    LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.piCongrRight_symm_apply,
    mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex]
  simp only [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    WithLp.fst, WithLp.snd, WithLp.ofLp_toLp, PiLp.toLp_apply,
    ContinuousLinearEquiv.piCongrRight_symm_apply, divideBySqrtTwo_symm_apply,
    Pi.mul_apply, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex, _root_.norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    norm_embedding_of_isReal, norm_embedding_eq]
  rw [sum_eq_sum_add_sum]
  simp
  have hreal (w : {w : InfinitePlace K // IsReal w}) :
      (embedding_of_isReal w.2 x) ^ 2 = (w.1 x) ^ 2 := by
    rw [← norm_embedding_of_isReal w.2 x, Real.norm_eq_abs, sq_abs]
  simp_rw [hreal, mul_pow, sq_abs, norm_embedding_eq, mul_assoc]

end DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

end
