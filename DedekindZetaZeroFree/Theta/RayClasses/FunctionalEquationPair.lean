module

public import DedekindZetaZeroFree.Theta.RayClasses.RapidDecay
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ShiftedParityGaussian

@[expose] public section

noncomputable section

open Classical NumberField MeasureTheory
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayTheta

variable {K : Type} [Field K] [NumberField K]

private lemma q_pos (t : ℝ) (ht : 0 < t) (h : RayCoset.logHyperplane K)
    (v : InfinitePlace K) : 0 < q K t h v := by
  exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)

private lemma q_inv (t : ℝ) (ht : 0 < t) (h : RayCoset.logHyperplane K) :
    (fun v => (q K (1 / t) h v)⁻¹) = q K t (-h) := by
  funext v
  simp [q, one_div, Real.inv_rpow ht.le, Real.exp_neg, mul_inv_rev, mul_comm]

private lemma J_q (t : ℝ) (ht : 0 < t) (h : RayCoset.logHyperplane K) :
    RayParity.J K (q K t h) = t := by
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hh : ∑ v : InfinitePlace K, (v.mult : ℝ) * h.val v = 0 := by
    simpa [RayCoset.logHyperplane, RayCoset.weightedLogSum] using h.property
  simp only [RayParity.J, q, mul_pow, Finset.prod_mul_distrib]
  have he : (∏ v : InfinitePlace K, Real.exp (h.val v) ^ v.mult) = 1 := by
    simp_rw [← Real.exp_nat_mul]
    rw [← Real.exp_sum, hh, Real.exp_zero]
  rw [he, mul_one, Finset.prod_pow_eq_pow_sum,
    InfinitePlace.sum_mult_eq, ← Real.rpow_natCast,
    ← Real.rpow_mul ht.le, inv_mul_cancel₀ hn, Real.rpow_one]

theorem fδ_one_div
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K))
    (t : ℝ) (ht : 0 < t) :
    fδ D δ (1 / t) = RayParity.εδ K δ * (t : ℂ) * gδDual D δ t := by
  letI := RayCoset.normalizedLattice_discrete D
  letI := RayCoset.normalizedLattice_isZLattice D
  have heq (h : RayCoset.logHyperplane K) :=
    (RayParity.ShiftedPoisson.poisson K (RayCoset.normalizedLattice D) δ
      (q K (1 / t) h) (q_pos (1 / t) (one_div_pos.mpr ht) h)
      (RayCoset.normalizedBasepoint D)).2.2.tsum_eq
  simp only [RayCoset.covolume_normalizedLattice, J_q (1 / t) (one_div_pos.mpr ht),
    q_inv t ht] at heq
  unfold fδ gδDual
  rw [if_pos (one_div_pos.mpr ht), if_pos ht]
  rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  simp only [one_div, mul_inv_rev, inv_inv]
  simp only [Complex.ofReal_one, inv_one, inv_inv, mul_one]
  field_simp
  <;> ring

def Pδ (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    WeakFEPair ℂ where
  f := fδ D δ
  g := gδDual D δ
  k := 1
  ε := RayParity.εδ K δ
  f₀ := f0δ D δ
  g₀ := g0δ D δ
  hf_int := locallyIntegrableOn_fδ D δ
  hg_int := locallyIntegrableOn_gδDual D δ
  hk := by norm_num
  hε := by
    exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
  h_feq := by
    intro t ht
    simpa only [Real.rpow_one, smul_eq_mul] using fδ_one_div D δ t ht
  hf_top := fδ_sub_f0δ_isBigO_rpow D δ
  hg_top := gδDual_sub_g0δ_isBigO_rpow D δ

@[simp] theorem Pδ_f (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    (Pδ D δ).f = fδ D δ := rfl

@[simp] theorem Pδ_g (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    (Pδ D δ).g = gδDual D δ := rfl

@[simp] theorem Pδ_k (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    (Pδ D δ).k = 1 := rfl

@[simp] theorem Pδ_ε (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    (Pδ D δ).ε = RayParity.εδ K δ := rfl

@[simp] theorem Pδ_f₀ (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    (Pδ D δ).f₀ = f0δ D δ := rfl

@[simp] theorem Pδ_g₀ (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    (Pδ D δ).g₀ = g0δ D δ := rfl

theorem f0δ_of_nonempty (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (hδ : δ.Nonempty) :
    f0δ D δ = 0 := by
  simp [f0δ, hδ.ne_empty]

theorem g0δ_of_nonempty (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (hδ : δ.Nonempty) :
    g0δ D δ = 0 := by
  simp [g0δ, hδ.ne_empty]

end DedekindZetaZeroFree.AbelianQuotient.RayTheta

end
