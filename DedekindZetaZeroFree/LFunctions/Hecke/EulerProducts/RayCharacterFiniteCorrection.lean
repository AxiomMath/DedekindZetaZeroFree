module

public import DedekindZetaZeroFree.LFunctions.Dedekind.WeightedIdealEulerProducts
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.FiniteOrderAndNormBounds

@[expose] public section

open scoped NumberField BigOperators

namespace DedekindZetaZeroFree.HeckeCorollary

open AbelianQuotient IsDedekindDomain

noncomputable def finiteEulerCorrection
    (K : Type) [Field K] [NumberField K]
    (w : Ideal (𝓞 K) → ℂ) (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏ P ∈ S, (1 - w P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))

theorem eulerCorrectionFactor_ne_zero
    (K : Type) [Field K] [NumberField K]
    (w : Ideal (𝓞 K) → ℂ) (hnorm : ∀ I, ‖w I‖ ≤ 1)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) (hs : 0 < s.re) :
    1 - w P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  have hq : 1 < Ideal.absNorm P.asIdeal := Odlyzko.one_lt_primeIdealNorm K P
  have hpow : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [show ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ =
        (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) from
      Odlyzko.norm_inverseNormPower _ (by omega) s]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (neg_neg_of_pos hs)
  have hlt : ‖w P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hnorm P.asIdeal) (norm_nonneg _)).trans_lt
      (by simpa using hpow)
  intro heq
  have hval := (sub_eq_zero.mp heq).symm
  rw [hval, norm_one] at hlt
  exact (lt_irrefl 1 hlt)

theorem finiteEulerCorrection_ne_zero
    (K : Type) [Field K] [NumberField K]
    (w : Ideal (𝓞 K) → ℂ) (hnorm : ∀ I, ‖w I‖ ≤ 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) (hs : 0 < s.re) :
    finiteEulerCorrection K w S s ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun P _ ↦ eulerCorrectionFactor_ne_zero K w hnorm P s hs)

theorem finiteEulerCorrection_differentiable
    (K : Type) [Field K] [NumberField K]
    (w : Ideal (𝓞 K) → ℂ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ (finiteEulerCorrection K w S) := by
  apply Differentiable.fun_finsetProd
  intro P _
  have hq : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by
    have h : 1 < Ideal.absNorm P.asIdeal := Odlyzko.one_lt_primeIdealNorm K P
    exact_mod_cast (show Ideal.absNorm P.asIdeal ≠ 0 by omega)
  exact (differentiable_const 1).sub
    (((differentiable_id.neg).const_cpow (Or.inl hq)).const_mul _)

theorem rayCharacter_eulerCorrection
    (K : Type) [Field K] [NumberField K]
    (m m₀ : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hm₀ : m₀ ≠ ⊥)
    (χ : RayClassCharacter K m) (χ₀ : RayClassCharacter K m₀)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hzero : ∀ P ∈ S, χ P.asIdeal = 0)
    (hagree : ∀ P ∉ S, χ P.asIdeal = χ₀ P.asIdeal)
    (s : ℂ) (hs : 1 < s.re) :
    (∑' I : Ideal (𝓞 K), χ I * (Ideal.absNorm I : ℂ) ^ (-s)) =
      (∑' I : Ideal (𝓞 K), χ₀ I * (Ideal.absNorm I : ℂ) ^ (-s)) *
        finiteEulerCorrection K χ₀ S s := by
  classical
  have hχ := weightedIdealEulerProduct_hasProd K χ χ.map_mul' χ.map_top'
    ((χ.eq_zero_iff' ⊥).mpr (Or.inl rfl)) (rayCharacter_norm_le_one K m hm χ) s hs
  have hχ₀ := weightedIdealEulerProduct_hasProd K χ₀ χ₀.map_mul' χ₀.map_top'
    ((χ₀.eq_zero_iff' ⊥).mpr (Or.inl rfl)) (rayCharacter_norm_le_one K m₀ hm₀ χ₀) s hs
  let c := fun P : HeightOneSpectrum (𝓞 K) ↦
    if P ∈ S then 1 - χ₀ P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) else 1
  have hc : HasProd c (finiteEulerCorrection K χ₀ S s) := by
    have hc' : HasProd c (∏ P ∈ S, c P) :=
      hasProd_prod_of_ne_finset_one (fun P hP ↦ by simp [c, hP])
    simpa [finiteEulerCorrection, c] using hc'
  apply hχ.unique
  convert hχ₀.mul hc using 1
  funext P
  by_cases hP : P ∈ S
  · simp only [hzero P hP, zero_mul, sub_zero, inv_one, c, ite_eq_left hP]
    exact (inv_mul_cancel₀ (eulerCorrectionFactor_ne_zero K χ₀
      (rayCharacter_norm_le_one K m₀ hm₀ χ₀) P s (by linarith))).symm
  · simp [c, hP, hagree P hP]

theorem rayCharacter_dirichletSummable
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) ↦ χ I * (Ideal.absNorm I : ℂ) ^ (-s)) := by
  exact (weightedIdealSummability K χ χ.map_mul' χ.map_top'
    ((χ.eq_zero_iff' ⊥).mpr (Or.inl rfl)) (rayCharacter_norm_le_one K m hm χ) s hs).of_norm

theorem rayCharacter_eulerCorrection_hasSum
    (K : Type) [Field K] [NumberField K]
    (m m₀ : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hm₀ : m₀ ≠ ⊥)
    (χ : RayClassCharacter K m) (χ₀ : RayClassCharacter K m₀)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hzero : ∀ P ∈ S, χ P.asIdeal = 0)
    (hagree : ∀ P ∉ S, χ P.asIdeal = χ₀ P.asIdeal)
    (s : ℂ) (hs : 1 < s.re) (z₀ : ℂ)
    (h₀ : HasSum (fun I : Ideal (𝓞 K) ↦ χ₀ I * (Ideal.absNorm I : ℂ) ^ (-s)) z₀) :
    HasSum (fun I : Ideal (𝓞 K) ↦ χ I * (Ideal.absNorm I : ℂ) ^ (-s))
      (z₀ * finiteEulerCorrection K χ₀ S s) := by
  have heq := rayCharacter_eulerCorrection K m m₀ hm hm₀ χ χ₀ S hzero hagree s hs
  rw [h₀.tsum_eq] at heq
  exact heq ▸ (rayCharacter_dirichletSummable K m hm χ s hs).hasSum

end DedekindZetaZeroFree.HeckeCorollary
