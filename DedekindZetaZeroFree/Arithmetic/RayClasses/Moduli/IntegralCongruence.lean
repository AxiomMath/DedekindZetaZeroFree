module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralIdealModulus

@[expose] public section

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.RayClassBridge

private theorem local_maximal_pow_mem_iff
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (t : v.adicCompletionIntegers F) :
    t ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n ↔
      Valued.v (t : v.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (v.adicCompletionIntegers F)
  have hval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have hu := Valuation.isUniformizer_of_maximalIdeal_eq_span
      (Valued.v : Valuation (v.adicCompletion F) _) (hπ.maximalIdeal_eq)
    rw [hu.val, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)]
    rfl
  have heq := (Valuation.valuationSubring.integers
    (Valued.v : Valuation (v.adicCompletion F) _)).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπ n
  change t ∈ ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n : Set _) ↔ _
  erw [heq]
  change Valued.v (t : v.adicCompletion F) ≤ Valued.v (π : v.adicCompletion F) ^ n ↔ _
  rw [hval, ← WithZero.exp_nsmul]
  simp

theorem integral_mem_rayLocalHigherUnitGroup_iff
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (_hn : 0 < n)
    (α : 𝓞 F) (_hα : α ≠ 0) (x : Fˣ) (hx : (x : F) = (α : F)) :
    ClassFieldTheory.finitePlaceUnitEmbedding v x ∈
      ClassFieldTheory.rayLocalHigherUnitGroup v n ↔
      α - 1 ∈ v.asIdeal ^ n := by
  let t : v.adicCompletionIntegers F :=
    ⟨algebraMap (𝓞 F) (v.adicCompletion F) (α - 1),
      v.coe_mem_adicCompletionIntegers (α - 1)⟩
  have hcong : t ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n ↔
      α - 1 ∈ v.asIdeal ^ n := by
    rw [local_maximal_pow_mem_iff]
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (α - 1)) ≤ _ ↔ _
    erw [v.valuedAdicCompletion_eq_valuation (α - 1)]
    rw [v.valuation_of_algebraMap, v.intValuation_le_pow_iff_mem]
  have hxlocal :
      (ClassFieldTheory.finitePlaceUnitEmbedding v x : v.adicCompletion F) =
        algebraMap (𝓞 F) (v.adicCompletion F) α := by
    change algebraMap F (v.adicCompletion F) (x : F) = _
    rw [hx, ← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  rw [ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff_exists_one_add v n _hn]
  constructor
  · rintro ⟨s, hs, he⟩
    have hst : s = t := by
      apply Subtype.ext
      change (s : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (α - 1)
      rw [map_sub, map_one]
      rw [hxlocal] at he
      change algebraMap (𝓞 F) (v.adicCompletion F) α = 1 + (s : v.adicCompletion F) at he
      rw [he]
      ring
    exact hcong.mp (hst ▸ hs)
  · intro h
    refine ⟨t, hcong.mpr h, ?_⟩
    rw [hxlocal]
    change algebraMap (𝓞 F) (v.adicCompletion F) α =
      1 + algebraMap (𝓞 F) (v.adicCompletion F) (α - 1)
    simp only [map_sub, map_one]
    ring

theorem integral_finite_ray_congruent_iff
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (α : 𝓞 F) (hα : α ≠ 0) (x : Fˣ) (hx : (x : F) = (α : F)) :
    (∀ v, v ∈ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support →
      ClassFieldTheory.finitePlaceUnitEmbedding v x ∈
        ClassFieldTheory.rayLocalHigherUnitGroup v
          ((narrowIdealModulus F 𝔪 h𝔪).finitePart v)) ↔
      α - 1 ∈ 𝔪 := by
  have hexp (v : HeightOneSpectrum (𝓞 F)) :
      (narrowIdealModulus F 𝔪 h𝔪).finitePart v =
        (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors := by
    simp only [narrowIdealModulus_finitePart,
      FractionalIdeal.count_coe F v h𝔪, Int.toNat_natCast]
  have hideal :
      (⨅ v : HeightOneSpectrum (𝓞 F),
        v.asIdeal ^ (narrowIdealModulus F 𝔪 h𝔪).finitePart v) = 𝔪 := by
    simp only [hexp]
    exact Ideal.iInf_maxPowDividing_eq h𝔪
  change _ ↔ α - 1 ∈ 𝔪
  conv_rhs => rw [← hideal]
  rw [Submodule.mem_iInf]
  constructor
  · intro h v
    by_cases hv : v ∈ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support
    · exact (integral_mem_rayLocalHigherUnitGroup_iff F v _
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)) α hα x hx).mp (h v hv)
    · have hz := Finsupp.notMem_support_iff.mp hv
      simp only [hz, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  · intro h v hv
    exact (integral_mem_rayLocalHigherUnitGroup_iff F v _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)) α hα x hx).mpr (h v)

theorem integral_infinite_ray_positive_iff
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (α : 𝓞 F) (x : Fˣ) (hx : (x : F) = (α : F)) :
    (∀ v, v ∈ (narrowIdealModulus F 𝔪 h𝔪).infinitePart →
      0 < v.1.embedding_of_isReal v.2 (x : F)) ↔
      ∀ φ : F →+* ℝ, 0 < φ (α : F) := by
  constructor
  · intro h φ
    let ψ : F →+* ℂ := Complex.ofRealHom.comp φ
    have hψ : NumberField.ComplexEmbedding.IsReal ψ := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext a
      simp [ψ, NumberField.ComplexEmbedding.conjugate]
    let v : {v : NumberField.InfinitePlace F // v.IsReal} :=
      ⟨NumberField.InfinitePlace.mk ψ, ⟨ψ, hψ, rfl⟩⟩
    have he : v.1.embedding_of_isReal v.2 = φ := by
      ext a
      apply Complex.ofReal_injective
      rw [NumberField.InfinitePlace.embedding_of_isReal_apply]
      exact congrArg (fun f : F →+* ℂ => f a)
        (NumberField.InfinitePlace.embedding_mk_eq_of_isReal hψ)
    simpa [narrowIdealModulus_infinitePart, he, hx] using h v (by simp)
  · intro h v hv
    simpa only [hx] using h (v.1.embedding_of_isReal v.2)

theorem isRayCongruent_iff_integral
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (α : 𝓞 F) (hα : α ≠ 0) (x : Fˣ) (hx : (x : F) = (α : F)) :
    ClassFieldTheory.IsRayCongruent (narrowIdealModulus F 𝔪 h𝔪) x ↔
      α - 1 ∈ 𝔪 ∧ (∀ φ : F →+* ℝ, 0 < φ (α : F)) := by
  exact and_congr (integral_finite_ray_congruent_iff F 𝔪 h𝔪 α hα x hx)
    (integral_infinite_ray_positive_iff F 𝔪 h𝔪 α x hx)

theorem span_add_modulus_eq_top_of_sub_one_mem
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (α : 𝓞 F) (hα : α - 1 ∈ 𝔪) :
    Ideal.span {α} ⊔ 𝔪 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have ha : α ∈ Ideal.span {α} ⊔ 𝔪 :=
    Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton α))
  have hb : α - 1 ∈ Ideal.span {α} ⊔ 𝔪 := Ideal.mem_sup_right hα
  simpa only [sub_sub_cancel] using (Ideal.span {α} ⊔ 𝔪).sub_mem ha hb

end DedekindZetaZeroFree.RayClassBridge

end
