module

public import DedekindZetaZeroFree.Theta.Unfolding.ParitySeriesMellin

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.Projection

variable {K : Type} [Field K] [NumberField K]

theorem sign_projection (D : RayCoset.Data K) (x : RayCoset.X D) :
    ((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K)⁻¹ *
        (∑ δ ∈ (Finset.univ : Finset (RayCoset.RealPlaces K)).powerset,
          (RayCoset.signδ D δ x : ℂ)) =
      if x ∈ RayCoset.positiveOrbits D then 1 else 0 := by
  classical
  induction x using Quotient.inductionOn with
  | h α =>
    change ((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K)⁻¹ *
        (∑ δ ∈ (Finset.univ : Finset (RayCoset.RealPlaces K)).powerset,
          (RayCoset.representativeSign δ α.val : ℂ)) =
        if RayCoset.TotallyPositive K α.val then 1 else 0
    simp only [RayCoset.representativeSign, Complex.ofReal_prod]
    rw [← Finset.prod_one_add]
    by_cases hp : RayCoset.TotallyPositive K α.val
    · rw [if_pos hp]
      have he : ∀ v : RayCoset.RealPlaces K,
          (1 + (Real.sign (RayCoset.realEmbedding K v (α.val : K)) : ℂ)) = 2 := by
        intro v
        rw [Real.sign_of_pos (hp (RayCoset.realEmbedding K v))]
        norm_num
      simp only [he, Finset.prod_const, Finset.card_univ]
      exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
    · rw [if_neg hp]
      obtain ⟨φ, hφ⟩ : ∃ φ : K →+* ℝ, ¬ 0 < φ (α.val : K) := by
        simpa only [RayCoset.TotallyPositive, not_forall] using hp
      let ψ : K →+* ℂ := Complex.ofRealHom.comp φ
      have hψ : NumberField.ComplexEmbedding.IsReal ψ := by
        ext y
        simp [ψ, NumberField.ComplexEmbedding.conjugate]
      let v : RayCoset.RealPlaces K :=
        ⟨NumberField.InfinitePlace.mk ψ, ⟨ψ, hψ, rfl⟩⟩
      have hv : RayCoset.realEmbedding K v = φ := by
        ext y
        apply Complex.ofReal_injective
        change ((NumberField.InfinitePlace.embedding_of_isReal v.property) y : ℂ) = _
        rw [NumberField.InfinitePlace.embedding_of_isReal_apply]
        change NumberField.InfinitePlace.embedding (NumberField.InfinitePlace.mk ψ) y = _
        rw [NumberField.InfinitePlace.embedding_mk_eq_of_isReal hψ]
        rfl
      have hn : φ (α.val : K) ≠ 0 :=
        (map_ne_zero φ).mpr (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr α.property.2)
      have hz : (1 + (Real.sign (RayCoset.realEmbedding K v (α.val : K)) : ℂ)) = 0 := by
        rw [hv, Real.sign_of_neg (lt_of_le_of_ne (not_lt.mp hφ) hn)]
        norm_num
      rw [Finset.prod_eq_zero (Finset.mem_univ v) hz, mul_zero]

end DedekindZetaZeroFree.AbelianQuotient.RayParity.Projection

namespace DedekindZetaZeroFree

open AbelianQuotient

set_option maxHeartbeats 800000 in

theorem rayParityProjection {K : Type} [Field K] [NumberField K]
    (D : RayCoset.Data K)
    (c : RayIdealClass K D.m D.modulus_ne_bot)
    (hc : rayIdealClass K D.m D.modulus_ne_bot D.a = some c⁻¹)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum
      (fun I : Ideal (𝓞 K) =>
        if rayIdealClass K D.m D.modulus_ne_bot I = some c then
          (Ideal.absNorm I : ℂ) ^ (-s)
        else 0)
      (((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K)⁻¹ *
        ∑ δ ∈ (Finset.univ : Finset (RayCoset.RealPlaces K)).powerset,
          RayCoset.Zδ D δ s) := by
  classical
  let A : ℂ := ((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K)⁻¹
  let S := (Finset.univ : Finset (RayCoset.RealPlaces K)).powerset
  let W : RayCoset.X D → ℂ := fun x => (RayCoset.normWeight D x : ℂ) ^ (-s)
  have hsum : HasSum
      (fun x => A * ∑ δ ∈ S, RayCoset.signedOrbitWeight D δ s x)
      (A * ∑ δ ∈ S, RayCoset.Zδ D δ s) :=
    (hasSum_sum (fun δ _ => RayCoset.hasSum_signedOrbitWeight D δ s hs)).mul_left A
  have hind : HasSum ((RayCoset.positiveOrbits D).indicator W)
      (A * ∑ δ ∈ S, RayCoset.Zδ D δ s) := by
    apply hsum.congr_fun
    intro x
    change (RayCoset.positiveOrbits D).indicator W x =
      A * ∑ δ ∈ S, (RayCoset.signδ D δ x : ℂ) * W x
    rw [← Finset.sum_mul, ← mul_assoc]
    rw [RayParity.Projection.sign_projection D x]
    by_cases hx : x ∈ RayCoset.positiveOrbits D <;>
      simp [Set.indicator_apply, hx]
  have hpos : HasSum (fun x : RayCoset.Xpos D => W x.val)
      (A * ∑ δ ∈ S, RayCoset.Zδ D δ s) :=
    hasSum_subtype_iff_indicator.mpr hind
  let e := RayCoset.positiveIdealEquiv D c hc
  have hclass : HasSum
      (fun I : {I : Ideal (𝓞 K) | rayIdealClass K D.m D.modulus_ne_bot I = some c} =>
        (Ideal.absNorm I.val : ℂ) ^ (-s))
      (A * ∑ δ ∈ S, RayCoset.Zδ D δ s) := by
    apply e.hasSum_iff.mp
    apply hpos.congr_fun
    intro x
    change (Ideal.absNorm (RayCoset.orbitIdeal D x.val) : ℂ) ^ (-s) = W x.val
    dsimp [W]
    rw [← RayCoset.orbitIdeal_absNorm D x.val, Complex.ofReal_natCast]
  have hall := (hasSum_subtype_iff_indicator
    (f := fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℂ) ^ (-s))
    (s := {I : Ideal (𝓞 K) | rayIdealClass K D.m D.modulus_ne_bot I = some c})).mp hclass
  apply hall.congr_fun
  intro I
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

end DedekindZetaZeroFree

end
