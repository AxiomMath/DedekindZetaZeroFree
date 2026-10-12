module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CosetSignsAndNorms

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable (K : Type) [Field K] [NumberField K]

def rayUnitRealSign (u : (𝓞 K)ˣ) (v : RealPlaces K) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (if 0 < realEmbedding K v ((u : 𝓞 K) : K) then 0 else 1)

theorem rayUnitRealSign_one (v : RealPlaces K) :
    rayUnitRealSign K 1 v = 1 := by
  simp [rayUnitRealSign]

theorem rayUnitRealSign_mul (u w : (𝓞 K)ˣ) (v : RealPlaces K) :
    rayUnitRealSign K (u * w) v = rayUnitRealSign K u v * rayUnitRealSign K w v := by
  have hu : realEmbedding K v ((u : 𝓞 K) : K) ≠ 0 :=
    ((u.isUnit.map (algebraMap (𝓞 K) K)).map (realEmbedding K v)).ne_zero
  have hw : realEmbedding K v ((w : 𝓞 K) : K) ≠ 0 :=
    ((w.isUnit.map (algebraMap (𝓞 K) K)).map (realEmbedding K v)).ne_zero
  unfold rayUnitRealSign
  simp only [Units.val_mul, map_mul]
  by_cases hp : 0 < realEmbedding K v ((u : 𝓞 K) : K)
  · by_cases hq : 0 < realEmbedding K v ((w : 𝓞 K) : K)
    · simp [hp, hq, mul_pos hp hq]
    · have hn := lt_of_le_of_ne (le_of_not_gt hq) hw
      simp [hp, hq, not_lt_of_gt (mul_neg_of_pos_of_neg hp hn)]
  · have hn := lt_of_le_of_ne (le_of_not_gt hp) hu
    by_cases hq : 0 < realEmbedding K v ((w : 𝓞 K) : K)
    · simp [hp, hq, not_lt_of_gt (mul_neg_of_neg_of_pos hn hq)]
    · have hn' := lt_of_le_of_ne (le_of_not_gt hq) hw
      simp only [hp, hq, mul_pos_of_neg_of_neg hn hn', if_true, if_false]
      change (0 : ZMod 2) = 1 + 1
      decide

def rayUnitSigns : (𝓞 K)ˣ →* (RealPlaces K → Multiplicative (ZMod 2)) where
  toFun := rayUnitRealSign K
  map_one' := funext (rayUnitRealSign_one K)
  map_mul' u w := funext (rayUnitRealSign_mul K u w)

def rayUnitResidueSign (m : Ideal (𝓞 K)) :
    (𝓞 K)ˣ →* (𝓞 K ⧸ m)ˣ × (RealPlaces K → Multiplicative (ZMod 2)) :=
  (Units.map (Ideal.Quotient.mk m).toMonoidHom).prod (rayUnitSigns K)

private theorem realPlaces_totallyPositive (α : 𝓞 K) :
    (∀ v : RealPlaces K, 0 < realEmbedding K v (α : K)) ↔ TotallyPositive K α := by
  constructor
  · intro h φ
    let ψ : K →+* ℂ := Complex.ofRealHom.comp φ
    have hψ : NumberField.ComplexEmbedding.IsReal ψ := by
      ext x
      simp [ψ]
    let v : RealPlaces K :=
      ⟨NumberField.InfinitePlace.mk ψ, NumberField.InfinitePlace.isReal_mk_iff.mpr hψ⟩
    have he : realEmbedding K v (α : K) = φ (α : K) := by
      apply Complex.ofReal_injective
      rw [realEmbedding, NumberField.InfinitePlace.embedding_of_isReal_apply]
      change NumberField.InfinitePlace.embedding (NumberField.InfinitePlace.mk ψ) (α : K) = _
      rw [NumberField.InfinitePlace.embedding_mk_eq_of_isReal hψ]
      rfl
    exact he ▸ h v
  · intro h v
    exact h (realEmbedding K v)

theorem rayUnitResidueSign_ker (m : Ideal (𝓞 K)) :
    (rayUnitResidueSign K m).ker = positiveRayUnits K m := by
  ext u
  change rayUnitResidueSign K m u = 1 ↔ IsRayUnit K m u
  have hsign : rayUnitSigns K u = 1 ↔ TotallyPositive K (u : 𝓞 K) := by
    rw [← realPlaces_totallyPositive K]
    change (fun v => rayUnitRealSign K u v) = (fun _ => 1) ↔ _
    rw [funext_iff]
    apply forall_congr'
    intro v
    unfold rayUnitRealSign
    by_cases h : 0 < realEmbedding K v ((u : 𝓞 K) : K)
    · simp [h]
    · simp only [h, if_false]
      change (1 : ZMod 2) = 0 ↔ False
      decide
  have hres : Units.map (Ideal.Quotient.mk m).toMonoidHom u = 1 ↔
      (u : 𝓞 K) - 1 ∈ m := by
    rw [← Units.val_inj]
    change Ideal.Quotient.mk m (u : 𝓞 K) = 1 ↔ _
    rw [← map_one (Ideal.Quotient.mk m), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  change (Units.map (Ideal.Quotient.mk m).toMonoidHom u, rayUnitSigns K u) = (1, 1) ↔ _
  rw [Prod.mk.injEq, hres, hsign]
  rfl

theorem finite_rayUnit_quotient (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Finite ((𝓞 K)ˣ ⧸ positiveRayUnits K m) := by
  letI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm
  rw [← rayUnitResidueSign_ker K m]
  exact Finite.of_equiv (rayUnitResidueSign K m).range
    (QuotientGroup.quotientKerEquivRange (rayUnitResidueSign K m)).symm

theorem positiveRayUnits_finiteIndex (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    (positiveRayUnits K m).FiniteIndex := by
  letI := finite_rayUnit_quotient K m hm
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_pos_pow_mem_positiveRayUnits
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (u : (𝓞 K)ˣ) :
    ∃ k : ℕ, 0 < k ∧ u ^ k ∈ positiveRayUnits K m := by
  obtain ⟨k, hk, _, hmem⟩ := (positiveRayUnits K m).exists_pow_mem_of_index_ne_zero
    (positiveRayUnits_finiteIndex K m hm).index_ne_zero u
  exact ⟨k, hk, hmem⟩

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
