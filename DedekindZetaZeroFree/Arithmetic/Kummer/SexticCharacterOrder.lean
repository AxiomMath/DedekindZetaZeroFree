module

public import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity

@[expose] public section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.Conductor
private theorem no_real (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : IsEmpty (F →+* ℝ) := by
  constructor
  intro φ
  have h : IsPrimitiveRoot (φ ζ) 12 := hζ.map_of_injective φ.injective
  have he : (φ ζ) ^ 12 = 1 := h.pow_eq_one
  have hs : (φ ζ) ^ 2 = 1 := by
    have he' : ((φ ζ)^2)^6 = 1^6 := by simpa [← pow_mul] using he
    exact (pow_left_inj₀ (sq_nonneg _) (by norm_num) (by norm_num : (6:ℕ) ≠ 0)).mp he'
  have hd := h.dvd_of_pow_eq_one 2 hs
  norm_num at hd

private theorem support_finite (F : Type) [Field F] [NumberField F] (u : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (u : F) ≠ 1}.Finite := by
  apply ((HeightOneSpectrum.Support.finite (𝓞 F) (u : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((u : F)⁻¹))).subset
  intro v hv
  change 1 < v.valuation F (u : F) ∨ 1 < v.valuation F ((u : F)⁻¹)
  rcases lt_or_gt_of_ne hv with h | h
  · right
    rw [Valuation.map_inv]
    exact (one_lt_inv₀ (lt_of_le_of_ne bot_le (Ne.symm (by simpa using (Units.ne_zero (Units.map (v.valuation F).toMonoidWithZeroHom.toMonoidHom u)))))).mpr h
  · exact Or.inl h

private theorem prime_coprime (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (RayClassBridge.narrowIdealModulus F m hm).finitePart.support) :
    v.asIdeal ⊔ m = ⊤ := by
  have hn : ¬ m ≤ v.asIdeal := by
    intro h
    apply hv
    change v ∈ (↑(RayClassBridge.narrowIdealModulus F m hm).finitePart.support : Set _)
    rw [RayClassBridge.narrowIdealModulus_support F m hm]
    exact h
  exact (Ideal.isMaximal_def.mp v.isMaximal).2 _
    (lt_of_le_of_ne le_sup_left (fun he => hn (he ▸ le_sup_right)))

theorem global_kummer_sixth_power
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (u : Fˣ) (χ : PrimitiveFrequencyCharacter F)
    (hχ : IsKummerFrequencyCharacter F ζ12 ι S u χ) :
    ∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ χ.conductor = ⊤ →
      χ.character n ^ (6 : ℕ) = 1 := by
  classical
  letI := no_real F ζ12 hζ12
  have hc : NumberField.IsTotallyComplex F := ⟨fun v =>
    NumberField.InfinitePlace.not_isReal_iff_isComplex.mp (fun h =>
      isEmptyElim (NumberField.InfinitePlace.embedding_of_isReal h))⟩

  let m := RayClassBridge.narrowIdealModulus F χ.conductor χ.conductor_ne_zero
  let bad := (hS.union (support_finite F u)).toFinset
  let a : HeightOneSpectrum (𝓞 F) →₀ ℕ := Finsupp.indicator bad (fun _ _ => 1)
  let M : ClassFieldTheory.RayClassModulus F :=
    { finitePart := m.finitePart + a, infinitePart := m.infinitePart }
  have hmM : m ≤ M := ⟨by intro v; simp [M], le_rfl⟩
  let R := RayClassBridge.rayCharacter F hc χ.conductor χ.conductor_ne_zero χ.character
  let P := ClassFieldTheory.rayClassIdealModulusProjection F hmM

  have hR : (powMonoidHom 6).comp (R.comp P) = 1 := by
    apply ClassFieldTheory.rayClassGroup_hom_ext_finitePrime F M
    intro v hv
    have hvM : v ∉ m.finitePart.support := by
      intro h
      apply hv
      exact Finsupp.mem_support_iff.mpr (by
        have hp := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
        change m.finitePart v + a v ≠ 0
        omega)
    have hvbad : v ∉ bad := by
      intro h
      apply hv
      apply Finsupp.mem_support_iff.mpr
      change m.finitePart v + a v ≠ 0
      have ha : a v = 1 := by simp [a, Finsupp.indicator, h]
      omega
    have hvS : v ∉ S := by
      intro h
      exact hvbad (by simp [bad, h])
    have hvu : v.valuation F (u : F) = 1 := by
      by_contra h
      exact hvbad (by simp [bad, h])
    have hcop := prime_coprime F χ.conductor χ.conductor_ne_zero v hvM
    have hid : ClassFieldTheory.rayClassOfFinitePrime m v hvM =
        RayClassBridge.integralRayClass F χ.conductor χ.conductor_ne_zero
          v.asIdeal v.ne_bot hcop := by rfl
    have hval : (R (ClassFieldTheory.rayClassOfFinitePrime m v hvM) : ℂ) =
        χ.character v.asIdeal := by
      rw [hid]
      exact RayClassBridge.rayCharacter_integral F hc χ.conductor
        χ.conductor_ne_zero χ.character v.asIdeal v.ne_bot hcop
    apply Units.ext
    change ((R (P (ClassFieldTheory.rayClassOfFinitePrime M v hv))) : ℂ) ^ 6 = 1
    rw [ClassFieldTheory.rayClassIdealModulusProjection_prime F hmM v hv, hval]
    obtain ⟨_, j, _, hj⟩ := hχ v hvS hvu
    rw [hj, ← map_pow]
    have hroot : (ζ12 ^ (2 : ℕ)) ^ (6 : ℕ) = 1 := by
      rw [← pow_mul]
      exact hζ12.pow_eq_one
    rw [← pow_mul, Nat.mul_comm j.val 6, pow_mul, hroot, one_pow, map_one]

  intro n hn hcop
  let c := RayClassBridge.integralRayClass F χ.conductor χ.conductor_ne_zero n hn hcop
  obtain ⟨d, hd⟩ := ClassFieldTheory.rayClassIdealModulusProjection_surjective F hmM c
  have hx := DFunLike.congr_fun hR d
  apply_fun (fun z : ℂˣ => (z : ℂ)) at hx
  change (R (P d) : ℂ) ^ 6 = 1 at hx
  rw [hd] at hx
  simpa [c, R, RayClassBridge.rayCharacter_integral] using hx
end DedekindZetaZeroFree.Detector.Conductor
