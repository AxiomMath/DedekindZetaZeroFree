module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralCongruence

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain FractionalIdeal

namespace DedekindZetaZeroFree.RayClassBridge

private theorem ray_valuation_le_one
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (x : Fˣ)
    (hx : ClassFieldTheory.finitePlaceUnitEmbedding v x ∈
      ClassFieldTheory.rayLocalHigherUnitGroup v n) :
    v.valuation F (x : F) ≤ 1 := by
  obtain ⟨y, hy, _⟩ := (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff v n _).mp hx
  have h := congrArg Units.val hy
  change (y : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (x : F) at h
  have hi := (y : v.adicCompletionIntegers F).property
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hi
  rw [h] at hi
  simpa only [HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, HeightOneSpectrum.adicCompletion.valued_coe] using hi

private theorem denominator_ideal
    (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    ∃ D : Ideal (𝓞 F), D ≠ ⊥ ∧
      (∀ b : 𝓞 F, b ∈ D ↔ ∃ a : 𝓞 F, (a : F) = (x : F) * (b : F)) := by
  obtain ⟨D, hD⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    (show (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ⊓
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((x : F)⁻¹) ≤ 1 from inf_le_left)
  have hmem (b : 𝓞 F) : b ∈ D ↔ ∃ a : 𝓞 F, (a : F) = (x : F) * (b : F) := by
    have hb : (b : F) ∈ (D : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ↔ b ∈ D := by
      rw [FractionalIdeal.mem_coeIdeal]
      constructor
      · rintro ⟨c, hc, hcb⟩
        exact (NumberField.RingOfIntegers.coe_injective hcb) ▸ hc
      · intro hb; exact ⟨b, hb, rfl⟩
    rw [← hb, hD]
    change ((b : F) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ∧
      (b : F) ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((x : F)⁻¹)) ↔ _
    rw [FractionalIdeal.mem_spanSingleton]
    constructor
    · rintro ⟨_, a, ha⟩
      refine ⟨a, ?_⟩
      rw [Algebra.smul_def] at ha
      change (a : F) * (x : F)⁻¹ = (b : F) at ha
      calc
        (a : F) = (x : F) * ((a : F) * (x : F)⁻¹) := by field_simp
        _ = (x : F) * (b : F) := by rw [ha]
    · rintro ⟨a, ha⟩
      refine ⟨(FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩, a, ?_⟩
      rw [Algebra.smul_def]
      change (a : F) * (x : F)⁻¹ = (b : F)
      rw [ha]; field_simp
  refine ⟨D, ?_, hmem⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 F) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb0
  have hbD : b ∈ D := (hmem b).mpr ⟨a, by rw [← hab]; field_simp⟩
  intro hz
  simpa [hz, hb0] using hbD

private theorem denominator_coprime
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ)
    (hx : ClassFieldTheory.IsRayCongruent (narrowIdealModulus F 𝔪 h𝔪) x)
    (D : Ideal (𝓞 F)) (hD : D ≠ ⊥)
    (hmem : ∀ b : 𝓞 F, b ∈ D ↔ ∃ a : 𝓞 F, (a : F) = (x : F) * (b : F)) :
    D ⊔ 𝔪 = ⊤ := by
  by_contra htop
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (D ⊔ 𝔪) htop
  have hDP : D ≤ P := le_trans le_sup_left hle
  have hMP : 𝔪 ≤ P := le_trans le_sup_right hle
  have hP0 : P ≠ ⊥ := by
    intro hz
    apply hD
    exact le_bot_iff.mp (hz ▸ hDP)
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, hP0⟩
  have hv : v ∈ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support := by
    change v ∈ (↑(narrowIdealModulus F 𝔪 h𝔪).finitePart.support : Set _)
    rw [narrowIdealModulus_support F 𝔪 h𝔪]
    exact hMP
  have hval := ray_valuation_le_one F v _ x (hx.1 v hv)
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer (x : F) hval
  have hbD : (b : 𝓞 F) ∈ D := (hmem b).mpr ⟨a, hab.symm⟩
  exact b.property (hDP hbD)

theorem isRayCongruent_clear_denominators
    (F : Type) [Field F] [NumberField F]
    (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (x : Fˣ)
    (hx : ClassFieldTheory.IsRayCongruent (narrowIdealModulus F 𝔪 h𝔪) x) :
    ∃ (α β : 𝓞 F),
      α ≠ 0 ∧ β ≠ 0 ∧ α - 1 ∈ 𝔪 ∧ β - 1 ∈ 𝔪 ∧
        (α : F) = (x : F) * (β : F) := by
  obtain ⟨D, hD, hmem⟩ := denominator_ideal F x
  have hcop := denominator_coprime F 𝔪 h𝔪 x hx D hD hmem
  have hex : ∃ β : 𝓞 F, β ∈ D ∧ β ≠ 0 ∧ β - 1 ∈ 𝔪 := by
    by_cases hm : 𝔪 = ⊤
    · obtain ⟨β, hβD, hβ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
      exact ⟨β, hβD, hβ, hm ▸ Submodule.mem_top⟩
    · obtain ⟨β, hβD, j, hj, hsum⟩ :=
        Ideal.isCoprime_iff_exists.mp (Ideal.isCoprime_iff_sup_eq.mpr hcop)
      have hcong : β - 1 ∈ 𝔪 := by
        have heq : β - 1 = -j := by rw [← hsum]; ring
        rw [heq]
        exact 𝔪.neg_mem hj
      have hβ : β ≠ 0 := by
        intro hz
        have hneg : (-1 : 𝓞 F) ∈ 𝔪 := by simpa [hz] using hcong
        have h1 : (1 : 𝓞 F) ∈ 𝔪 := by simpa using 𝔪.neg_mem hneg
        exact hm (Ideal.eq_top_of_isUnit_mem 𝔪 h1 isUnit_one)
      exact ⟨β, hβD, hβ, hcong⟩
  obtain ⟨β, hβD, hβ, hβm⟩ := hex
  obtain ⟨α, hαeq⟩ := (hmem β).mp hβD
  have hβF : (β : F) ≠ 0 := by exact_mod_cast hβ
  have hα : α ≠ 0 := by
    intro hz
    have hh := hαeq
    simp only [hz, map_zero] at hh
    exact (mul_ne_zero x.ne_zero hβF) hh.symm
  let b : Fˣ := Units.mk0 (β : F) hβF
  have hb : (b : F) = (β : F) := rfl
  have hbcong := (integral_finite_ray_congruent_iff F 𝔪 h𝔪 β hβ b hb).mpr hβm
  have hab : ((x * b : Fˣ) : F) = (α : F) := by
    simpa only [Units.val_mul, hb] using hαeq.symm
  have hαm : α - 1 ∈ 𝔪 := by
    apply (integral_finite_ray_congruent_iff F 𝔪 h𝔪 α hα (x * b) hab).mp
    intro v hv
    rw [map_mul]
    exact (ClassFieldTheory.rayLocalHigherUnitGroup v _).mul_mem (hx.1 v hv) (hbcong v hv)
  exact ⟨α, β, hα, hβ, hαm, hβm, hαeq⟩

end DedekindZetaZeroFree.RayClassBridge
