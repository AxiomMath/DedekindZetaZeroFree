module

public import DedekindZetaZeroFree.Arithmetic.Kummer.Sextic.ArtinCharacter
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ConductorKernel
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveLocalMinimality

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.PrimitiveRay

variable {F : Type} [Field F] [NumberField F]

theorem primitiveRay_exists (hc : NumberField.IsTotallyComplex F)
    (Φ : IdeleClassGroup F →ₜ* ℂˣ)
    (ho : ∃ n : ℕ, 0 < n ∧ ∀ c : IdeleClassGroup F, Φ c ^ n = 1) :
    ∃ (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
      (ρ : ClassFieldTheory.RayClassGroup (RayClassBridge.narrowIdealModulus F m hm) →* ℂˣ)
      (χ : RayClassCharacter F m),
      χ.IsPrimitive ∧
      (∀ I : Ideal (𝓞 F), χ I =
        if h : I ≠ ⊥ ∧ I ⊔ m = ⊤ then
          (ρ (RayClassBridge.integralRayClass F m hm I h.1 h.2) : ℂ)
        else 0) ∧
      (∀ c : IdeleClassGroup F,
        ρ ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
          F (RayClassBridge.narrowIdealModulus F m hm)).symm
            (QuotientGroup.mk'
              (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
                F (RayClassBridge.narrowIdealModulus F m hm)).congruenceSubgroup c)) = Φ c) ∧
      (∀ c : IdeleClassGroup F,
        RayClassBridge.ideleClassCharacter F hc m hm χ c = Φ c) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        IsLeast {k : ℕ | ∀ t : (v.adicCompletion F)ˣ,
          t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k →
            Φ (IdeleGroup.finitePlaceIdeleClass v t) = 1}
          ((RayClassBridge.narrowIdealModulus F m hm).finitePart v)) := by
  obtain ⟨_, _, m, hm, _, hdefining, hleast⟩ := conductorKernel hc Φ ho
  obtain ⟨ρ, _, χ, _, hzero, hρ, hχ⟩ :=
    rayDescent hc Φ.toMonoidHom m hm hdefining
  refine ⟨m, hm, ρ, χ, ?_, hzero, hρ, hχ, hleast⟩
  apply (primitive_iff_local_isLeast hc m hm χ).mpr
  intro v
  simp only [hχ]
  exact hleast v

theorem primitiveRay_support (hc : NumberField.IsTotallyComplex F)
    (Φ : IdeleClassGroup F →ₜ* ℂˣ)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (χ : RayClassCharacter F m)
    (hprimitive : χ.IsPrimitive)
    (hχ : ∀ c : IdeleClassGroup F,
      RayClassBridge.ideleClassCharacter F hc m hm χ c = Φ c)
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : ∀ t : (v.adicCompletion F)ˣ,
      t ∈ (v.adicCompletionIntegers F).units →
        Φ (IdeleGroup.finitePlaceIdeleClass v t) = 1) :
    ¬ m ≤ v.asIdeal := by
  have hleast := (primitive_iff_local_isLeast hc m hm χ).mp hprimitive v
  have hzero : 0 ∈ {k : ℕ | ∀ t : (v.adicCompletion F)ˣ,
      t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k →
        RayClassBridge.ideleClassCharacter F hc m hm χ
          (IdeleGroup.finitePlaceIdeleClass v t) = 1} := by
    intro t ht
    rw [ClassFieldTheory.rayLocalHigherUnitGroup_zero] at ht
    rw [hχ]
    exact hunram t ht
  have he := Nat.eq_zero_of_le_zero (hleast.2 hzero)
  intro hdiv
  have hsupport : v ∈ (RayClassBridge.narrowIdealModulus F m hm).finitePart.support := by
    change v ∈ (↑(RayClassBridge.narrowIdealModulus F m hm).finitePart.support :
      Set (HeightOneSpectrum (𝓞 F)))
    rw [RayClassBridge.narrowIdealModulus_support]
    exact hdiv
  exact (Finsupp.mem_support_iff.mp hsupport) he

end DedekindZetaZeroFree.PrimitiveRay

end
