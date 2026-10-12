module

public import ClassFieldTheory.All
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.FiniteCharacters

@[expose] public section

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.RayClassBridge

def ideleClassCharacter
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    IdeleClassGroup F →* ℂˣ :=
  (rayCharacter F hcomplex 𝔪 h𝔪 η).comp
    ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
        F (narrowIdealModulus F 𝔪 h𝔪)).symm.toMonoidHom.comp
      (QuotientGroup.mk'
        (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
          F (narrowIdealModulus F 𝔪 h𝔪)).congruenceSubgroup))

theorem ideleClassCharacter_continuous
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    Continuous (ideleClassCharacter F hcomplex 𝔪 h𝔪 η) := by
  let M := ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
    F (narrowIdealModulus F 𝔪 h𝔪)
  letI : DiscreteTopology (RayClass.RayClassGroup M) :=
    QuotientGroup.discreteTopology (RayClass.isOpen_congruenceSubgroup M)
  exact (continuous_of_discreteTopology (f := fun c : RayClass.RayClassGroup M =>
    rayCharacter F hcomplex 𝔪 h𝔪 η
      ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
        F (narrowIdealModulus F 𝔪 h𝔪)).symm c))).comp
    QuotientGroup.continuous_mk

theorem ideleClassCharacter_exponent_pos
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    0 < Nat.card (ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪)) := by
  exact rayClassGroup_card_pos F 𝔪 h𝔪

theorem ideleClassCharacter_pow_card
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (c : IdeleClassGroup F) :
    ideleClassCharacter F hcomplex 𝔪 h𝔪 η c ^
      Nat.card (ClassFieldTheory.RayClassGroup (narrowIdealModulus F 𝔪 h𝔪)) = 1 := by
  exact rayCharacter_pow_card F hcomplex 𝔪 h𝔪 η _

@[simp] theorem ideleClassCharacter_norm
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (c : IdeleClassGroup F) :
    ‖(ideleClassCharacter F hcomplex 𝔪 h𝔪 η c : ℂ)‖ = 1 := by
  exact rayCharacter_norm F hcomplex 𝔪 h𝔪 η _

theorem ideleClassCharacter_congruenceSubgroup_le_ker
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
      F (narrowIdealModulus F 𝔪 h𝔪)).congruenceSubgroup ≤
        (ideleClassCharacter F hcomplex 𝔪 h𝔪 η).ker := by
  intro c hc
  change rayCharacter F hcomplex 𝔪 h𝔪 η
    ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
      F (narrowIdealModulus F 𝔪 h𝔪)).symm
      (QuotientGroup.mk' _ c)) = 1
  simp only [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).mpr hc, map_one]

theorem ideleClassCharacter_finitePrimeIdele
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support) :
    (ideleClassCharacter F hcomplex 𝔪 h𝔪 η
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
        (IdeleGroup.finitePrimeIdele v)) : ℂ) = η v.asIdeal := by
  change (rayCharacter F hcomplex 𝔪 h𝔪 η
    ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele
      F (narrowIdealModulus F 𝔪 h𝔪)).symm (QuotientGroup.mk' _
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
          (IdeleGroup.finitePrimeIdele v)))) : ℂ) = _
  rw [← ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime
    F (narrowIdealModulus F 𝔪 h𝔪) v hv, MulEquiv.symm_apply_apply]
  have hnot : ¬ 𝔪 ≤ v.asIdeal := by
    simpa only [← Finset.mem_coe, narrowIdealModulus_support, Set.mem_setOf_eq] using hv
  have hcop : v.asIdeal ⊔ 𝔪 = ⊤ := by
    exact v.isMaximal.out.2 _
      (lt_of_le_of_ne le_sup_left (fun h => hnot (h ▸ le_sup_right)))
  have heq : ClassFieldTheory.rayClassOfFinitePrime (narrowIdealModulus F 𝔪 h𝔪) v hv =
      integralRayClass F 𝔪 h𝔪 v.asIdeal v.ne_bot hcop := rfl
  rw [heq]
  exact rayCharacter_integral F hcomplex 𝔪 h𝔪 η v.asIdeal v.ne_bot hcop

theorem ideleClassCharacter_finitePlaceIdeleClass_higherUnit
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ)
    (hu : u ∈ ClassFieldTheory.rayLocalHigherUnitGroup v
      ((narrowIdealModulus F 𝔪 h𝔪).finitePart v)) :
    ideleClassCharacter F hcomplex 𝔪 h𝔪 η
      (IdeleGroup.finitePlaceIdeleClass v u) = 1 := by
  apply ideleClassCharacter_congruenceSubgroup_le_ker F hcomplex 𝔪 h𝔪 η
  apply RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup
    (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
      F (narrowIdealModulus F 𝔪 h𝔪)) v
  refine ⟨u, ?_, rfl⟩
  change u ∈ RayClass.localHigherUnitGroup v ((narrowIdealModulus F 𝔪 h𝔪).finitePart v)
  rwa [ClassFieldTheory.rayLocalHigherUnitGroup_eq_rayClass] at hu

theorem ideleClassCharacter_finitePlaceIdeleClass_unit_of_not_dvd
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    (u : (v.adicCompletion F)ˣ) (hu : u ∈ (v.adicCompletionIntegers F).units) :
    ideleClassCharacter F hcomplex 𝔪 h𝔪 η
      (IdeleGroup.finitePlaceIdeleClass v u) = 1 := by
  apply ideleClassCharacter_finitePlaceIdeleClass_higherUnit F hcomplex 𝔪 h𝔪 η
  have hv' : v ∉ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support := by
    simpa only [← Finset.mem_coe, narrowIdealModulus_support, Set.mem_setOf_eq] using hv
  rw [Finsupp.notMem_support_iff.mp hv',
    ClassFieldTheory.rayLocalHigherUnitGroup_eq_rayClass]
  simpa only [RayClass.localHigherUnitGroup_zero] using hu

theorem ideleClassCharacter_infinitePlaceIdeleClass
    (F : Type) [Field F] [NumberField F] (hcomplex : NumberField.IsTotallyComplex F)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (w : NumberField.InfinitePlace F) (z : w.Completionˣ) :
    ideleClassCharacter F hcomplex 𝔪 h𝔪 η
      (IdeleGroup.infinitePlaceIdeleClass w z) = 1 := by
  apply ideleClassCharacter_congruenceSubgroup_le_ker F hcomplex 𝔪 h𝔪 η
  let M := ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
    F (narrowIdealModulus F 𝔪 h𝔪)
  change IdeleGroup.infinitePlaceIdeleClass w z ∈ M.congruenceSubgroup
  rw [RayClass.Modulus.congruenceSubgroup]
  refine ⟨IdeleGroup.infinitePlaceIdele w z, Subgroup.mem_sup_left ?_, rfl⟩
  rw [RayClass.Modulus.mem_ideleCongruenceSubgroup_iff]
  constructor
  · rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local]
    intro w'
    rw [RayClass.Modulus.localInfiniteCongruenceSubgroup_of_not_isReal M w'
      (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hcomplex.isComplex w'))]
    trivial
  · exact (RayClass.finiteCongruenceSubgroup M.finitePart).one_mem

end DedekindZetaZeroFree.RayClassBridge

end
