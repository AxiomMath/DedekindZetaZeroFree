module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IdelicCharacterLift
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IntegralCharacters

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain
open DedekindZetaZeroFree
open GlobalClassFieldTheory.GlobalClassFields
noncomputable section
namespace DedekindZetaZeroFree.PrimitiveRay
variable {F : Type} [Field F] [NumberField F]

def kernelConductor (hc : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F))
    (hm : m ≠ ⊥) (η : RayClassCharacter F m) : ConductorialSubgroup F :=
  ⟨(RayClassBridge.ideleClassCharacter F hc m hm η).ker,
    ⟨ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
      (RayClassBridge.narrowIdealModulus F m hm),
      RayClassBridge.ideleClassCharacter_congruenceSubgroup_le_ker F hc m hm η⟩⟩

def modulusIdeal (s : HeightOneSpectrum (𝓞 F) →₀ ℕ) : Ideal (𝓞 F) :=
  ∏ v ∈ s.support, v.asIdeal ^ s v

theorem modulusIdeal_ne_bot (s : HeightOneSpectrum (𝓞 F) →₀ ℕ) : modulusIdeal s ≠ ⊥ := by
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ v.ne_bot)

theorem modulusIdeal_count (s : HeightOneSpectrum (𝓞 F) →₀ ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v (modulusIdeal s : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = s v := by
  unfold modulusIdeal
  change FractionalIdeal.count F v ((FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 F)) F) (∏ w ∈ s.support, w.asIdeal ^ s w)) = _
  rw [map_prod, FractionalIdeal.count_prod]
  · change (∑ i ∈ s.support, FractionalIdeal.count F v ((i.asIdeal ^ s i : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) = _
    simp only [FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow,
      FractionalIdeal.count_maximal]
    by_cases hv : v ∈ s.support
    · rw [Finset.sum_eq_single_of_mem v hv]
      · simp
      · intro w _ hw
        simp [hw]
    · rw [Finsupp.notMem_support_iff.mp hv]
      apply Finset.sum_eq_zero
      intro w hw
      have hne : w ≠ v := fun h => hv (h ▸ hw)
      simp [hne]
  · intro w _
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ w.ne_bot)

theorem modulusIdeal_M (s : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    (M F (modulusIdeal s) (modulusIdeal_ne_bot s)).finitePart = s := by
  ext v
  change Int.toNat (FractionalIdeal.count F v (modulusIdeal s : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) = s v
  rw [modulusIdeal_count, Int.toNat_natCast]

theorem modulusIdeal_le (s : HeightOneSpectrum (𝓞 F) →₀ ℕ) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (hs : s ≤ (M F m hm).finitePart) : m ≤ modulusIdeal s := by
  apply (M_le_iff F _ _ (modulusIdeal_ne_bot s) hm).mp
  rw [ClassFieldTheory.RayClassModulus.le_iff]
  exact ⟨by rw [modulusIdeal_M]; exact fun v => hs v, by simp⟩

theorem kernel_defining (hc : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F))
    (hm : m ≠ ⊥) (η : RayClassCharacter F m) :
    (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
      (M F (modulusIdeal (kernelConductor hc m hm η).narrowFiniteConductor)
        (modulusIdeal_ne_bot _))).congruenceSubgroup ≤
      (RayClassBridge.ideleClassCharacter F hc m hm η).ker := by
  letI := hc
  let H := kernelConductor hc m hm η
  obtain ⟨n, hn, he⟩ := H.exists_definingModulus_finitePart_eq_narrowFiniteConductor
  letI : IsEmpty (ClassFieldTheory.RayClassRealPlace F) :=
    ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hc.isComplex v.val)) v.property⟩
  have hMn : ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
      (M F (modulusIdeal H.narrowFiniteConductor) (modulusIdeal_ne_bot _)) = n := by
    apply RayClass.Modulus.ext
    · exact (modulusIdeal_M _).trans he.symm
    · exact Subsingleton.elim _ _
  change (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
      (M F (modulusIdeal H.narrowFiniteConductor) (modulusIdeal_ne_bot _))).congruenceSubgroup ≤ H.1
  rw [hMn]
  exact hn

theorem kernel_bound (hc : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F))
    (hm : m ≠ ⊥) (η : RayClassCharacter F m) :
    m ≤ modulusIdeal (kernelConductor hc m hm η).narrowFiniteConductor := by
  apply modulusIdeal_le _ m hm
  exact (kernelConductor hc m hm η).narrowFiniteConductor_le
    (RayClassBridge.ideleClassCharacter_congruenceSubgroup_le_ker F hc m hm η)

theorem localTrivial (hc : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F))
    (hm : m ≠ ⊥) (η : RayClassCharacter F m) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ)
    (hu : u ∈ ClassFieldTheory.rayLocalHigherUnitGroup v
      ((kernelConductor hc m hm η).narrowFiniteConductor v)) :
    RayClassBridge.ideleClassCharacter F hc m hm η
      (IdeleGroup.finitePlaceIdeleClass v u) = 1 := by
  apply (kernelConductor hc m hm η).narrowFiniteLocalConductorExponent_spec v
  refine ⟨u, ?_, rfl⟩
  rw [← ClassFieldTheory.rayLocalHigherUnitGroup_eq_rayClass,
    ← (kernelConductor hc m hm η).narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent]
  exact hu
end DedekindZetaZeroFree.PrimitiveRay

end
