module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ModulusIdeal

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
open GlobalClassFieldTheory.GlobalClassFields

noncomputable section
namespace DedekindZetaZeroFree.PrimitiveRay

variable {F : Type} [Field F] [NumberField F]

theorem conductorKernel (hc : NumberField.IsTotallyComplex F)
    (Φ : IdeleClassGroup F →ₜ* ℂˣ)
    (ho : ∃ n : ℕ, 0 < n ∧ ∀ c : IdeleClassGroup F, Φ c ^ n = 1) :
    ∃ (hclosed : IsClosed ((Φ.toMonoidHom.ker : Subgroup (IdeleClassGroup F)) :
        Set (IdeleClassGroup F)))
      (hfinite : Φ.toMonoidHom.ker.FiniteIndex)
      (m : Ideal (𝓞 F)) (hm : m ≠ ⊥),
      m = modulusIdeal (by
        letI := hfinite
        exact (ConductorialSubgroup.ofClosedFiniteIndex Φ.toMonoidHom.ker
          hclosed).narrowFiniteConductor) ∧
      (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal
        F (RayClassBridge.narrowIdealModulus F m hm)).congruenceSubgroup ≤
          Φ.toMonoidHom.ker ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        IsLeast {k : ℕ | ∀ t : (v.adicCompletion F)ˣ,
          t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k →
            Φ (IdeleGroup.finitePlaceIdeleClass v t) = 1}
          ((RayClassBridge.narrowIdealModulus F m hm).finitePart v)) := by
  classical
  obtain ⟨n, hn, hpow⟩ := ho
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hclosed : IsClosed ((Φ.toMonoidHom.ker : Subgroup (IdeleClassGroup F)) :
      Set (IdeleClassGroup F)) := by
    exact isClosed_singleton.preimage Φ.continuous
  have hrange : Φ.toMonoidHom.range ≤ rootsOfUnity n ℂ := by
    rintro _ ⟨c, rfl⟩
    exact (mem_rootsOfUnity n (Φ c)).mpr (hpow c)
  letI : Finite Φ.toMonoidHom.range :=
    Finite.of_injective (fun x : Φ.toMonoidHom.range =>
      (⟨x.val, hrange x.property⟩ : rootsOfUnity n ℂ))
      (fun x y h => Subtype.ext (congrArg (fun z : rootsOfUnity n ℂ => (z : ℂˣ)) h))
  have hfinite : Φ.toMonoidHom.ker.FiniteIndex := inferInstance
  letI := hfinite
  let H := ConductorialSubgroup.ofClosedFiniteIndex Φ.toMonoidHom.ker hclosed
  refine ⟨hclosed, hfinite, modulusIdeal H.narrowFiniteConductor,
    modulusIdeal_ne_bot _, rfl, ?_, ?_⟩
  · obtain ⟨a, ha, he⟩ := H.exists_definingModulus_finitePart_eq_narrowFiniteConductor
    letI : IsEmpty (ClassFieldTheory.RayClassRealPlace F) :=
      ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
        (hc.isComplex v.val)) v.property⟩
    have heq : ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
        (RayClassBridge.narrowIdealModulus F (modulusIdeal H.narrowFiniteConductor)
          (modulusIdeal_ne_bot _)) = a := by
      apply RayClass.Modulus.ext
      · exact (modulusIdeal_M _).trans he.symm
      · exact Subsingleton.elim _ _
    rw [heq]
    exact ha
  · intro v
    change IsLeast {k : ℕ | ∀ t : (v.adicCompletion F)ˣ,
      t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k →
        Φ (IdeleGroup.finitePlaceIdeleClass v t) = 1}
      ((M F (modulusIdeal H.narrowFiniteConductor) (modulusIdeal_ne_bot _)).finitePart v)
    rw [modulusIdeal_M,
      H.narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent]
    constructor
    · intro t ht
      apply H.narrowFiniteLocalConductorExponent_spec v
      refine ⟨t, ?_, rfl⟩
      rwa [← ClassFieldTheory.rayLocalHigherUnitGroup_eq_rayClass]
    · intro k hk
      apply H.narrowFiniteLocalConductorExponent_le v
      rintro _ ⟨t, ht, rfl⟩
      change Φ (IdeleGroup.finitePlaceIdeleClass v t) = 1
      apply hk t
      rwa [ClassFieldTheory.rayLocalHigherUnitGroup_eq_rayClass]

end DedekindZetaZeroFree.PrimitiveRay

end
