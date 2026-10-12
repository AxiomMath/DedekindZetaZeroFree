module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralRepresentatives
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescent
public import DedekindZetaZeroFree.Theta.Profiles.RayThetaKernelsAndZeroModes

@[expose] public section

noncomputable section

open scoped NumberField
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]
variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)

structure RayThetaRepresentatives where
  coset : RayIdealClass F m hm → RayCoset.Data F
  modulus_eq : ∀ c, (coset c).m = m
  inverse_class : ∀ c, rayIdealClass F m hm (coset c).a = some (c⁻¹)

def chooseRayThetaRepresentatives : RayThetaRepresentatives F m hm := by
  classical
  let a := fun c : RayIdealClass F m hm =>
    Classical.choose (exists_integral_inverse_rayIdealClass F m hm c)
  have ha : ∀ c, a c ≠ ⊥ ∧ a c ⊔ m = ⊤ ∧
      rayIdealClass F m hm (a c) = some (c⁻¹) :=
    fun c => Classical.choose_spec (exists_integral_inverse_rayIdealClass F m hm c)
  let b := fun c : RayIdealClass F m hm =>
    Classical.choose (exists_ray_congruence_basepoint F m (a c) (ha c).2.1)
  have hb : ∀ c, b c ∈ a c ∧ b c - 1 ∈ m :=
    fun c => Classical.choose_spec
      (exists_ray_congruence_basepoint F m (a c) (ha c).2.1)
  exact
    { coset := fun c =>
        { m := m
          modulus_ne_bot := hm
          a := a c
          ideal_ne_bot := (ha c).1
          coprime := (ha c).2.1
          b := b c
          basepoint_mem := (hb c).1
          basepoint_congruent_one := (hb c).2 }
      modulus_eq := fun _ => rfl
      inverse_class := fun c => (ha c).2.2 }

structure RayCharacterData (η : DedekindZetaZeroFree.RayClassCharacter F m) where
  ψ : RayIdealClass F m hm →* ℂ
  descent : ∀ I : Ideal (𝓞 F), η I =
    match rayIdealClass F m hm I with
    | none => 0
    | some c => ψ c
  principal_iff : η.IsPrincipal ↔ ψ = 1

variable {F m hm}

def chooseRayCharacterData (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    RayCharacterData F m hm η :=
  { ψ := Classical.choose (rayCharacterDescent F m hm η)
    descent := (Classical.choose_spec (rayCharacterDescent F m hm η)).1
    principal_iff := (Classical.choose_spec (rayCharacterDescent F m hm η)).2 }

def conductorNorm (F : Type) [Field F] [NumberField F] (m : Ideal (𝓞 F)) : ℝ :=
  (|NumberField.discr F| : ℝ) * (Ideal.absNorm m : ℝ)

def conductorScale (F : Type) [Field F] [NumberField F] (m : Ideal (𝓞 F)) : ℝ :=
  Real.sqrt (conductorNorm F m)

theorem conductorNorm_pos (hm : m ≠ ⊥) : 0 < conductorNorm F m := by
  unfold conductorNorm
  apply mul_pos
  · exact_mod_cast (abs_pos.mpr (NumberField.discr_ne_zero F))
  · exact_mod_cast (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hm))

theorem conductorScale_pos (hm : m ≠ ⊥) : 0 < conductorScale F m := by
  exact Real.sqrt_pos.mpr (conductorNorm_pos hm)

theorem conductorScale_sq (hm : m ≠ ⊥) :
    conductorScale F m ^ 2 = conductorNorm F m := by
  exact Real.sq_sqrt (le_of_lt (conductorNorm_pos hm))

def normalizedRayTheta (D : RayThetaRepresentatives F m hm)
    (ψ : RayIdealClass F m hm →* ℂ) (t : ℝ) : ℂ := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  exact (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
    ∑ c : RayIdealClass F m hm,
      ψ c * RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m)

def normalizedRayDualTheta (D : RayThetaRepresentatives F m hm)
    (ψ : RayIdealClass F m hm →* ℂ) (t : ℝ) : ℂ := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  exact (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
    (conductorScale F m : ℂ) *
    ∑ c : RayIdealClass F m hm,
      ψ c * RayTheta.gδDual (D.coset c) ∅ (conductorScale F m * t)

def normalizedRayConjugateTheta (D : RayThetaRepresentatives F m hm)
    (ψ : RayIdealClass F m hm →* ℂ) (t : ℝ) : ℂ := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  exact (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
    ∑ c : RayIdealClass F m hm,
      (starRingEnd ℂ) (ψ c) * RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m)

end DedekindZetaZeroFree.Hecke.Theta

end
