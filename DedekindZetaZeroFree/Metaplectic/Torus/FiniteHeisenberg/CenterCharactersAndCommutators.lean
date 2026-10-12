module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenberg.CubicCenterQuotient
public import DedekindZetaZeroFree.Metaplectic.Torus.CubicPhaseCharacter

@[expose] public section

open scoped NumberField Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TorusFiniteCenterQuotient

noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPGlobalTorusFiniteStages

variable (C : CompatibleModelData F ζ hζ) (L : Level F ζ hζ C)

theorem centerCharacter_cube (z : center F ζ hζ C L) :
    centerCharacter F ζ hζ C L z ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := phaseToCenter_surjective F ζ hζ C L z
  rw [centerCharacter_phase]
  exact phaseCharacter_cube F ζ hζ C L k

def ordinaryRoots : rootsOfUnity 3 F →* rootsOfUnity 3 ℂ where
  toFun ε := ⟨KPGlobalTorusFunctionData.iota F ζ hζ ε, by
    change KPGlobalTorusFunctionData.iota F ζ hζ ε ^ 3 = 1
    rw [← map_pow]
    have hp : ε ^ 3 = 1 := by apply Subtype.ext; exact ε.property
    rw [hp, map_one]⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ x y

theorem ordinaryRoots_injective : Function.Injective (ordinaryRoots F ζ hζ) := by
  intro ε δ he
  have hi : KPGlobalTorusFunctionData.iota F ζ hζ ε = KPGlobalTorusFunctionData.iota F ζ hζ δ :=
    congrArg (fun z : rootsOfUnity 3 ℂ => (z : ℂˣ)) he
  have h6 := KPLocalCover.coefficientEmbedding_injective F ζ hζ hi
  exact Subtype.ext (congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) h6)

theorem ordinaryRoots_surjective : Function.Surjective (ordinaryRoots F ζ hζ) := by
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity 3 ℂ) := Fintype.ofFinite _
  have hF : Nat.card (rootsOfUnity 3 F) = 3 :=
    (hζ.pow (by norm_num : 0 < 12) (by norm_num : 12 = 4 * 3)).card_rootsOfUnity
  have hcard : Fintype.card (rootsOfUnity 3 F) = Fintype.card (rootsOfUnity 3 ℂ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, Complex.card_rootsOfUnity]
  exact ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨ordinaryRoots_injective F ζ hζ, hcard⟩).2

theorem center_eq_cubicCenter : center F ζ hζ C L = cubicCenter F ζ hζ C L := by
  apply le_antisymm _ (cubicCenter_le_center F ζ hζ C L)
  intro z hz
  let cz : center F ζ hζ C L := ⟨z, hz⟩
  let εC : rootsOfUnity 3 ℂ := ⟨centerCharacter F ζ hζ C L cz, centerCharacter_cube F ζ hζ C L cz⟩
  obtain ⟨ε, hε⟩ := ordinaryRoots_surjective F ζ hζ εC
  have hchar : centerCharacter F ζ hζ C L (phaseToCenter F ζ hζ C L (rootPhase F ζ hζ C L ε)) =
      centerCharacter F ζ hζ C L cz := by
    rw [centerCharacter_phase, rootPhase_character]
    exact congrArg (fun t : rootsOfUnity 3 ℂ => (t : ℂˣ)) hε
  have he := centerCharacter_faithful F ζ hζ C L hchar
  exact ⟨ε, congrArg (fun t : center F ζ hζ C L => (t : H F ζ hζ C L)) he⟩

def centerEquiv : rootsOfUnity 3 F ≃* center F ζ hζ C L :=
  (cubicCenterEquiv F ζ hζ C L).trans
    (MulEquiv.subgroupCongr (center_eq_cubicCenter F ζ hζ C L).symm)

instance center_finite : Finite (center F ζ hζ C L) :=
  Finite.of_equiv (rootsOfUnity 3 F) (centerEquiv F ζ hζ C L).toEquiv

instance H_finite : Finite (H F ζ hζ C L) := by
  letI := quotient_finite F ζ hζ C L
  letI : Finite (projection F ζ hζ C L).ker := by
    rw [projection_kernel]
    infer_instance
  letI : Fintype (symplecticQuotient F ζ hζ C L) := Fintype.ofFinite _
  letI : Fintype (projection F ζ hζ C L).ker := Fintype.ofFinite _
  letI : Fintype (H F ζ hζ C L) := Group.fintypeOfKerOfCodom (projection F ζ hζ C L)
  infer_instance

end

end DedekindZetaZeroFree.TorusFiniteCenterQuotient

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TorusFiniteCenterQuotient
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusFiniteStages
variable (C : CompatibleModelData F ζ hζ) (L : Level F ζ hζ C)

theorem centerEquiv_apply (ε : rootsOfUnity 3 F) :
    centerEquiv F ζ hζ C L ε = phaseToCenter F ζ hζ C L (rootPhase F ζ hζ C L ε) := by
  apply Subtype.ext
  rfl

theorem centerEquiv_character (ε : rootsOfUnity 3 F) :
    centerCharacter F ζ hζ C L (centerEquiv F ζ hζ C L ε) =
      KPGlobalTorusFunctionData.iota F ζ hζ ε := by
  rw [centerEquiv_apply, centerCharacter_phase, rootPhase_character]

theorem H_commutator_formula (x y : H F ζ hζ C L) :
    x * y * x⁻¹ * y⁻¹ =
      (centerEquiv F ζ hζ C L (stagePairing F ζ hζ C L
        (projection F ζ hζ C L x) (projection F ζ hζ C L y) ^ 4)).val := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [centerEquiv_apply]
  exact commutator_formula F ζ hζ C L a b

theorem H_commutator_mem (x y : H F ζ hζ C L) :
    x * y * x⁻¹ * y⁻¹ ∈ center F ζ hζ C L := by
  rw [H_commutator_formula]
  exact (centerEquiv F ζ hζ C L _).property

theorem H_commutator_character (x y : H F ζ hζ C L) :
    centerCharacter F ζ hζ C L ⟨x * y * x⁻¹ * y⁻¹, H_commutator_mem F ζ hζ C L x y⟩ =
      KPGlobalTorusFunctionData.iota F ζ hζ (stagePairing F ζ hζ C L
        (projection F ζ hζ C L x) (projection F ζ hζ C L y) ^ 4) := by
  have he : (⟨x * y * x⁻¹ * y⁻¹, H_commutator_mem F ζ hζ C L x y⟩ : center F ζ hζ C L) =
      centerEquiv F ζ hζ C L (stagePairing F ζ hζ C L
        (projection F ζ hζ C L x) (projection F ζ hζ C L y) ^ 4) :=
    Subtype.ext (H_commutator_formula F ζ hζ C L x y)
  rw [he, centerEquiv_character]

end
end DedekindZetaZeroFree.TorusFiniteCenterQuotient

end
