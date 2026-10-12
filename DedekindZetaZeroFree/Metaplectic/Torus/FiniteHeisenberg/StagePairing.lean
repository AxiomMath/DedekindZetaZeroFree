module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenberg.CenterCharactersAndCommutators

@[expose] public section

open scoped NumberField Classical commutatorElement
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TorusFiniteHeisenberg
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusFiniteStages TorusFiniteCenterQuotient
variable (C : CompatibleModelData F ζ hζ) (L : Level F ζ hζ C)

local instance : Fintype (symplecticQuotient F ζ hζ C L) :=
  @Fintype.ofFinite _ (quotient_finite F ζ hζ C L)

private theorem root_four (ε : rootsOfUnity 3 F) : ε ^ 4 = ε := by
  have hp : ε ^ 3 = 1 := by apply Subtype.ext; exact ε.property
  rw [pow_succ, hp, one_mul]

private theorem stage_exponent_three (x : symplecticQuotient F ζ hζ C L) : x ^ 3 = 1 := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
  have hd : d.val ^ 3 = 1 := by
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
      (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F)) d.val
    rw [← hy, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
  have hd' : d ^ 3 = 1 := Subtype.ext hd
  rw [← QuotientGroup.mk'_apply, ← map_pow, hd', map_one]

 def actualPairing : symplecticQuotient F ζ hζ C L →*
    (symplecticQuotient F ζ hζ C L →* rootsOfUnity 3 ℂ) := by
  let b := stagePairing F ζ hζ C L
  have hb := finite_symplectic F ζ hζ C L
  have h1 (x) : b x 1 = 1 := by
    have hh := hb.2.1 x 1 1
    simpa only [mul_one, mul_eq_left] using hh.symm
  have h2 (y) : b 1 y = 1 := by
    have hh := hb.1 1 1 y
    simpa only [mul_one, mul_eq_left] using hh.symm
  exact
    { toFun := fun x =>
        { toFun := fun y => ordinaryRoots F ζ hζ (b x y ^ 4)
          map_one' := by rw [h1, one_pow, map_one]
          map_mul' := by intro y z; dsimp only [b]; rw [hb.2.1, mul_pow, map_mul] }
      map_one' := by
        apply MonoidHom.ext
        intro y
        change ordinaryRoots F ζ hζ (b 1 y ^ 4) = 1
        rw [h2, one_pow, map_one]
      map_mul' := by
        intro x y
        apply MonoidHom.ext
        intro z
        change ordinaryRoots F ζ hζ (b (x * y) z ^ 4) =
          ordinaryRoots F ζ hζ (b x z ^ 4) * ordinaryRoots F ζ hζ (b y z ^ 4)
        dsimp only [b]
        rw [hb.1, mul_pow, map_mul] }

private theorem actualPairing_injective : Function.Injective (actualPairing F ζ hζ C L) := by
  intro x y he
  have hb := finite_symplectic F ζ hζ C L
  have hn : ∀ z, stagePairing F ζ hζ C L (x / y) z = 1 := by
    intro z
    have hv := congrArg (fun f : symplecticQuotient F ζ hζ C L →* rootsOfUnity 3 ℂ => f z) he
    change ordinaryRoots F ζ hζ (stagePairing F ζ hζ C L x z ^ 4) =
      ordinaryRoots F ζ hζ (stagePairing F ζ hζ C L y z ^ 4) at hv
    have heq := ordinaryRoots_injective F ζ hζ hv
    rw [root_four, root_four] at heq
    have hh := hb.1 (x / y) y z
    rw [div_mul_cancel, heq] at hh
    exact (mul_right_cancel (hh.symm.trans (one_mul _).symm))
  exact div_eq_one.mp (hb.2.2.2 _ hn)

private theorem actualPairing_perfect : Function.Bijective (actualPairing F ζ hζ C L) := by
  let V := symplecticQuotient F ζ hζ C L
  let A := V →* rootsOfUnity 3 ℂ
  letI : Finite V := quotient_finite F ζ hζ C L
  let n := Monoid.exponent V
  letI : NeZero n := ⟨Monoid.exponent_ne_zero_of_finite⟩
  letI : HasEnoughRootsOfUnity ℂ n := HasEnoughRootsOfUnity.of_card_le
    (by rw [Complex.card_rootsOfUnity])
  have hcard : Nat.card (V →* ℂˣ) = Nat.card V :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity V ℂ
  let φ : A → V →* ℂˣ := fun f => (rootsOfUnity 3 ℂ).subtype.comp f
  have hφ : Function.Injective φ := by
    intro f g he
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun h : V →* ℂˣ => h x) he
  letI : Finite (V →* ℂˣ) := Finite.of_equiv V
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity V ℂ).some.toEquiv.symm
  letI : Finite A := Finite.of_injective φ hφ
  letI : Fintype A := Fintype.ofFinite _
  have hle : Fintype.card A ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← hcard]
    exact Nat.card_le_card_of_injective φ hφ
  refine ⟨actualPairing_injective F ζ hζ C L, ?_⟩
  by_contra hn
  have hh := Fintype.card_lt_of_injective_not_surjective (actualPairing F ζ hζ C L)
    (actualPairing_injective F ζ hζ C L) hn
  exact (not_lt_of_ge hle) hh

theorem actual_finite_heisenberg :
    ∃ T : FinitePolarization.HeisenbergData
        (H F ζ hζ C L) (symplecticQuotient F ζ hζ C L),
      ∃ hC : T.C = center F ζ hζ C L,
        T.π = projection F ζ hζ C L ∧
        (∀ z : T.C, T.ω z = centerCharacter F ζ hζ C L
          ⟨z.val, hC ▸ z.property⟩) ∧
        ∀ x y, T.pairing x y = ordinaryRoots F ζ hζ
          (stagePairing F ζ hζ C L x y ^ 4) := by
  let T : FinitePolarization.HeisenbergData (H F ζ hζ C L) (symplecticQuotient F ζ hζ C L) :=
    { C := center F ζ hζ C L
      central := center_central F ζ hζ C L
      π := projection F ζ hζ C L
      quotient_surjective := projection_surjective F ζ hζ C L
      quotient_kernel := projection_kernel F ζ hζ C L
      exponent_three := stage_exponent_three F ζ hζ C L
      ω := centerCharacter F ζ hζ C L
      faithful := centerCharacter_faithful F ζ hζ C L
      pairing := actualPairing F ζ hζ C L
      alternating := by
        intro x
        change ordinaryRoots F ζ hζ (stagePairing F ζ hζ C L x x ^ 4) = 1
        rw [(finite_symplectic F ζ hζ C L).2.2.1, one_pow, map_one]
      perfect := actualPairing_perfect F ζ hζ C L
      commutator_mem := H_commutator_mem F ζ hζ C L
      commutator_pairing := H_commutator_character F ζ hζ C L }
  exact ⟨T, rfl, rfl, (by intro z; rfl), (by intro x y; rfl)⟩

end
end DedekindZetaZeroFree.TorusFiniteHeisenberg
