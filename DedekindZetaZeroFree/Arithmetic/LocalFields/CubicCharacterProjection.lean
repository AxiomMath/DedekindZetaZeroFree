module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.CubicCharacterExpansion
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RootParameterCompactPicture

@[expose] public section

section

namespace DedekindZetaZeroFree.KPRankOneCubicCharacterProducts

open CubicCharacters
 lemma mu_cube (z : Mu3) : z ^ 3 = 1 := by
  apply Subtype.ext
  exact (mem_rootsOfUnity 3 _).mp z.property

 noncomputable def quotientChars (A : Type*) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] :
    ((A ⧸ cubes A) →ₜ* Mu3) ≃* (A →ₜ* Mu3) := by
  let mk : A →ₜ* (A ⧸ cubes A) :=
    ⟨QuotientGroup.mk' (cubes A), QuotientGroup.continuous_mk⟩
  have kills (f : A →ₜ* Mu3) : cubes A ≤ f.toMonoidHom.ker := by
    rintro x ⟨y, rfl⟩
    change f (y ^ 3) = 1
    rw [map_pow, mu_cube]
  let lift (f : A →ₜ* Mu3) : (A ⧸ cubes A) →ₜ* Mu3 :=
    ⟨QuotientGroup.lift (cubes A) f.toMonoidHom (kills f),
      (QuotientGroup.isQuotientMap_mk (cubes A)).continuous_iff.mpr f.continuous⟩
  exact
    { toFun := fun f => f.comp mk
      invFun := lift
      left_inv := fun f => by
        ext q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (cubes A) q
        rfl
      right_inv := fun f => by ext x; rfl
      map_mul' := fun f g => by ext x; rfl }

end DedekindZetaZeroFree.KPRankOneCubicCharacterProducts

end

section

namespace DedekindZetaZeroFree.KPRankOneCubicProjection

open scoped ValuativeRel
open MeasureTheory ValuativeRel

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]

abbrev D := KPLocalTorus.CubeClasses Kˣ

abbrev X := D K →ₜ* CubicCharacters.Mu3

abbrev DU := (𝒪[K])ˣ ⧸ CubicCharacters.cubes (𝒪[K])ˣ

def N : ℕ := 9 * KPLocalTorus.inverseThreeModule K

def unitInclusion : (𝒪[K])ˣ →* Kˣ :=
  Units.map (𝒪[K]).subtype.toMonoidHom

def eta (z : ℂˣ) (y : Kˣ) : ℂˣ :=
  z ^ KPCubicExpansion.valuationExponent K y

private lemma cubes_closed : IsClosed (CubicCharacters.cubes Kˣ : Set Kˣ) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have hc : IsClosed (Set.range fun x : K => x ^ 3) := (isClosedMap_pow (R := K) 3).isClosed_range
  have he : (CubicCharacters.cubes Kˣ : Set Kˣ) =
      Units.val ⁻¹' (Set.range fun x : K => x ^ 3) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : K), (Units.val_pow_eq_pow_val x 3).symm⟩
    · rintro ⟨x, hx⟩
      have hn : x ≠ 0 := by
        intro h
        exact Units.ne_zero y (by simpa [h] using hx.symm)
      refine ⟨Units.mk0 x hn, ?_⟩
      apply Units.ext
      exact hx
  rw [he]
  exact hc.preimage Units.continuous_val

private lemma class_pow (q : D K) : q ^ 3 = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CubicCharacters.cubes Kˣ) q
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩

theorem local_character_count (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    DiscreteTopology (D K) ∧ Finite (D K) ∧
    Nat.card (D K) = N K ∧ Finite (X K) ∧ Nat.card (X K) = N K := by
  letI : Finite (D K) := KPLocalTorus.finite_cubeClasses K ζ hζ
  letI : (CubicCharacters.cubes Kˣ).FiniteIndex := ⟨Nat.ne_of_gt (Nat.card_pos (α := D K))⟩
  letI : DiscreteTopology (D K) := QuotientGroup.discreteTopology
    ((CubicCharacters.cubes Kˣ).isOpen_of_isClosed_of_finiteIndex (cubes_closed K))
  let e : X K ≃ (D K →* ℂˣ) :=
    { toFun := fun χ => (rootsOfUnity 3 ℂ).subtype.comp χ.toMonoidHom
      invFun := fun f => ⟨f.codRestrict (rootsOfUnity 3 ℂ) (fun q => by
        rw [mem_rootsOfUnity, ← map_pow, class_pow, map_one]), continuous_of_discreteTopology⟩
      left_inv := fun χ => by ext q; rfl
      right_inv := fun f => by ext q; rfl }
  letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (D K)) :=
    HasEnoughRootsOfUnity.of_dvd ℂ (Monoid.exponent_dvd_of_forall_pow_eq_one (class_pow K))
  letI : Finite (X K) := Finite.of_injective e e.injective
  have hd := KPLocalTorus.card_cubeClasses K ζ hζ
  refine ⟨inferInstance, inferInstance, hd, inferInstance, ?_⟩
  exact (Nat.card_congr e).trans
    ((CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (D K) ℂ).trans hd)

variable [MeasurableSpace K] [BorelSpace K]

theorem unit_mass (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx (𝒪[K] : Set K) = ENNReal.ofReal m) :
    KPCubicHaar.multiplicativeHaar K dx
        {x : Kˣ | (x : K) ∈ 𝒪[K] ∧ ((x⁻¹ : Kˣ) : K) ∈ 𝒪[K]} =
      ENNReal.ofReal (m * (1 - (KPCubicUnitIndices.residueCard K : ℝ)⁻¹)) := by
  exact (kp_rankone_cubic_haar_power_measure K dx m hm hvol).2

local instance : BorelSpace Kˣ := ⟨by
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  calc
    MeasurableSpace.comap Units.val ‹MeasurableSpace K› =
        MeasurableSpace.comap Units.val (borel K) :=
      congrArg (MeasurableSpace.comap Units.val)
        (BorelSpace.measurable_eq (α := K))
    _ = borel Kˣ := by
      rw [(Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]⟩

theorem eta_uniformizer_coordinates (z : ℂˣ) (π : Kˣ)
    (hπ : valuation K (π : K) = ValuativeRel.uniformizer K)
    (j : ℤ) (u : (𝒪[K])ˣ) :
    eta K z (π ^ j * unitInclusion K u) = z ^ j := by
  rw [eta, KPCubicExpansion.valuationExponent_mul,
    KPCubicExpansion.valuationExponent_zpow,
    KPCubicExpansion.valuationExponent_uniformizer π hπ]
  change z ^ (j * 1 + KPCubicExpansion.valuationExponent K
    (Units.map (𝒪[K]).subtype.toMonoidHom u)) = z ^ j
  rw [KPCubicExpansion.valuationExponent_unit]
  simp

end
end DedekindZetaZeroFree.KPRankOneCubicProjection

end
