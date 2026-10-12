module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.IndependentReverseImages
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ImageRepresentations
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.VanishingOppositeCompositions
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TameTwistedCoinvariantRank
public import DedekindZetaZeroFree.Algebra.QuotientRankBounds
public import DedekindZetaZeroFree.Algebra.DualTestsForIndependentVectors
public import DedekindZetaZeroFree.Algebra.RangeRankFromDiagonalPairings
public import DedekindZetaZeroFree.Theta.Whittaker.DiagonalCharacterTransport

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualWhittaker
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair
open KPExceptionalRaw.FiniteSource.TameWhittakerSteps
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

 local instance whittakerCoinvariantRankOnePlusSectionAddCommGroup : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
 local instance whittakerCoinvariantRankOneMinusSectionAddCommGroup : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance

theorem residue_char_ne_three
    (ht : (3 : (valuation (LocalField F q)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer) :
    ringChar (IsLocalRing.ResidueField (valuation (LocalField F q)).integer) ≠ 3 := by
  intro h
  apply ht
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (3 : IsLocalRing.ResidueField (valuation (LocalField F q)).integer) = 0
  simpa only [h, Nat.cast_ofNat] using
    (ringChar.Nat.cast_ringChar (R := IsLocalRing.ResidueField (valuation (LocalField F q)).integer))

private theorem range_coinvariants_map
    {G N V W : Type*} [Group G] [Group N]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (n : N →* G) (ψ : N →* ℂˣ) (f : ρ.IntertwiningMap σ) :
    LinearMap.range (rootCoinvariantsMap ρ σ n ψ f) =
      (LinearMap.range f.toLinearMap).map (rootCoinvariantsMk σ n ψ) := by
  have h := rootCoinvariantsMap_comp_mk ρ σ n ψ f
  calc LinearMap.range (rootCoinvariantsMap ρ σ n ψ f)
      = LinearMap.range
          ((rootCoinvariantsMap ρ σ n ψ f).comp (rootCoinvariantsMk ρ n ψ)) := by
        rw [LinearMap.range_comp,
          LinearMap.range_eq_top.mpr (rootCoinvariantsMk_surjective ρ n ψ), Submodule.map_top]
    _ = LinearMap.range ((rootCoinvariantsMk σ n ψ).comp f.toLinearMap) := by rw [h]
    _ = (LinearMap.range f.toLinearMap).map (rootCoinvariantsMk σ n ψ) :=
      LinearMap.range_comp f.toLinearMap (rootCoinvariantsMk σ n ψ)

theorem standard_coinvariant_rank_le_one
    (ht : (3 : (valuation (LocalField F q)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer) :
    Module.rank ℂ (RootCoinvariants
      (actualCanonicalImageRepresentation F ζ hζ q S P μ hμ)
      (KPLocalJacquetImage.root S.borel)
      (KPKirillovProjectorGerms.frequencyCharacter F q 1)) ≤ 1 := by
  have htchar := residue_char_ne_three F q ht
  have hroot : ∃ ξ : LocalField F q, IsPrimitiveRoot ξ 12 :=
    ⟨algebraMap F (LocalField F q) ζ,
      hζ.map_of_injective (FaithfulSMul.algebraMap_injective F (LocalField F q))⟩
  let ρ := actualCanonicalImageRepresentation F ζ hζ q S P μ hμ
  let χ := KPKirillovProjectorGerms.frequencyCharacter F q 1
  let n := KPLocalJacquetImage.root S.borel
  let A := actualCanonicalForwardMap F ζ hζ q S P μ hμ
  let Q := ActualImageAlgebra.quotientMap A
  let R := actualCanonicalReverseMap F ζ hζ q S P μ hμ
  let p := rootCoinvariantsMap (IPlus S.borel P) ρ n χ Q
  let i := rootCoinvariantsMap (IMinus S.borel P) (IPlus S.borel P) n χ R
  have hp : Function.Surjective p := by
    intro w
    obtain ⟨v, rfl⟩ := rootCoinvariantsMk_surjective ρ n χ w
    obtain ⟨f, hf⟩ := ActualImageAlgebra.quotientMap_surjective A v
    rw [← hf]
    exact ⟨rootCoinvariantsMk (IPlus S.borel P) n χ f, rfl⟩
  have hz : p.comp i = 0 := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change rootCoinvariantsMk ρ n χ (Q (R v)) = 0
    have hQR : Q (R v) = 0 := by
      apply Subtype.ext
      exact LinearMap.congr_fun (actual_zero_opposite_compositions F ζ hζ q S P μ hμ).1 v
    exact congrArg (rootCoinvariantsMk ρ n χ) hQR |>.trans (map_zero _)
  have hi : 2 ≤ Module.rank ℂ (LinearMap.range i) := by
    obtain ⟨v₀, v₂, h⟩ := exists_reverse_independent_columns F ζ hζ q S P μ hμ htchar
    obtain ⟨ell₀, ell₂, h00, h02, h20, h22⟩ :=
      Uniqueness.ReverseMinor.exists_dual_diagonal_pairings_of_independent _ _ h (1 : ℂ) 1
    dsimp only [i]
    rw [range_coinvariants_map]
    exact Uniqueness.ReverseMinor.rank_map_range_ge_two_of_diagonal_pairings
      R.toLinearMap (rootCoinvariantsMk (IPlus S.borel P) n χ)
      v₀ v₂ ell₀ ell₂ 1 1 one_ne_zero one_ne_zero h00 h02 h20 h22
  apply Uniqueness.rank_le_of_surjective_zero_composition i p hp hz 1 2 _ hi
  exact Uniqueness.standard_plus_coinvariant_rank_le_three F ζ hζ q
    (actualRawInducing F ζ hζ q S) P hroot htchar

theorem coinvariant_rank_le_one
    (ht : (3 : (valuation (LocalField F q)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer)
    (ψ : Multiplicative (LocalField F q) →ₜ* ℂˣ) (hne : ψ.toMonoidHom ≠ 1) :
    Module.rank ℂ (RootCoinvariants
      (actualCanonicalImageRepresentation F ζ hζ q S P μ hμ)
      (KPLocalJacquetImage.root S.borel) ψ.toMonoidHom) ≤ 1 := by
  let χ : AddChar (LocalField F q) ℂˣ := AddChar.toMonoidHomEquiv.symm ψ.toMonoidHom
  have hχ : Continuous χ := ψ.continuous.comp continuous_ofAdd
  have hnχ : χ ≠ 1 := by
    intro he
    apply hne
    exact congrArg AddChar.toMonoidHom he
  have hn : KPLocalJacquetImage.root S.borel =
      KPLocalSmoothRepresentation.upperRoot F ζ hζ q := by
    ext x
    exact (S.openCell P).upper_eq (Multiplicative.toAdd x)
  obtain ⟨e⟩ := RawTransport.actual_character_quotient F ζ hζ q
    (actualCanonicalImageRepresentation F ζ hζ q S P μ hμ) χ hχ hnχ
  change Module.rank ℂ (RootCoinvariants
    (actualCanonicalImageRepresentation F ζ hζ q S P μ hμ)
    (KPLocalJacquetImage.root S.borel) χ.toMonoidHom) ≤ 1
  rw [hn, e.rank_eq, ← hn]
  exact standard_coinvariant_rank_le_one F ζ hζ q S P μ hμ ht

end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualWhittaker

end
