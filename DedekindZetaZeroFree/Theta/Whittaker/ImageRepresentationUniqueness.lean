module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.WhittakerCoinvariantRankOne

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ActualWhittaker
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem equivariant_rank_le_one_of_coinvariant_rank_le_one
    {G N V : Type*} [Group G] [Group N] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (n : N →* G) (ψ : N →* ℂˣ)
    (hJ : Module.rank ℂ (RootCoinvariants ρ n ψ) ≤ 1) :
    Module.rank ℂ (RootEquivariantMaps ρ n ψ ℂ) ≤ 1 := by
  letI : Module.Finite ℂ (RootCoinvariants ρ n ψ) :=
    Module.rank_lt_aleph0_iff.mp (hJ.trans_lt Cardinal.one_lt_aleph0)
  let e := rootCoinvariantsUniversalEquiv ρ n ψ ℂ
  letI : Module.Finite ℂ (RootEquivariantMaps ρ n ψ ℂ) := e.finiteDimensional
  rw [← e.rank_eq, ← Module.finrank_eq_rank]
  have hfin : Module.finrank ℂ (Module.Dual ℂ (RootCoinvariants ρ n ψ)) ≤ 1 := by
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_le_of_rank_le (by simpa using hJ :
      Module.rank ℂ (RootCoinvariants ρ n ψ) ≤ (1 : ℕ))
  exact_mod_cast hfin

theorem rank_le_one
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (ht : (3 : (valuation (LocalField F q)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer)
    (ψ : Multiplicative (LocalField F q) →ₜ* ℂˣ) (hne : ψ.toMonoidHom ≠ 1) :
    Module.rank ℂ (RootEquivariantMaps
      (actualCanonicalImageRepresentation F ζ hζ q S P μ hμ)
      (KPLocalJacquetImage.root S.borel) ψ.toMonoidHom ℂ) ≤ 1 := by
  exact equivariant_rank_le_one_of_coinvariant_rank_le_one _ _ _
    (coinvariant_rank_le_one F ζ hζ q S P μ hμ ht ψ hne)

end DedekindZetaZeroFree.ExteriorWhittakerValues.ActualWhittaker

end
