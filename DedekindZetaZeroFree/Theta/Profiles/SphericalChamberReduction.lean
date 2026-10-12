module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.ScalarChamberReduction

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.FourierContinuation.CurrentSphericalReduction
open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPLocalGoodSphericalImage KPRankOneTameSphericalFactor KPRankOneShellContinuation
open KPLocalExceptionalConstruction KPLocalTameIntertwiningBlock KPRankOneShellRepair
open _root_.DedekindZetaZeroFree.KPLocalTameIntertwiningBlock renaming compact_extension_one → compact_extension_one
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
variable (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
theorem actual_spherical_chamber
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (hu : UnramifiedCompactInducingData S.borel P S.iwasawa)
    (hW : (compactTorus S.borel S.iwasawa).map S.borel.weyl.toMulEquiv.toMonoidHom = compactTorus S.borel S.iwasawa)
    (φp : compactPicture S.borel P S.iwasawa .plus) (φm : compactPicture S.borel P S.iwasawa .minus)
    (hp : IsSphericalVector (LocalField F q) S.borel P S.iwasawa .plus φp)
    (hm : IsSphericalVector (LocalField F q) S.borel P S.iwasawa .minus φm)
    (hscalar : ∀ s : ℂ, convergenceHalfPlane .plus s →
      standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ .plus s φp 1 1 = forwardFactor (LocalField F q) μ s) :
    ∀ s : ℂ, convergenceHalfPlane .plus s → ∀ (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q),
      standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ .plus s φp g h = forwardFactor (LocalField F q) μ s *
        ((compactTrivialization S.borel P S.iwasawa .minus (-s) φm).val g).val h := by
  intro s hs g h
  let B := actualCanonicalContinued F q ζ hζ S P μ hμ .plus s
  let vp : compactLevel S.borel P S.iwasawa .plus S.iwasawa.compact :=
    ⟨φp, spherical_vector_mem_level (LocalField F q) S.borel P S.iwasawa .plus φp hp⟩
  have hlevel : B φp ∈ compactLevel S.borel P S.iwasawa .minus S.iwasawa.compact := by
    rw [show B φp = _ from actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .plus s S.iwasawa.compact le_rfl vp]
    exact (continuedLevel (LocalField F q) S.borel P S.iwasawa S.iwasawa.compact .plus
      (actualCanonicalLevelNumerator F ζ hζ q S P S.iwasawa.compact le_rfl μ hμ .plus) s vp).property
  have hf := minus_compact_level_formula (LocalField F q) S.borel P S.iwasawa hu hW φm (B φp) hm hlevel
  have he := actualCanonicalContinued_chamber F q ζ hζ S P μ hμ .plus s hs φp 1 1
  simp only [transportToSections, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at he
  have hv := congrArg (fun v : InducedModule P => v.val 1)
    (compact_extension_one (LocalField F q) S.borel P S.iwasawa .minus (-s) (B φp))
  change ((compactTrivialization S.borel P S.iwasawa .minus (-s) (B φp)).val 1).val 1 = _ at he
  erw [hv, hscalar s hs] at he
  rw [he] at hf
  rw [← actualCanonicalContinued_chamber F q ζ hζ S P μ hμ .plus s hs φp g h]
  simp only [transportToSections, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change ((compactTrivialization S.borel P S.iwasawa .minus (-s) (B φp)).val g).val h = _
  rw [hf, map_smul]
  rfl
end DedekindZetaZeroFree.FourierContinuation.CurrentSphericalReduction

end
