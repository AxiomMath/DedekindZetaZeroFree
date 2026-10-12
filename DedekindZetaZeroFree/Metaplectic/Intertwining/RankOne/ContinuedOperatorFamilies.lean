module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.MeromorphicGroupEquivariance
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CanonicalNumeratorCoefficientsAndMeromorphicLevels

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))

 theorem uniformizer_exists : ∃ π : (LocalField F q)ˣ,
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  obtain ⟨x, hx⟩ := valuation_surjective (K := LocalField F q) (e.symm (WithZero.exp (-1 : ℤ)))
  have hv : valuation (LocalField F q) x ≠ 0 := by
    rw [hx]
    exact (map_ne_zero e.symm).mpr (by simp)
  have hn : x ≠ 0 := fun h => hv (by simp [h])
  refine ⟨Units.mk0 x hn, ?_⟩
  change e (valuation (LocalField F q) x) = _
  rw [hx, e.apply_symm_apply]

def actualFamilyUniformizer : (LocalField F q)ˣ := (uniformizer_exists F q).choose

theorem actualFamilyUniformizer_spec :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (actualFamilyUniformizer F q : LocalField F q)) =
      WithZero.exp (-1 : ℤ) := (uniformizer_exists F q).choose_spec

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ε : Sign)

def actualCanonicalContinued (s : ℂ) :
    compactPicture S.borel P S.iwasawa (sourceSign ε) →ₗ[ℂ]
      compactPicture S.borel P S.iwasawa (targetSign ε) :=
  actualContinued F ζ hζ q S P μ hμ (actualFamilyUniformizer F q)
    (actualFamilyUniformizer_spec F q) ε s

theorem actualCanonicalContinued_eq_level (s : ℂ)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
    actualCanonicalContinued F q ζ hζ S P μ hμ ε s φ.val =
      (continuedLevel (LocalField F q) S.borel P S.iwasawa J ε
        (actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ ε) s φ).val := by
  unfold actualCanonicalContinued
  rw [actualContinued_eq_level F ζ hζ q S P μ hμ (actualFamilyUniformizer F q)
    (actualFamilyUniformizer_spec F q) ε s J hJ φ,
    actualCanonicalLevelNumerator_eq_actual F ζ hζ q S P J hJ μ hμ ε
      (actualFamilyUniformizer F q) (actualFamilyUniformizer_spec F q)]
  rfl

theorem actualCanonicalContinued_intertwines (s : ℂ)
    (hs : denominator (LocalField F q) ε s ≠ 0) (g : ActualCover F ζ hζ q)
    (f : sectionSpace S.borel P (sourceSign ε) (sourceParameter ε s)) :
    transportToSections (LocalField F q) S.borel P S.iwasawa ε s
      (actualCanonicalContinued F q ζ hζ S P μ hμ ε s)
      (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g f) =
    principalSeries S.borel P (targetSign ε) (targetParameter ε s) g
      (transportToSections (LocalField F q) S.borel P S.iwasawa ε s
        (actualCanonicalContinued F q ζ hζ S P μ hμ ε s) f) :=
  actualContinued_section_intertwines F ζ hζ q S P μ hμ (actualFamilyUniformizer F q)
    (actualFamilyUniformizer_spec F q) ε s hs g f

theorem actualCanonicalContinued_chamber (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
      (actualCanonicalContinued F q ζ hζ S P μ hμ ε s)
      (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ)).val g).val h =
    standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ g h :=
  actualContinued_section_eq_integral F ζ hζ q S P μ hμ (actualFamilyUniformizer F q)
    (actualFamilyUniformizer_spec F q) ε s hs
    (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ) g h

include hμ in

theorem actualCanonicalContinued_integrable (s : ℂ) (hs : convergenceHalfPlane ε s)
    (f : sectionSpace S.borel P (sourceSign ε) (sourceParameter ε s))
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    Integrable (fun x : LocalField F q =>
      (f.val (kernelW (LocalField F q) S.borel ε *
        S.borel.upperRoot (Multiplicative.ofAdd x) * g)).val h) μ :=
  actual_section_integrable F ζ hζ q S P μ hμ (actualFamilyUniformizer F q)
    (actualFamilyUniformizer_spec F q) ε s hs f g h

end DedekindZetaZeroFree.KPRankOneShellRepair

end
