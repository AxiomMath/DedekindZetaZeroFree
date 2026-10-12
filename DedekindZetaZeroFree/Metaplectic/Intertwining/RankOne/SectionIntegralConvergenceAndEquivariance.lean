module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CompatibleLevelContinuation
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.StandardIntegralBorelCovariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
  (ε : Sign)

theorem actualContinued_compact_eq_integral (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    ((actualContinued F ζ hζ q S P μ hμ π hπ ε s φ).val k).val h =
      standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ k h := by
  obtain ⟨J, hJ, hφ⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) φ
  rw [actualContinued_eq_level F ζ hζ q S P μ hμ π hπ ε s J hJ ⟨φ, hφ⟩]
  exact actualContinuedLevel_eq_integral F ζ hζ q S P J hJ μ hμ π hπ ε s hs ⟨φ, hφ⟩ k h

theorem actualContinued_section_eq_integral (s : ℂ) (hs : convergenceHalfPlane ε s)
    (f : sectionSpace S.borel P (sourceSign ε) (sourceParameter ε s))
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
        (actualContinued F ζ hζ q S P μ hμ π hπ ε s) f).val g).val h =
      ∫ x : LocalField F q,
        (f.val (kernelW (LocalField F q) S.borel ε *
          S.borel.upperRoot (Multiplicative.ofAdd x) * g)).val h ∂μ := by
  let φ := (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)).symm f
  have hB := KPRankOneShellActualBorel.standardIntegral_borel_coordinate F ζ hζ q S P μ ε s φ
    (S.iwasawa.borelPart g) (S.iwasawa.compactPart g) h
  rw [← S.iwasawa.decomposition g] at hB
  have he : (∫ x : LocalField F q, (f.val (kernelW (LocalField F q) S.borel ε *
      S.borel.upperRoot (Multiplicative.ofAdd x) * g)).val h ∂μ) =
      standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ g h := by
    unfold standardIntegralCoordinate
    simp only [φ, LinearEquiv.apply_symm_apply]
  rw [he, hB]
  change (inducingAction S.borel P (targetSign ε) (targetParameter ε s) (S.iwasawa.borelPart g)
    ((actualContinued F ζ hζ q S P μ hμ π hπ ε s φ).val (S.iwasawa.compactPart g))).val h = _
  have ha : ∀ v : InducedModule P,
      (inducingAction S.borel P (targetSign ε) (targetParameter ε s) (S.iwasawa.borelPart g) v).val h =
      inducingScalar S.borel (targetParameter ε s) (S.iwasawa.borelPart g) *
        v.val (h * (if targetSign ε = .plus then S.borel.retract (S.iwasawa.borelPart g)
          else S.borel.weyl (S.borel.retract (S.iwasawa.borelPart g)))) := by
    intro v
    cases ε <;> rfl
  rw [ha, actualContinued_compact_eq_integral F ζ hζ q S P μ hμ π hπ ε s hs]

theorem actualContinued_section_intertwines_chamber (s : ℂ) (hs : convergenceHalfPlane ε s)
    (g : ActualCover F ζ hζ q)
    (f : sectionSpace S.borel P (sourceSign ε) (sourceParameter ε s)) :
    transportToSections (LocalField F q) S.borel P S.iwasawa ε s
        (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
      (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g f) =
    principalSeries S.borel P (targetSign ε) (targetParameter ε s) g
      (transportToSections (LocalField F q) S.borel P S.iwasawa ε s
        (actualContinued F ζ hζ q S P μ hμ π hπ ε s) f) := by
  apply Subtype.ext
  funext x
  apply Subtype.ext
  funext h
  change ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
      (actualContinued F ζ hζ q S P μ hμ π hπ ε s)
      (principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g f)).val x).val h =
    ((transportToSections (LocalField F q) S.borel P S.iwasawa ε s
      (actualContinued F ζ hζ q S P μ hμ π hπ ε s) f).val (x * g)).val h
  rw [actualContinued_section_eq_integral F ζ hζ q S P μ hμ π hπ ε s hs,
    actualContinued_section_eq_integral F ζ hζ q S P μ hμ π hπ ε s hs]
  apply integral_congr_ae
  filter_upwards [] with t
  change (f.val ((kernelW (LocalField F q) S.borel ε *
    S.borel.upperRoot (Multiplicative.ofAdd t) * x) * g)).val h = _
  rw [mul_assoc]

include hμ π hπ in

theorem actual_section_integrable (s : ℂ) (hs : convergenceHalfPlane ε s)
    (f : sectionSpace S.borel P (sourceSign ε) (sourceParameter ε s))
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    Integrable (fun x : LocalField F q =>
      (f.val (kernelW (LocalField F q) S.borel ε *
        S.borel.upperRoot (Multiplicative.ofAdd x) * g)).val h) μ := by
  let fg := principalSeries S.borel P (sourceSign ε) (sourceParameter ε s) g f
  let φ := (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)).symm fg
  obtain ⟨J, hJ, hφ⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) φ
  have hi := actual_standard_integral_coordinate_integrable F ζ hζ q S P J hJ μ hμ π hπ
    ε s hs ⟨φ, hφ⟩ 1 h
  have he : actualStandardIntegrand F ζ hζ q S P ε s φ 1 h =
      fun x : LocalField F q => (f.val (kernelW (LocalField F q) S.borel ε *
        S.borel.upperRoot (Multiplicative.ofAdd x) * g)).val h := by
    funext x
    unfold actualStandardIntegrand
    simp only [φ, LinearEquiv.apply_symm_apply]
    change (f.val ((kernelW (LocalField F q) S.borel ε *
      S.borel.upperRoot (Multiplicative.ofAdd x) * 1) * g)).val h = _
    rw [mul_one]
  rw [he] at hi
  exact hi

end DedekindZetaZeroFree.KPRankOneShellRepair

end
