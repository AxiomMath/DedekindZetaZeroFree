module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.LocalProducts.IntegralAnalyticity
public import DedekindZetaZeroFree.Metaplectic.Intertwining.CompactModels.ExponentialPolynomialCorrection

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity.CorrectedOutputAnalytic
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open KPRankOneShellRepair KPRankOneShellContinuation ActualOutputAnalytic
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open ActualCofactor LocalCompactChange
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity.ActualOutputAnalytic renaming multilinear_coordinate_analytic → multilinear_coordinate_analytic
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor renaming actualFiberCoordinates → actualFiberCoordinates

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem finite_corrected_full_right_coordinate_analytic
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (J : IwasawaData S.borel)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (φ : compactPicture S.borel P S.iwasawa .plus)
    (g : ActualCover F ζ hζ q) (t : actualTorus F ζ hζ q) :
    AnalyticOnNhd ℂ (fun s =>
      ((transportToSections (LocalField F q) S.borel P S.iwasawa .plus s
        (actualCanonicalContinued F q ζ hζ S P μ hμ .plus s)
        (compactTrivialization S.borel P S.iwasawa .plus s
          (correctedCompact F ζ hζ q S S.iwasawa J P s φ))).val g).val t)
      KPContinuation.spectralDomain := by
  let M (s : ℂ) : compactPicture S.borel P S.iwasawa .plus →ₗ[ℂ] ℂ :=
    { toFun := fun ψ =>
        ((transportToSections (LocalField F q) S.borel P S.iwasawa .plus s
          (actualCanonicalContinued F q ζ hζ S P μ hμ .plus s)
          (compactTrivialization S.borel P S.iwasawa .plus s ψ)).val g).val t
      map_add' := by intro ψ χ; simp only [map_add]; rfl
      map_smul' := by intro c ψ; simp only [map_smul]; rfl }
  let N := correctionSpectrum F ζ hζ q S S.iwasawa J
  let v (r : ℝ) := correctionComponent F ζ hζ q S S.iwasawa J P r φ
  have he (s : ℂ) : M s (correctedCompact F ζ hζ q S S.iwasawa J P s φ) =
      ∑ r ∈ N, Complex.exp (s * (r : ℂ)) * M s (v r) := by
    rw [correctedCompact_expansion, map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  have hf : (fun s => M s (correctedCompact F ζ hζ q S S.iwasawa J P s φ)) =
      (fun s => ∑ r ∈ N, Complex.exp (s * (r : ℂ)) * M s (v r)) := funext he
  change AnalyticOnNhd ℂ (fun s => M s (correctedCompact F ζ hζ q S S.iwasawa J P s φ)) _
  rw [hf]
  intro s hs
  apply Finset.analyticAt_fun_sum
  intro r _
  exact (show AnalyticAt ℂ (fun s => Complex.exp (s * (r : ℂ))) s by fun_prop).mul
    (finite_full_right_coordinate_analytic F ζ hζ q S P μ hμ (v r) g t s hs)

variable (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
variable (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : C₀.exceptional ⊆ E)
variable (J : ∀ q : E, IwasawaData (C₀.canonical q.val).borel)
variable (φfin : ∀ q : E, compactPicture (C₀.canonical q.val).borel (C₀.polarization q.val)
  (C₀.canonical q.val).iwasawa .plus)
variable (gfin : ∀ q : E, ActualCover F ζ hζ q.val)
variable (t : KPGlobalTorusFunctionData.E F ζ hζ)

variable (φarch : {w : NumberField.InfinitePlace F // w.IsComplex} →
  KPComplexIntertwinerParameterMajorant.CompactPicture)
variable (garch : {w : NumberField.InfinitePlace F // w.IsComplex} → KPCplxCharacterHaar.ComplexGL2)

end DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity.CorrectedOutputAnalytic

end
