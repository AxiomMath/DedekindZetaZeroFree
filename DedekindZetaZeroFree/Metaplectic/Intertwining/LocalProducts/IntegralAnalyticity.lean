module

public import DedekindZetaZeroFree.LFunctions.Tate.UnitShellFourierNonvanishing
public import DedekindZetaZeroFree.Metaplectic.Intertwining.LocalProductAnalyticClearing
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ChamberIntegrals.FiniteVectorFubini

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity.ActualOutputAnalytic
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open KPRankOneShellRepair KPRankOneShellContinuation
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor renaming actualFiberCoordinates → actualFiberCoordinates
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor renaming actual_fiber_coordinates_apply → actual_fiber_coordinates_apply
open _root_.DedekindZetaZeroFree.KPRankOneTranslatedMeromorphy renaming section_coordinate_formula → section_coordinate_formula
open _root_.DedekindZetaZeroFree.KPRankOneTranslatedMeromorphy renaming target_scalar_diff → target_scalar_diff

 theorem multilinear_coordinate_analytic
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {J : ι → Type} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (e : ∀ i, V i ≃ₗ[ℂ] (J i → ℂ)) (L : MultilinearMap ℂ V ℂ)
    (v : ℂ → ∀ i, V i) (Ω : Set ℂ)
    (hv : ∀ i j, AnalyticOnNhd ℂ (fun s => e i (v s i) j) Ω) :
    AnalyticOnNhd ℂ (fun s => L (v s)) Ω := by
  let w (i : ι) (j : J i) := (e i).symm (Pi.single j 1)
  have he (y : ∀ i, V i) : L y =
      ∑ r : ∀ i, J i, (∏ i, e i (y i) (r i)) * L (fun i => w i (r i)) := by
    have hex (i : ι) : y i = ∑ j, e i (y i) j • w i j := by
      apply (e i).injective
      simp only [map_sum, map_smul, w, LinearEquiv.apply_symm_apply]
      rw [← Finset.univ_sum_single (e i (y i))]
      apply Finset.sum_congr rfl
      intro j _
      funext k
      simp [Pi.single_apply]
    calc
      L y = L (fun i => ∑ j, e i (y i) j • w i j) := congrArg L (funext hex)
      _ = _ := by
        rw [L.map_sum_finset]
        apply Finset.sum_congr rfl
        intro r _
        simpa only [smul_eq_mul] using
          L.map_smul_univ (fun i => e i (y i) (r i)) (fun i => w i (r i))
  have hf : (fun s => L (v s)) =
      (fun s => ∑ r : ∀ i, J i, (∏ i, e i (v s i) (r i)) * L (fun i => w i (r i))) :=
    funext (fun s => he (v s))
  rw [hf]
  intro s hs
  apply Finset.analyticAt_fun_sum
  intro r _
  exact (Finset.analyticAt_fun_prod Finset.univ (fun i _ => hv i (r i) s hs)).mul
    analyticAt_const

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem finite_full_right_coordinate_analytic
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (φ : compactPicture S.borel P S.iwasawa .plus)
    (g : ActualCover F ζ hζ q) (t : actualTorus F ζ hζ q) :
    AnalyticOnNhd ℂ (fun s =>
      ((transportToSections (LocalField F q) S.borel P S.iwasawa .plus s
        (actualCanonicalContinued F q ζ hζ S P μ hμ .plus s)
        (compactTrivialization S.borel P S.iwasawa .plus s φ)).val g).val t)
      KPContinuation.spectralDomain := by
  have he (s : ℂ) :
      ((transportToSections (LocalField F q) S.borel P S.iwasawa .plus s
        (actualCanonicalContinued F q ζ hζ S P μ hμ .plus s)
        (compactTrivialization S.borel P S.iwasawa .plus s φ)).val g).val t =
      inducingScalar S.borel (-s) (S.iwasawa.borelPart g) *
        ((actualCanonicalContinued F q ζ hζ S P μ hμ .plus s φ).val
          (S.iwasawa.compactPart g)).val
            (t * S.borel.weyl (S.borel.retract (S.iwasawa.borelPart g))) := by
    unfold transportToSections
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change ((compactTrivialization S.borel P S.iwasawa .minus (-s)
      (actualCanonicalContinued F q ζ hζ S P μ hμ .plus s
        ((compactTrivialization S.borel P S.iwasawa .plus s).symm
          (compactTrivialization S.borel P S.iwasawa .plus s φ)))).val g).val t = _
    rw [LinearEquiv.symm_apply_apply]
    exact section_coordinate_formula F ζ hζ q S P .plus s _ g t
  simp_rw [he]
  have hc := ActualLocalProduct.finite_coordinate_analytic F ζ hζ q S P μ hμ φ
    (S.iwasawa.compactPart g)
    (t * S.borel.weyl (S.borel.retract (S.iwasawa.borelPart g)))
  have hd := target_scalar_diff F ζ hζ q S .plus (S.iwasawa.borelPart g)
  intro s hs
  exact (hd.analyticAt s).mul (hc s hs)

variable (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
variable (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : C₀.exceptional ⊆ E)
variable (φfin : ∀ q : E, compactPicture (C₀.canonical q.val).borel (C₀.polarization q.val)
  (C₀.canonical q.val).iwasawa .plus)
variable (gfin : ∀ q : E, ActualCover F ζ hζ q.val)
variable (t : KPGlobalTorusFunctionData.E F ζ hζ)

variable (φarch : {w : NumberField.InfinitePlace F // w.IsComplex} →
  KPComplexIntertwinerParameterMajorant.CompactPicture)
variable (garch : {w : NumberField.InfinitePlace F // w.IsComplex} → KPCplxCharacterHaar.ComplexGL2)

end DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity.ActualOutputAnalytic

end
