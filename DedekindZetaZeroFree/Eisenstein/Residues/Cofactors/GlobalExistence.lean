module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Cofactors.BoundedRegionExistence
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.GlobalFiberIntegral
public import DedekindZetaZeroFree.LFunctions.Hecke.EulerProducts.ExteriorNormalizer

@[expose] public section

noncomputable section
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming adelic_measure_box → adelic_measure_box
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming finite_measure_sigmaFinite → finite_measure_sigmaFinite
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming arch_measure_sigmaFinite → arch_measure_sigmaFinite
local instance cofactorGlobalProducerArchMeasurable (F : Type) [Field F] [NumberField F] : MeasurableSpace (NumberField.InfiniteAdeleRing F) := borel _
local instance cofactorGlobalProducerArchBorel (F : Type) [Field F] [NumberField F] : BorelSpace (NumberField.InfiniteAdeleRing F) := ⟨rfl⟩
open _root_.DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant renaming forwardSection_real_formula → forwardSection_real_formula
open scoped Classical NumberField TensorProduct BigOperators Topology
open Filter
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages KPLocalExceptionalConstruction
open KPGlobalResidualConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem exterior_enlargement_tendsto
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) :
    Tendsto (fun T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) =>
      KPGlobalFiniteSIntertwiner.enlargementFactor F E (E ∪ T) s) atTop
      (𝓝 (KPGlobalFiniteSIntertwiner.normalizer F  ζ hζ E s)) := by
  have hp := ExteriorFactorLimit.exterior_goodFactor_hasProd F ζ hζ  E s hs
  have he (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
      KPGlobalFiniteSIntertwiner.enlargementFactor F E (E ∪ T) s =
        ∏ q ∈ T, if q ∈ E then (1 : ℂ) else KPGlobalFiniteSIntertwiner.goodFactor F q s := by
    unfold KPGlobalFiniteSIntertwiner.enlargementFactor
    simp only [Finset.union_sdiff_left]
    calc
      (∏ q ∈ T \ E, KPGlobalFiniteSIntertwiner.goodFactor F q s) =
          ∏ q ∈ T.filter (fun q => q ∉ E), KPGlobalFiniteSIntertwiner.goodFactor F q s := by
            congr 1
            ext q
            simp
      _ = _ := by
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro q _
        by_cases hq : q ∈ E <;> simp [hq]
  change Tendsto (fun T => ∏ q ∈ T, if q ∈ E then (1 : ℂ) else
    KPGlobalFiniteSIntertwiner.goodFactor F q s) atTop _ at hp
  simpa only [he] using hp

theorem exists_current_global_cofactor
    (E : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (hD : localDifferentSupport F ⊆ (E : Set _)) :
    ∃ (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
        (C.canonical q.val).iwasawa .plus)
      (t : KPGlobalTorusFunctionData.E F ζ hζ) (b : ℂ → ℂ),
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1 ∧
      MeromorphicOn b Set.univ ∧ AnalyticAt ℂ b 0 ∧ b 0 ≠ 0 ∧
      ∀ z : ℂ, (1/3 : ℝ) < z.re →
        coreScattering R P C (cofactorSourceCore R P C E hE φ) z
          (NormOneTorusAlgebra.rightEvaluation F ζ hζ t) =
          KPGlobalFiniteSIntertwiner.normalizer F  ζ hζ E z * b z := by
  obtain ⟨φ,t,b,ht,hm,ha,hn,hbox⟩ := exists_current_boxed_cofactor R P C E hE hD
  refine ⟨φ,t,b,ht,hm,ha,hn,?_⟩
  intro z hz
  let x := cofactorSourceCore R P C E hE φ
  have hi := coreFlatFiber_chamber_integrable R P C x z hz t ht
  have hl := tendsto_setIntegral_of_monotone
    (FullSourceExhaustion.adelicBox_measurable F)
    (FullSourceExhaustion.adelicBox_monotone F) hi.integrableOn
  rw [FullSourceExhaustion.adelicBox_iUnion F, Measure.restrict_univ] at hl
  have hl' := hl.comp (tendsto_atTop_mono (fun T : Finset (KPFinitePlace F) =>
    (Finset.subset_union_right : T ⊆ E ∪ T)) tendsto_id)
  rw [← coreFlatFiber_chamber_integral R P C x z t ht] at hl'
  have he := (exterior_enlargement_tendsto R  E z hz).mul_const (b z)
  have he' := he.congr' (Filter.Eventually.of_forall (fun T =>
    (hbox (E ∪ T) Finset.subset_union_left z (by
      change -(1/6 : ℝ) < z.re
      linarith)).symm))
  exact tendsto_nhds_unique hl' he'

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
