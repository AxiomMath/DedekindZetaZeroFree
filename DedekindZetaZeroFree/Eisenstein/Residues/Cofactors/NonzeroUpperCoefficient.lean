module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Scattering.MeromorphicNumerators
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.GlobalExistence
public import DedekindZetaZeroFree.Eisenstein.Residues.NormalizerClearingValues

@[expose] public section

noncomputable section
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming adelic_measure_box → adelic_measure_box
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming finite_measure_sigmaFinite → finite_measure_sigmaFinite
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming arch_measure_sigmaFinite → arch_measure_sigmaFinite
local instance cofactorNonzeroArchMeasurable (F : Type) [Field F] [NumberField F] : MeasurableSpace (NumberField.InfiniteAdeleRing F) := borel _
local instance cofactorNonzeroArchBorel (F : Type) [Field F] [NumberField F] : BorelSpace (NumberField.InfiniteAdeleRing F) := ⟨rfl⟩
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

theorem exists_current_nonzero_upper  :
    ∃ (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C))
      (g : MomentSources.Group R),
      (∫ u : KPAdditiveQuotient F, coreResidue R P C x
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) * g)
        ∂KPWildKernelUpperBound.quotientHaar F) ≠ 0 := by
  let E := C.exceptional ∪ (finite_localDifferentSupport F).toFinset
  have hE : C.exceptional ⊆ E := Finset.subset_union_left
  have hD : localDifferentSupport F ⊆ (E : Set _) := by
    intro q hq
    exact Finset.mem_union_right _ ((finite_localDifferentSupport F).mem_toFinset.mpr hq)
  obtain ⟨φ,t,b,ht,hm,ha,hn,hfactor⟩ := exists_current_global_cofactor R P C  E hE hD
  let x := cofactorSourceCore R P C E hE φ
  let g := NormOneTorusAlgebra.rightEvaluation F ζ hζ t
  obtain ⟨M,B,r,hM,hMch,hr,hrb,hB,hclear,hcenter⟩ := core_scattering_continuation R P C x g
  have h0 : (0 : ℂ) ∈ KPContinuation.spectralDomain := by norm_num [KPContinuation.spectralDomain]
  have hb0 := hB 0 (Metric.mem_ball_self hr)
  have hnear : B =ᶠ[𝓝[≠] (0 : ℂ)] fun s => s * M s := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with s hs hs0
    exact hclear s hs hs0
  have hv := clearing_value_from_global_cofactor F ζ hζ  E hM.meromorphicOn hm
    KPContinuation.spectralDomain_isConnected KPContinuation.convergenceHalfPlane_subset_spectralDomain
    h0 ha.continuousAt hb0.continuousAt (fun s hs => (hMch s hs).trans (hfactor s hs)) hnear
  have hnrm : KPGlobalFiniteSIntertwiner.residueNormalizer F  ζ hζ E ≠ 0 := by
    intro he
    have hp := (KPGlobalFiniteSIntertwiner.residueNormalizer_pos F  ζ hζ E).2
    rw [he, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  refine ⟨x,g,?_⟩
  rw [← hcenter, hv]
  exact mul_ne_zero hnrm hn

theorem exists_coreResidue_ne_zero  :
    ∃ x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C),
      coreResidue R P C x ≠ 0 := by
  obtain ⟨x,g,h⟩ := exists_current_nonzero_upper R P C
  refine ⟨x,?_⟩
  intro hx
  apply h
  simp only [hx, Pi.zero_apply, integral_zero]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
