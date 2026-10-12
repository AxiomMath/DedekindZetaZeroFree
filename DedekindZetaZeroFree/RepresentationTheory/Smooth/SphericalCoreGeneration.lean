module

public import DedekindZetaZeroFree.Theta.Periods.SphericalTensor.SmoothGlobalization
public import DedekindZetaZeroFree.Theta.Periods.SphericalProductNonvanishing
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FirstRootHarishChandraHeckeRecovery

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MeasureTheory MomentSources FourierContinuation FourierContinuation.ComplexLines
open KPCplxActualImage KPCplxWhittakerUnique
open KPActualReflectionData.StandardLocalSource
open KPReferenceChange.StandardComplexImage
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem actualRightWord_eq_adelic (R : PrincipalMellin.ActualRecipe S η)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (f : Functions R) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f =
      AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord, AdelicRightLieWords.actualRightWord]
    rw [ih]
    rfl

theorem prepared_spherical_entries_ne_zero {Q : AdmissibleFlatSources R}
    {T : Realization R Q} (D : SourceFactorization R Q T)
    (K : PreparedSphericalTensor R D) : ∀p,K.entries p≠0 := by
  rintro ⟨p,hp⟩
  cases p with
  | inl w =>
    rw [K.spherical w hp]
    exact sphericalCoreSeed_ne_zero
  | inr q =>
    have hq : q∈R.A.Sf := by
      have h := (D.bad_exact (Sum.inr q)).mp (K.stage_exact ▸ hp)
      rcases h with ⟨w,h⟩ | ⟨q0,h,hq0⟩
      · cases h
      · cases h;exact hq0
    intro hz
    have hh := K.finite_value ⟨q,hq⟩ hp
    rw [hz,map_zero] at hh
    exact zero_ne_one hh

theorem core_spherical_generated_of_realization {Q Q0 : AdmissibleFlatSources R}
    {T : Realization R Q} (D : SourceFactorization R Q T)
    (K : PreparedSphericalTensor R D) (hNative : SourceNativeLie R D)
    (T0 : Realization R Q0) (hT0 : ∀v,T0.theta v=K.value) :
    ∀x,D.coreMap x∈ThetaExpansion.sphericalHCSpan R K.value := by
  have hs : hcHeckeSpan T≤hcHeckeSpan T0 := by
    apply frozen_hc_recovery_of_differential_stability R D T0
      KPGlobalResidualConstruction.NativeComplexHCOperators.operators
    · intro v hv
      exact complexHC_algebra_cyclic _
        KPGlobalResidualConstruction.NativeComplexHCAlgebraic.native_operators_simple v hv
    · intro s x w hw i hm
      have hh := hNative s w hw i (PiTensorProduct.tprod ℂ x)
      rw [FourierContinuation.HCGeneration.tensorSlot_tprod] at hh
      change _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
        (KPGlobalResidualConstruction.NativeComplexHCOperators.operators i (x ⟨Sum.inl w,hw⟩)))=_ at hh
      rw [hh]
      have hd := wordRecovery_word R T0 hm
        [(FourierContinuation.HCGeneration.actualLieIndexEquiv (F:=F)).symm (w,i)]
      simpa only [KPContActualSphericalRightFieldIdentification.actualRightWord,_root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction] using hd
    · intro v
      exact ⟨K.stage,K.entries,K.stage_exact,(hT0 v).symm,
        prepared_spherical_entries_ne_zero D K⟩
  have he : hcHeckeSpan T0≤ThetaExpansion.sphericalHCSpan R K.value := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,a,w,rfl⟩
    rw [hT0]
    exact Submodule.subset_span ⟨a,w,by rw [actualRightWord_eq_adelic R]⟩
  intro x
  exact he (hs (D.core_same_residue x).1)
end DedekindZetaZeroFree.RootDerivatives

end
