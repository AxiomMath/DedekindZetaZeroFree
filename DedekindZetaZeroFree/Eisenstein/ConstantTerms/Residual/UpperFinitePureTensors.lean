module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Residual.ReflectedFinitePurity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SectionContinuity
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorWords.Germs

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators TensorProduct Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open CurrentRepairedLocalBinding MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPGlobalResidualConstruction KPLiteralChamber
open KPLiteralScalarArchUniformBands KPAdelicCoverRestrictedProduct TensorActionSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

theorem upper_finite_pure_near_compact
    (s : RestrictedTensorSimple.Level (bad R P C))
    (K : Set (InfinitePlace F → ComplexGL2)) (hK : IsCompact K)
    (r : Raw R) (hr : ∀w : InfinitePlace F,r (.inl w)=1)
    (v : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    ∃ A : Set (InfinitePlace F → ComplexGL2), IsCompact A ∧ K ⊆ interior A ∧
    ∃ n : ℕ, ∃ d : Fin n → ℂ, ∃ f : Fin n → InfinitePlace F → PrincipalSeries negativeParameter,
      ∀ a ∈ A,
        (∫ u : KPAdditiveQuotient F,
          LiteralSource.coreResidue R P C
            (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v))
            (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) *
              scalarQuotient F ζ hζ (amalgamation F ζ hζ (r * sectionTuple F ζ hζ a)))
          ∂KPWildKernelUpperBound.quotientHaar F) =
        ∑j, d j * ∏w, f j w (a w) := by
  obtain ⟨A,hA,hKA⟩ := exists_compact_superset hK
  have hc : Continuous (fun a => r * sectionTuple F ζ hζ a) :=
    continuous_const.mul (sectionTuple_continuous F ζ hζ)
  obtain ⟨E,hsE,hCE,hfactor⟩ := current_upper_residue_factorization R N P C  s
    (Set.image (fun a => r * sectionTuple F ζ hζ a) A) (hA.image hc)
  let y := RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
    (bad R P C) s (fullLevel R P C E hCE)
    (sourceStage_le_fullLevel R P C s E hCE hsE) v
  obtain ⟨n,d,f,hf⟩ := reflected_finite_pure R N P C (fullLevel R P C E hCE)
    (by intro w; simp [fullLevel,LiteralSource.cofactorSourceLevel]) r hr
    (sourceStageQuotient R (imageData R N P C) (fullLevel R P C E hCE).val y)
  refine ⟨A,hA,hKA,n,fun j => KPGlobalFiniteSIntertwiner.residueNormalizer F  ζ hζ E *
    (arithmeticStageScale R (fullLevel R P C E hCE).val : ℂ) * d j,f,?_⟩
  intro a ha
  rw [hfactor _ ⟨a,ha,rfl⟩ v,parameterStage_zero]
  change _ * ((arithmeticStageScale R (fullLevel R P C E hCE).val : ℂ) *
    (reflectedStage R N P C _ _ _).val.val 1) = _
  rw [hf]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
