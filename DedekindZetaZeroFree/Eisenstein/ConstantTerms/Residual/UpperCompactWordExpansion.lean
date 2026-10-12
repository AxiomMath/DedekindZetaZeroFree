module

public import DedekindZetaZeroFree.Eisenstein.Residues.CompactConvolution.GermWordExpansion

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open CurrentRepairedLocalBinding MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPGlobalResidualConstruction KPLiteralChamber
open KPLiteralScalarArchUniformBands KPAdelicCoverRestrictedProduct TensorActionSource
open KPContActualSphericalRightFieldIdentification CurrentComplexBoundary
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (LiteralSource.Plus R.A P C) (LiteralSource.plusReference R.A P C) (LiteralSource.bad R.A P C)
local instance : CompactSpace ComplexSU2 := by
  apply isCompact_iff_compactSpace.mp
  convert complexSU2_isCompact using 1
  exact Subtype.range_coe.symm

def originalUpper (h : KPLiteralRaw.G F ζ hζ → ℂ) (g : KPLiteralRaw.G F ζ hζ) : ℂ :=
  ∫q : KPAdditiveQuotient F, h (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g)
    ∂KPWildKernelUpperBound.quotientHaar F

include N in
theorem upper_compact_word_expansion
    (x : Core) (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    ∃ n : ℕ, ∃ d : Fin n → ℂ, ∃ f : Fin n → InfinitePlace F → PrincipalSeries negativeParameter,
      ∀w k, actualRightWord F ζ hζ w (originalUpper R (LiteralSource.coreResidue R P C x))
        (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val) =
      ∑j,d j*pureCompact negativeParameter
        (fun i=>matrixWord negativeParameter (slotWords i (w.map (matrixLetter F))) (f j i)) k := by
  obtain ⟨y,rfl⟩ := (coreEquiv R N P C).surjective x
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C,le_rfl⟩⟩
  obtain ⟨s,v,rfl⟩ := Module.DirectLimit.exists_of y
  obtain ⟨r,hr,hc⟩ := c.property
  have hrw : ∀w : InfinitePlace F,r (.inl w)=1 := fun w=>(Subgroup.mem_iInf.mp hr) w
  have hemb : Continuous complexSU2Embedding := by
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val
    · have hi (k : ComplexSU2) : (↑(complexSU2Embedding k)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [←map_inv]; rfl
      simp_rw [hi]
      exact continuous_subtype_val.star
  let emb : (InfinitePlace F → ComplexSU2) → InfinitePlace F → ComplexGL2 :=
    fun u i=>complexSU2Embedding (u i)
  have hembs : Continuous emb := continuous_pi (fun i=>hemb.comp (continuous_apply i))
  have hK : IsCompact (Set.range emb) := isCompact_range hembs
  obtain ⟨A,hA,hKA,n,d,f,he⟩ := upper_finite_pure_near_compact R N P C  s
    (Set.range emb) hK r hrw v
  refine ⟨n,d,f,?_⟩
  intro w k
  apply compactWord_of_germ_expansion F ζ hζ negativeParameter c _ d f _ w k
  intro u
  have hnhds : A ∈ 𝓝 (emb u) := mem_interior_iff_mem_nhds.mp (hKA ⟨u,rfl⟩)
  filter_upwards [hnhds] with a ha
  have hg : scalarQuotient F ζ hζ (amalgamation F ζ hζ (r*sectionTuple F ζ hζ a)) =
      finiteSlicePoint F ζ hζ c a := by
    rw [map_mul,map_mul,sectionTuple_insertion]
    change ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)) r * _ = _
    rw [hc]
    exact (finite_section_commute F ζ hζ c a).eq.symm
  simpa only [hg,originalUpper,RestrictedTensorSimple.stageInclusion] using he a ha
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
