module

public import DedekindZetaZeroFree.Theta.Periods.ArchimedeanTensorProduct
public import DedekindZetaZeroFree.Theta.Whittaker.Tensors.ComplexSlices
public import DedekindZetaZeroFree.Theta.Periods.Wild.GlobalTensorEvaluation

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)

variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)

variable
    (hR : RootAligned R) (N : TraceHaarTransport R) (hC : C.exceptional = R.A.Sf)
    (u : ∀ j : bad R.A P C, Plus R.A P C j.val)
    (hspherical : ∀ z (p : KPFinitePlace F), p ∉ R.A.Sf →
      ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
        k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
      ∀ g, (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))).val z
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) =
        (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))).val z g)
    (hx : fourier R (KPWildKernelUpperBound.quotientHaar F)
      (coreResidue R P C (RestrictedTensorSimple.stageInclusion _ _ _
        ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ u))) 1 ≠ 0)

local notation "DC" => canonicalCovariantNative R P C μ hμ  hR N hC u hspherical hx
set_option quotPrecheck false
local notation "HC" => (DC).toGenerated.tensorHC
local notation "H" => actualImageData R P C μ hμ

open KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod WildCurrentGlobalMap
local notation "D" => (DC).tensorDetected.toTensorActions

def canonicalWildPeriod (T : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level (D).bad) (hT : places T ⊆ s.val)
    (x : ∀j : s.val,actualLocal R (D).finiteData j) (g : Group R) :
    AmbientTensor F T (fiber (D) T) →ₗ[ℂ] ℂ :=
  ((D).toTensorHC.literalPeriod g).comp
    ((RestrictedTensorSimple.stageInclusion _ (D).references (D).bad s).comp
      ((RestrictedTensorSimple.insert _ (fullFiller (D) s x)
        (places T) s.val hT).comp (reindex (D) T).toLinearMap))

theorem canonicalWildPeriod_eq (T : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level (D).bad) (hT : places T ⊆ s.val)
    (x : ∀j : s.val,actualLocal R (D).finiteData j) (g : Group R)
    (z : AmbientTensor F T (fiber (D) T)) :
    canonicalWildPeriod R P C μ hμ  hR N hC u hspherical hx T s hT x g z =
    fourier R (D).sources.dq (globalMap (D) T s hT x z) g := rfl

theorem canonicalWild_arch_background (T : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level (D).bad) (hT : places T ⊆ s.val)
    (x : ∀j : s.val,actualLocal R (D).finiteData j)
    (hdet : coreStageMultilinear _ (D).references (D).bad ((D).toTensorHC.literalPeriod 1) s x ≠ 0)
    (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) :
    ∃c : ℂ, ∀g : Group R,
      (∀w, PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 g w = 1) →
      ∀z : AmbientTensor F T (fiber (D) T),
      fourier R (D).sources.dq (globalMap (D) T s hT x z)
        (g*KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 a) =
      c*fourier R (D).sources.dq (globalMap (D) T s hT x z) g := by
  have hw : ∀w : InfinitePlace F, Sum.inl w∈s.val := fun w =>
    s.property (show Sum.inl w ∈ bad R.A P C from by
      simp [bad,KPGlobalResidualConstruction.ScalarAbsorption.fullBad])
  obtain ⟨c,hc⟩ := ComplexLines.actualStage_arch_background R P C μ hμ N  s x hdet hw a
  refine ⟨c,?_⟩
  intro g hg z
  have hp : ∀y : ∀q : T,fiber (D) T q,
      fourier R (D).sources.dq (globalMap (D) T s hT x (PiTensorProduct.tprod ℂ y))
        (g*KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 a) =
      c*fourier R (D).sources.dq (globalMap (D) T s hT x (PiTensorProduct.tprod ℂ y)) g := by
    intro y
    have he : ∀w, stageTuple (D) T s x y ⟨Sum.inl w,hw w⟩ = x ⟨Sum.inl w,hw w⟩ := by
      intro w
      simp [stageTuple,places]
    have hh := hc (stageTuple (D) T s x y) he g hg
    rw [globalMap_pure]
    exact hh
  change canonicalWildPeriod R P C μ hμ  hR N hC u hspherical hx T s hT x
      (g*KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 a) z =
    c*canonicalWildPeriod R P C μ hμ  hR N hC u hspherical hx T s hT x g z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod b y =>
    simp only [map_smul,smul_eq_mul,canonicalWildPeriod_eq]
    rw [hp y]
    ring
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add,h₁,h₂,mul_add]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
