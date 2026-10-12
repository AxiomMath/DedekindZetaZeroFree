module

public import DedekindZetaZeroFree.Theta.Periods.WildArchimedeanFactors
public import DedekindZetaZeroFree.Theta.Periods.ArchimedeanFourierCenter
public import DedekindZetaZeroFree.Theta.Periods.Wild.JointFormFaithfulness

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
open WildFiniteExteriorAssembly KPAdelicCoverRestrictedProduct
local notation "D" => (DC).tensorDetected.toTensorActions

theorem archInsertion_commute_projection_one (g : Group R)
    (hg : ∀w, PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 g w = 1)
    (a : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) :
    Commute g (KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 a) := by
  obtain ⟨E,hE,hp,hs,hk,_⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F R.A.zeta12 R.A.primitive_zeta12
  have hm : g ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F R.A.zeta12 R.A.primitive_zeta12 := by
    rw [←hk]
    change PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 g = 1
    funext w
    exact hg w
  exact (RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F R.A.zeta12 R.A.primitive_zeta12 a ⟨g,hm⟩).symm

theorem canonicalJointArchExterior (T : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level (D).bad) (hT : places T ⊆ s.val)
    (x : ∀j : s.val,actualLocal R (D).finiteData j)
    (hdet : coreStageMultilinear _ (D).references (D).bad ((D).toTensorHC.literalPeriod 1) s x ≠ 0) :
    JointArchExterior (D) T s hT x := by
  intro h hh a ha
  let b := PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 (rawGlobal (R := R) h)
  obtain ⟨ε,hε⟩ := CurrentRawArchCenter.raw_arch_fourier R h hh
  obtain ⟨c,hc⟩ := canonicalWild_arch_background R P C μ hμ  hR N hC u hspherical hx T s hT x hdet b
  let χ : ℂ := KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 ε
  refine ⟨χ*c,?_⟩
  intro z
  have hg : ∀w, PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12
      (rawGlobal (R := R) a) w = 1 := fun w => CurrentOutputExtension.raw_arch_projection_one R a w (ha w)
  have hcomm := (archInsertion_commute_projection_one R (rawGlobal (R := R) a) hg b).eq.symm
  have hreg : globalMap (D) T s hT x z ∈ regularResidualFunctions R := by
    dsimp only [globalMap,LinearMap.comp_apply]
    exact (D).regular _
  have hcenter := hε (D).sources.dq (globalMap (D) T s hT x z) hreg (rawGlobal (R := R) a)
  have harch := hc (rawGlobal (R := R) a) hg z
  calc
    _ = χ * fourier R (D).sources.dq (globalMap (D) T s hT x z)
      (KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 b * rawGlobal (R := R) a) := hcenter
    _ = χ * fourier R (D).sources.dq (globalMap (D) T s hT x z)
      (rawGlobal (R := R) a * KPSmoothActualFlowData.archimedeanInsertion F R.A.zeta12 R.A.primitive_zeta12 b) :=
      congrArg (fun t => χ * fourier R (D).sources.dq (globalMap (D) T s hT x z) t) hcomm
    _ = χ * (c * fourier R (D).sources.dq (globalMap (D) T s hT x z) (rawGlobal (R := R) a)) :=
      congrArg (fun t:ℂ => χ*t) harch
    _ = _ := (mul_assoc _ _ _).symm

theorem canonicalJointForm_injective (T : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level (D).bad) (hT : places T ⊆ s.val)
    (x : ∀j : s.val,actualLocal R (D).finiteData j)
    (hdet : coreStageMultilinear _ (D).references (D).bad ((D).toTensorHC.literalPeriod 1) s x ≠ 0)
    (ht : ∀q : KPFinitePlace F, Sum.inr q ∉ places T → WildCurrentTameExterior.tameSlot (Sum.inr q))
    (q : T) : Function.Injective (WildCurrentJointForm.jointForm (D) T s hT x) :=
  jointForm_injective_of_arch_exterior (DC).tensorDetected T s hT x hdet ht
    (canonicalJointArchExterior R P C μ hμ  hR N hC u hspherical hx T s hT x hdet) q

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
