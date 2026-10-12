module

public import DedekindZetaZeroFree.Eisenstein.Induction.RestrictedTensorRealization
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.InverseTensorSlots
public import DedekindZetaZeroFree.Metaplectic.Kubota.Induction.UnitaryRationalFiberComparison

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal BigOperators
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot
open KPGlobalTorusFiniteStages KPGlobalResidualConstruction
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
open PrincipalOfKP.ResidueCoreBridge.CanonicalBinding
open NativeStageSlot
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
local notation "Raw" => KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ
abbrev bad : Finset (KPHilbert.Place F) :=
  ScalarAbsorption.fullBad (A := InfinitePlace F) (Q := KPFinitePlace F) C.exceptional

abbrev Plus : KPHilbert.Place F → Type
  | Sum.inl _ => KPLiteralTensor.harmonicPlus
  | Sum.inr q => KPLocalPrincipalSeries.sectionSpace (C.canonical q).borel (C.polarization q) .plus 0

instance plusAdd (v : KPHilbert.Place F) : AddCommGroup (Plus A P C v) := by
  cases v <;> dsimp [Plus] <;> infer_instance
instance plusModule (v : KPHilbert.Place F) : Module ℂ (Plus A P C v) := by
  cases v <;> dsimp [Plus] <;> infer_instance

def matrix (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) : ComplexGL2 :=
  Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).toRingHom g.g

variable (s : RestrictedTensorSimple.Level (bad A P C))
variable (x : ∀ j : s.val, Plus A P C j.val)
variable (g : KPAdelicCoverRestrictedProduct.RestrictedCover F A.zeta12 A.primitive_zeta12)

def finiteTuple (x : ∀ j : s.val, Plus A P C j.val)
    (g : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) (q : s.val.toRight) : LocalFiber F ζ hζ P C q.val :=
  (x ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩).val
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (g (Sum.inr q.val)))

def finiteFiber (x : ∀ j : s.val, Plus A P C j.val)
    (g : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) : KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  EisensteinReferenceSections.SourceTensor.realization F ζ hζ P C
    (RestrictedTensorSimple.stageInclusion (LocalFiber F ζ hζ P C)
      (localReference F ζ hζ P C) C.exceptional (ScalarAbsorption.rightLevel C.exceptional s)
      (PiTensorProduct.tprod ℂ (finiteTuple A P C s x g)))

def finiteScalar : ℂ :=
  (productUnitaryToRational F ζ hζ P (finiteFiber A P C s x g)).val.val 1

def archComplement (w : InfinitePlace F) : ℂ :=
  ∏ j : s.val, match j with
    | ⟨Sum.inl u, hu⟩ => if u = w then 1 else
        (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (Sum.inl u)).epsilon : ℂ) *
          (x ⟨Sum.inl u, hu⟩).val (matrix A u (g (Sum.inl u)))
    | ⟨Sum.inr _, _⟩ => 1

def coefficient (w : InfinitePlace F) : ℂ :=
  archComplement A P C s x g w * finiteScalar A P C s x g *
    (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (Sum.inl w)).epsilon : ℂ)

def positive (w : InfinitePlace F) : PrincipalSeries positiveParameter →L[ℂ] ℂ :=
  (coefficient A P C s x g w) •
    ⟨{ toFun := fun f => f (matrix A w (g (Sum.inl w)))
       map_add' := by intros; rfl
       map_smul' := by intros; rfl },
     KPCplxHarmonicExtraction.principalSeries_evaluation_continuous
       positiveParameter (matrix A w (g (Sum.inl w)))⟩

def negative (w : InfinitePlace F) : PrincipalSeries negativeParameter →L[ℂ] ℂ :=
  (positive A P C s x g w).comp inverse

@[simp] theorem negative_apply (w : InfinitePlace F) (f : PrincipalSeries negativeParameter) :
    negative A P C s x g w f =
      coefficient A P C s x g w * (inverse f) (matrix A w (g (Sum.inl w))) := rfl

theorem negative_integral (w : InfinitePlace F) (f : KPLiteralTensor.harmonicPlus) :
    negative A P C s x g w
      (KPCplxIntertwinerEigenvalues.standardIntertwiner (1 : ℂˣ) f.val) =
      coefficient A P C s x g w * f.val (matrix A w (g (Sum.inl w))) := by
  rw [negative_apply, inverse_integral]

def matrixSlot (w : InfinitePlace F) (a : ComplexGL2) :
    PrincipalSeries negativeParameter →ₗ[ℂ] ℂ where
  toFun f := coefficient A P C s x g w * (inverse f) (matrix A w (g (Sum.inl w)) * a)
  map_add' := by intro f h; simp [mul_add]
  map_smul' := by intro c f; simp [mul_left_comm]

end DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot

end
