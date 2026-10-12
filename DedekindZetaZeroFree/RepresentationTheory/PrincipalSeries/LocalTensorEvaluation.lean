module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment
public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors
public import DedekindZetaZeroFree.Metaplectic.Kubota.Induction.UnitaryRationalFiberComparison

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField IsDedekindDomain
open KPGlobalTorusFiniteStages KPLocalPrincipalSeries
open PrincipalOfKP.ResidueCoreBridge.CanonicalBinding
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)

abbrev Plus : KPHilbert.Place F → Type
  | Sum.inl _ => KPLiteralTensor.harmonicPlus
  | Sum.inr q => sectionSpace (C.canonical q).borel (C.polarization q) .plus 0

instance plusAdd (v : KPHilbert.Place F) : AddCommGroup (Plus A P C v) := by
  cases v <;> dsimp [Plus] <;> infer_instance
instance plusModule (v : KPHilbert.Place F) : Module ℂ (Plus A P C v) := by
  cases v <;> dsimp [Plus] <;> infer_instance

abbrev Fiber := KPGlobalResidualConstruction.ScalarAbsorption.FullV
  (A := InfinitePlace F) (fun q => LocalFiber F A.zeta12 A.primitive_zeta12 P C q)
abbrev reference := KPGlobalResidualConstruction.ScalarAbsorption.fullReference
  (A := InfinitePlace F) (fun q => LocalFiber F A.zeta12 A.primitive_zeta12 P C q)
  (localReference F A.zeta12 A.primitive_zeta12 P C)
abbrev bad := KPGlobalResidualConstruction.ScalarAbsorption.fullBad
  (A := InfinitePlace F) C.exceptional

def finiteTensorMap : RestrictedTensorSimple.Core
    (LocalFiber F A.zeta12 A.primitive_zeta12 P C)
    (localReference F A.zeta12 A.primitive_zeta12 P C) C.exceptional →ₗ[ℂ]
    KPGlobalTorusFunctionData.TorusSmoothUnion F A.zeta12 A.primitive_zeta12
      (productModel F A.zeta12 A.primitive_zeta12 P) :=
  (KPGlobalResidualConstruction.TorusCoreComparison.finiteTensorCore_lift_exists
    F A.zeta12 A.primitive_zeta12 P C).choose

theorem finiteTensorMap_stage (s : RestrictedTensorSimple.Level C.exceptional)
    (x : RestrictedTensorSimple.Stage (LocalFiber F A.zeta12 A.primitive_zeta12 P C) s.val) :
    finiteTensorMap A P C (RestrictedTensorSimple.stageInclusion
      (LocalFiber F A.zeta12 A.primitive_zeta12 P C)
      (localReference F A.zeta12 A.primitive_zeta12 P C) C.exceptional s x) =
      finiteTensorRealization F A.zeta12 A.primitive_zeta12 P C s.val s.property x :=
  (KPGlobalResidualConstruction.TorusCoreComparison.finiteTensorCore_lift_exists
    F A.zeta12 A.primitive_zeta12 P C).choose_spec.2.2 s.val s.property x

def comparison : RestrictedTensorSimple.Core (Fiber A P C) (reference A P C) (bad A P C) →ₗ[ℂ]
    ↥(KPGlobalResidualConstruction.smoothRationalFiber F A.zeta12 A.primitive_zeta12) :=
  (productUnitaryToRational F A.zeta12 A.primitive_zeta12 P).comp
    ((finiteTensorMap A P C).comp
      (KPGlobalResidualConstruction.ScalarAbsorption.absorb
        (A := InfinitePlace F) (LocalFiber F A.zeta12 A.primitive_zeta12 P C)
        (localReference F A.zeta12 A.primitive_zeta12 P C) C.exceptional))

theorem comparison_stage (s : RestrictedTensorSimple.Level (bad A P C))
    (x : RestrictedTensorSimple.Stage (Fiber A P C) s.val) :
    comparison A P C (RestrictedTensorSimple.stageInclusion
      (Fiber A P C) (reference A P C) (bad A P C) s x) =
    productUnitaryToRational F A.zeta12 A.primitive_zeta12 P
      (finiteTensorMap A P C (RestrictedTensorSimple.stageInclusion
        (LocalFiber F A.zeta12 A.primitive_zeta12 P C)
        (localReference F A.zeta12 A.primitive_zeta12 P C) C.exceptional
        (KPGlobalResidualConstruction.ScalarAbsorption.rightLevel C.exceptional s)
        (KPGlobalResidualConstruction.ScalarAbsorption.stageEquiv
          (LocalFiber F A.zeta12 A.primitive_zeta12 P C) s.val x))) := by
  simp only [comparison, LinearMap.comp_apply,
    KPGlobalResidualConstruction.ScalarAbsorption.absorb_stage]

def complexMatrix (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 (Sum.inl w)) :
    KPCplxCharacterHaar.ComplexGL2 :=
  Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).toRingHom g.g

def localValue (v : KPHilbert.Place F) (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 v)
    (f : Plus A P C v) : Fiber A P C v :=
  match v with
  | Sum.inl w => (KPSourceConvention.ordinaryGenuineCharacter F A.zeta12 A.primitive_zeta12
      g.epsilon : ℂ) * f.val (complexMatrix A w g)
  | Sum.inr q => f.val (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) g)

def localValueMap (v : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 v) :
    Plus A P C v →ₗ[ℂ] Fiber A P C v where
  toFun := localValue A P C v g
  map_add' := by intro f h; cases v <;> simp [localValue, mul_add]
  map_smul' := by intro c f; cases v <;> simp [localValue, mul_left_comm]

def rationalEvaluation :
    ↥(KPGlobalResidualConstruction.smoothRationalFiber F A.zeta12 A.primitive_zeta12) →ₗ[ℂ] ℂ where
  toFun f := f.val.val 1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

abbrev Raw := KPAdelicCoverRestrictedProduct.RestrictedCover F A.zeta12 A.primitive_zeta12

def rawStageValue (s : RestrictedTensorSimple.Level (bad A P C)) (g : Raw A) :
    PiTensorProduct ℂ (fun j : s.val => Plus A P C j.val) →ₗ[ℂ] ℂ :=
  ((rationalEvaluation A).comp ((comparison A P C).comp
    (RestrictedTensorSimple.stageInclusion (Fiber A P C) (reference A P C) (bad A P C) s))).comp
      (PiTensorProduct.map (fun j => localValueMap A P C j.val (g j.val)))

def rawStageInsertion (s : RestrictedTensorSimple.Level (bad A P C)) :
    PiTensorProduct ℂ (fun j : s.val => Plus A P C j.val) →ₗ[ℂ] (Raw A → ℂ) where
  toFun x g := rawStageValue A P C s g x
  map_add' := by intro x y; funext g; exact map_add _ x y
  map_smul' := by intro c x; funext g; exact map_smul _ c x

theorem rawStageInsertion_pure (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw A) :
    rawStageInsertion A P C s (PiTensorProduct.tprod ℂ x) g =
      (comparison A P C (RestrictedTensorSimple.stageInclusion
        (Fiber A P C) (reference A P C) (bad A P C) s
        (PiTensorProduct.tprod ℂ (fun j => localValue A P C j.val (g j.val) (x j))))).val.val 1 := by
  simp [rawStageInsertion, rawStageValue, localValueMap, rationalEvaluation,
    PiTensorProduct.map_tprod]

def archScalar (v : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 v) (f : Plus A P C v) : ℂ :=
  match v with
  | Sum.inl w => localValue A P C (Sum.inl w) g f
  | Sum.inr _ => 1

def finiteValue (v : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 v) (f : Plus A P C v) : Fiber A P C v :=
  match v with
  | Sum.inl _ => 1
  | Sum.inr q => localValue A P C (Sum.inr q) g f

theorem localValue_factor (v : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 v) (f : Plus A P C v) :
    localValue A P C v g f = archScalar A P C v g f • finiteValue A P C v g f := by
  cases v <;> simp [archScalar, finiteValue]

theorem rawStageInsertion_arch_factorization (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw A) :
    rawStageInsertion A P C s (PiTensorProduct.tprod ℂ x) g =
      (∏ j : s.val, archScalar A P C j.val (g j.val) (x j)) *
        (comparison A P C (RestrictedTensorSimple.stageInclusion
          (Fiber A P C) (reference A P C) (bad A P C) s
          (PiTensorProduct.tprod ℂ (fun j => finiteValue A P C j.val (g j.val) (x j))))).val.val 1 := by
  rw [rawStageInsertion_pure]
  simp_rw [localValue_factor]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
  simp only [map_smul, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def atFrozenPlaces (R : PrincipalMellin.ActualRecipe S η)
    (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
    (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
    (hCS : C.exceptional ⊆ R.A.Sf) : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P where
  canonical := C.canonical
  polarization := C.polarization
  subgroup_matches := C.subgroup_matches
  character_matches := C.character_matches
  exceptional := R.A.Sf
  unramified q hq := C.unramified q (fun h => hq (hCS h))
  actual_compact q hq := C.actual_compact q (fun h => hq (hCS h))

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
