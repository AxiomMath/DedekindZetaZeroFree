module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.NegativeSlotChartJets
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalTensorEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal BigOperators
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot
open KPGlobalTorusFiniteStages KPGlobalResidualConstruction
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
open PrincipalOfKP.ResidueCoreBridge.CanonicalBinding
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option diagnostics true
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
local notation "Raw" => KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ
local notation "V" => ScalarAbsorption.FullV (LocalFiber F ζ hζ P C)
local notation "e" => ScalarAbsorption.fullReference (LocalFiber F ζ hζ P C) (localReference F ζ hζ P C)

def inducingValue (v : KPHilbert.Place F) (f : Plus A P C v)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ v) : V v :=
  match v with
  | Sum.inl w => (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ g.epsilon : ℂ) *
      f.val (matrix A w g)
  | Sum.inr q => f.val (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)

def tensorValue (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw) : ℂ :=
  (productUnitaryToRational F ζ hζ P
    (EisensteinReferenceSections.SourceTensor.realization F ζ hζ P C
      (ScalarAbsorption.absorb (LocalFiber F ζ hζ P C) (localReference F ζ hζ P C) C.exceptional
        (RestrictedTensorSimple.stageInclusion V e (bad A P C) s
          (PiTensorProduct.tprod ℂ (fun j => inducingValue A P C j.val (x j) (g j.val))))))).val.val 1

theorem tensorValue_formula (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw) :
    tensorValue A P C s x g =
      (∏ w : s.val.toLeft,
        (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (Sum.inl w.val)).epsilon : ℂ) *
          (x ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩).val
            (matrix A w.val (g (Sum.inl w.val)))) * finiteScalar A P C s x g := by
  unfold tensorValue
  rw [ScalarAbsorption.absorb_stage, ScalarAbsorption.stageEquiv_pure,
    map_smul, map_smul, map_smul]
  rfl

theorem tensorValue_shared (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw) :
    tensorValue A P C s x g =
      LiteralSource.rawStageInsertion A P C s (PiTensorProduct.tprod ℂ x) g := by
  rw [LiteralSource.rawStageInsertion_pure, LiteralSource.comparison_stage,
    ScalarAbsorption.stageEquiv_pure]
  simp only [map_smul]
  rw [LiteralSource.finiteTensorMap_stage]
  unfold tensorValue
  rw [ScalarAbsorption.absorb_stage, ScalarAbsorption.stageEquiv_pure]
  simp only [map_smul]
  rw [EisensteinReferenceSections.SourceTensor.realization_stage]
  rfl

 def stageSplit (s : Finset (KPHilbert.Place F)) : s ≃ s.toLeft ⊕ s.toRight where
  toFun j := match j with
    | ⟨Sum.inl w, hw⟩ => Sum.inl ⟨w, Finset.mem_toLeft.mpr hw⟩
    | ⟨Sum.inr q, hq⟩ => Sum.inr ⟨q, Finset.mem_toRight.mpr hq⟩
  invFun j := match j with
    | Sum.inl w => ⟨Sum.inl w.val, Finset.mem_toLeft.mp w.property⟩
    | Sum.inr q => ⟨Sum.inr q.val, Finset.mem_toRight.mp q.property⟩
  left_inv j := by rcases j with ⟨j, hj⟩; cases j <;> rfl
  right_inv j := by cases j <;> rfl

theorem archComplement_left (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw) (w : InfinitePlace F) :
    archComplement A P C s x g w = ∏ u : s.val.toLeft,
      if u.val = w then 1 else
        (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (Sum.inl u.val)).epsilon : ℂ) *
          (x ⟨Sum.inl u.val, Finset.mem_toLeft.mp u.property⟩).val
            (matrix A u.val (g (Sum.inl u.val))) := by
  unfold archComplement
  rw [← (stageSplit s.val).symm.prod_comp, Fintype.prod_sum_type]
  simp only [stageSplit, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk, Finset.prod_const_one,
    mul_one]

theorem finiteScalar_update (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s.val) (f : KPLiteralTensor.harmonicPlus) :
    finiteScalar A P C s (Function.update x ⟨Sum.inl w, hw⟩ f) g =
      finiteScalar A P C s x g := by
  unfold finiteScalar finiteFiber
  congr 3

theorem negative_tensor_pin (s : RestrictedTensorSimple.Level (bad A P C))
    (x : ∀ j : s.val, Plus A P C j.val) (g : Raw) (w : InfinitePlace F)
    (hw : Sum.inl w ∈ s.val) (f : KPLiteralTensor.harmonicPlus) :
    negative A P C s x g w
      (KPCplxIntertwinerEigenvalues.standardIntertwiner (1 : ℂˣ) f.val) =
        tensorValue A P C s (Function.update x ⟨Sum.inl w, hw⟩ f) g := by
  rw [negative_integral, tensorValue_formula, finiteScalar_update,
    coefficient, archComplement_left]
  let i : s.val.toLeft := ⟨w, Finset.mem_toLeft.mpr hw⟩
  let b : s.val.toLeft → ℂ := fun u =>
    (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (Sum.inl u.val)).epsilon : ℂ) *
      (x ⟨Sum.inl u.val, Finset.mem_toLeft.mp u.property⟩).val
        (matrix A u.val (g (Sum.inl u.val)))
  have he : (fun u : s.val.toLeft =>
    (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (Sum.inl u.val)).epsilon : ℂ) *
      (Function.update x ⟨Sum.inl w, hw⟩ f ⟨Sum.inl u.val, Finset.mem_toLeft.mp u.property⟩).val
        (matrix A u.val (g (Sum.inl u.val)))) =
    Function.update b i
      ((KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (g (Sum.inl w)).epsilon : ℂ) *
        f.val (matrix A w (g (Sum.inl w)))) := by
    funext u
    by_cases hu : u = i
    · subst u
      simp [i]
    · have hv : u.val ≠ w := fun h => hu (Subtype.ext h)
      simp [Function.update_of_ne hu, b, Function.update_of_ne
        (show (⟨Sum.inl u.val, Finset.mem_toLeft.mp u.property⟩ : s.val) ≠ ⟨Sum.inl w, hw⟩
          from fun h => hv (Sum.inl.inj (congrArg Subtype.val h)))]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have hp : (∏ u : s.val.toLeft, if u.val = w then (1 : ℂ) else b u) =
      ∏ u ∈ (Finset.univ : Finset s.val.toLeft).erase i, b u := by
    have hi : (fun u : s.val.toLeft => if u.val = w then (1 : ℂ) else b u) =
        Function.update b i 1 := by
      funext u
      by_cases hu : u = i
      · subst u; simp [i]
      · have hv : u.val ≠ w := fun h => hu (Subtype.ext h)
        simp [hu, hv]
    rw [hi, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
      Finset.sdiff_singleton_eq_erase]
  change (((∏ u : s.val.toLeft, if u.val = w then 1 else b u) * _) * _) * _ = _
  rw [hp]
  ring

end DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot

end
