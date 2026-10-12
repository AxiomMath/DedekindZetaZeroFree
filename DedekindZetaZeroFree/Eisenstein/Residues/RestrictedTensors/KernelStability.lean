module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalActionAlgebrasAndCommutants
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.OperatorWords

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources HCGeneration KPGlobalResidualConstruction
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ
local notation "A" => actualLocalAlgebra R H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem tensorSlot_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (i : ι) (a b : Module.End ℂ (V i)) :
    tensorSlot i (a+b) = tensorSlot i a + tensorSlot i b := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, tensorSlot_tprod]
  exact (PiTensorProduct.tprod ℂ).map_update_add x i (a (x i)) (b (x i))

private theorem tensorSlot_smul_id {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (i : ι) (c : ℂ) :
    tensorSlot i (c • (LinearMap.id : Module.End ℂ (V i))) = c • LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply,
    LinearMap.id_apply, tensorSlot_tprod]
  simpa only [Function.update_eq_self] using
    (PiTensorProduct.tprod ℂ).map_update_smul x i c (x i)

theorem actualCoreResidue_generator_zero (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level E) (b : StageGenerator R P C s)
    (x : RestrictedTensorSimple.Stage W s.val)
    (hx : actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s x) = 0) :
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s
      (actualStageGenerator R P C μ hμ s b x)) = 0 := by
  rw [actualCoreResidue_stage_generator, hx]
  cases b <;> funext g <;> simp [stageScalarGenerator, KPLiteralRaw.rightAction, actualRight]

private theorem stage_kernel_algebra (N : TraceHaarTransport R)
    (s : RestrictedTensorSimple.Level E) (j : s.val) (a : A j.val)
    (x : RestrictedTensorSimple.Stage W s.val)
    (hx : actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s x) = 0) :
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s
      (tensorSlot (V := fun k : s.val => W k.val) j a.val x)) = 0 := by
  let K := LinearMap.ker ((actualCoreResidue R P C μ hμ N).comp
    (RestrictedTensorSimple.stageInclusion W e E s))
  change x ∈ K at hx
  change tensorSlot (V := fun k : s.val => W k.val) j a.val x ∈ K
  obtain ⟨j,hj⟩ := j
  cases j with
  | inl v =>
    obtain ⟨a,ha⟩ := a
    change tensorSlot (V := fun k : s.val => W k.val) ⟨Sum.inl v,hj⟩ a x ∈ K
    change a ∈ NativeComplexHCSource.algebra NativeComplexHCOperators.operators at ha
    induction ha using Algebra.adjoin_induction generalizing x with
    | mem a ha =>
      rcases ha with ⟨k,rfl⟩ | ⟨i,rfl⟩
      · have he : actualStageGenerator R P C μ hμ s (.compact v k) =
            tensorSlot (V := fun k : s.val => W k.val) ⟨Sum.inl v,hj⟩
              (complexCoreCompactLinearMap k) := by rfl
        have hh := actualCoreResidue_generator_zero R P C μ hμ N s (.compact v k) x hx
        exact (congrArg (fun T : Module.End ℂ (RestrictedTensorSimple.Stage W s.val) =>
          actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s (T x))) he).symm.trans hh
      · have hh := actualCoreResidue_generator_zero R P C μ hμ N s
          (.lie ((actualLieIndexEquiv (F := F)).symm (v,i))) x hx
        have he : actualStageGenerator R P C μ hμ s
            (.lie ((actualLieIndexEquiv (F := F)).symm (v,i))) =
            tensorSlot (V := fun k : s.val => W k.val) ⟨Sum.inl v,hj⟩
              (NativeComplexHCOperators.operators i) := by
          let slot (wb : InfinitePlace F × Fin 6) :
              Module.End ℂ (RestrictedTensorSimple.Stage W s.val) :=
            tensorSlot (V := fun k : s.val => W k.val)
              ⟨Sum.inl wb.1, s.property (by simp [bad, ScalarAbsorption.fullBad])⟩
              (localOperation R H (Sum.inl wb.1) [.inr wb.2])
          change slot (actualLieIndexEquiv (F := F)
            ((actualLieIndexEquiv (F := F)).symm (v,i))) = slot (v,i)
          exact congrArg slot ((actualLieIndexEquiv (F := F)).apply_symm_apply (v,i))
        exact (congrArg (fun T : Module.End ℂ (RestrictedTensorSimple.Stage W s.val) =>
          actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s (T x))) he).symm.trans hh
    | algebraMap c =>
      rw [show algebraMap ℂ (Module.End ℂ complexCore) c = c • LinearMap.id from rfl,
        tensorSlot_smul_id]
      exact K.smul_mem c hx
    | add a b ha hb iha ihb =>
      rw [tensorSlot_add]
      exact K.add_mem (iha x hx) (ihb x hx)
    | mul a b ha hb iha ihb =>
      rw [show a*b = a.comp b from rfl, tensorSlot_comp]
      exact iha _ (ihb x hx)
  | inr q =>
    obtain ⟨a,ha⟩ := a
    change tensorSlot (V := fun k : s.val => W k.val) ⟨Sum.inr q,hj⟩ a x ∈ K
    change a ∈ NativeRepresentationAlgebra.algebra (actualFiniteRepresentation R H q) at ha
    induction ha using Algebra.adjoin_induction generalizing x with
    | mem a ha =>
      obtain ⟨g,rfl⟩ := ha
      obtain ⟨raw,hr⟩ := QuotientGroup.mk'_surjective
        (KPPGLLocalCover.splitScalarSubgroup F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) g
      have hh := actualCoreResidue_generator_zero R P C μ hμ N s (.finite q hj raw) x hx
      have he : actualStageGenerator R P C μ hμ s (.finite q hj raw) =
          tensorSlot (V := fun k : s.val => W k.val) ⟨Sum.inr q,hj⟩
            (actualFiniteRepresentation R H q g) := by
        change tensorSlot (V := fun k : s.val => W k.val) ⟨Sum.inr q,hj⟩
          (actualFiniteRepresentation R H q (KPPGLLocalCover.coverQuotient F R.A.zeta12
            R.A.primitive_zeta12 (Sum.inr q) raw)) = _
        exact congrArg (fun g => tensorSlot (V := fun k : s.val => W k.val)
          ⟨Sum.inr q,hj⟩ (actualFiniteRepresentation R H q g)) hr
      exact (congrArg (fun T : Module.End ℂ (RestrictedTensorSimple.Stage W s.val) =>
        actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.stageInclusion W e E s (T x))) he).symm.trans hh
    | algebraMap c =>
      rw [show algebraMap ℂ (Module.End ℂ (W (.inr q))) c = c • LinearMap.id from rfl,
        tensorSlot_smul_id]
      exact K.smul_mem c hx
    | add a b ha hb iha ihb =>
      rw [tensorSlot_add]
      exact K.add_mem (iha x hx) (ihb x hx)
    | mul a b ha hb iha ihb =>
      rw [show a*b = a.comp b from rfl, tensorSlot_comp]
      exact iha _ (ihb x hx)

private theorem slotAction_stage
    (s : RestrictedTensorSimple.Level E) (j : KPHilbert.Place F) (hj : j ∈ s.val)
    (a : A j) (x : RestrictedTensorSimple.Stage W s.val) :
    RestrictedTensorSimple.slotAction W (fun v => ↥(A v)) e E j a
      (RestrictedTensorSimple.stageInclusion W e E s x) =
    RestrictedTensorSimple.stageInclusion W e E s (tensorSlot (V := fun k : s.val => W k.val) ⟨j,hj⟩ a.val x) := by
  have he : (RestrictedTensorSimple.slotAction W (fun v => ↥(A v)) e E j a).comp
      (RestrictedTensorSimple.stageInclusion W e E s) =
      (RestrictedTensorSimple.stageInclusion W e E s).comp (tensorSlot (V := fun k : s.val => W k.val) ⟨j,hj⟩ a.val) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      tensorSlot_tprod]
    apply (RestrictedTensorSimple.slotAction_pure W (fun v => ↥(A v)) e E j a s hj v).trans
    apply congrArg (RestrictedTensorSimple.stageInclusion W e E s)
    apply congrArg (PiTensorProduct.tprod ℂ)
    funext k
    by_cases hk : k = ⟨j,hj⟩
    · subst k
      simp only [Function.update_self]
      rfl
    · simp only [Function.update, dif_neg hk]
  exact LinearMap.congr_fun he x

private theorem kernel_slot_stable (N : TraceHaarTransport R)
    (j : KPHilbert.Place F) (a : A j) (x : RestrictedTensorSimple.Core W e E)
    (hx : actualCoreResidue R P C μ hμ N x = 0) :
    actualCoreResidue R P C μ hμ N (RestrictedTensorSimple.slotAction W (fun v => ↥(A v)) e E j a x) = 0 := by
  let : Nonempty (RestrictedTensorSimple.Level E) := ⟨⟨E,le_rfl⟩⟩
  obtain ⟨s,y,hy⟩ := Module.DirectLimit.exists_of x
  change RestrictedTensorSimple.stageInclusion W e E s y = x at hy
  let t : RestrictedTensorSimple.Level E := ⟨Insert.insert j s.val,
    s.property.trans (Finset.subset_insert j s.val)⟩
  let z := RestrictedTensorSimple.transition W e E s t (Finset.subset_insert j s.val) y
  have hz : RestrictedTensorSimple.stageInclusion W e E t z = x := by
    rw [← hy]
    exact Module.DirectLimit.of_f
  have ht : j ∈ t.val := Finset.mem_insert_self j s.val
  rw [← hz, slotAction_stage]
  exact stage_kernel_algebra R P C μ hμ N t ⟨j,ht⟩ a z (hz.symm ▸ hx)

theorem actualCoreResidue_kernel_stable (N : TraceHaarTransport R)
    (a : RestrictedTensorSimple.actionAlgebra W (fun v => ↥(A v)) e E)
    (x : RestrictedTensorSimple.Core W e E)
    (hx : actualCoreResidue R P C μ hμ N x = 0) :
    actualCoreResidue R P C μ hμ N (a • x) = 0 := by
  let K := LinearMap.ker (actualCoreResidue R P C μ hμ N)
  change x ∈ K at hx
  change a.val x ∈ K
  obtain ⟨a,ha⟩ := a
  change a x ∈ K
  induction ha using Algebra.adjoin_induction generalizing x with
  | mem a ha =>
    obtain ⟨j,b,rfl⟩ := ha
    exact kernel_slot_stable R P C μ hμ N j b x hx
  | algebraMap c => exact K.smul_mem c hx
  | add a b ha hb iha ihb => exact K.add_mem (iha x hx) (ihb x hx)
  | mul a b ha hb iha ihb => exact iha _ (ihb x hx)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
