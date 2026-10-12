module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandraHeckeLieCovariance
public import DedekindZetaZeroFree.Nonvanishing.Descent.SeedOrbitGeneration
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandra.ScalarWordTranslations

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources NonDegenerate

section Algebraic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable {A : ι → Type*} (op : ∀ i, A i → Module.End ℂ (V i))

def tensorSlot (i : ι) (T : Module.End ℂ (V i)) : Module.End ℂ (PiTensorProduct ℂ V) :=
  PiTensorProduct.map (Function.update (fun j => LinearMap.id : ∀ j, Module.End ℂ (V j)) i T)

theorem tensorSlot_tprod (i : ι) (T : Module.End ℂ (V i)) (v : ∀ i, V i) :
    tensorSlot i T (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (Function.update v i (T (v i))) := by
  rw [tensorSlot, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem tupleOperator_mem_of_slot_stable
    (M : Submodule ℂ (PiTensorProduct ℂ V))
    (hM : ∀ i a x, x ∈ M → tensorSlot i (op i a) x ∈ M)
    (a : ∀ i, A i) (x : PiTensorProduct ℂ V) (hx : x ∈ M) :
    tupleOperator op a x ∈ M := by
  let f (I : Finset ι) : ∀ i, Module.End ℂ (V i) :=
    fun i => if i ∈ I then op i (a i) else LinearMap.id
  have h : ∀ I : Finset ι, PiTensorProduct.map (f I) x ∈ M := by
    intro I
    induction I using Finset.induction_on with
    | empty => simpa [f, PiTensorProduct.map_id] using hx
    | @insert i I hi ih =>
      have he : PiTensorProduct.map (f (insert i I)) =
          (tensorSlot i (op i (a i))).comp (PiTensorProduct.map (f I)) := by
        rw [tensorSlot, ← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases hji : j = i
        · subst j
          simp [f, hi]
        · simp [f, hji]
      rw [he]
      exact hM i (a i) _ ih
  simpa only [f, Finset.mem_univ, if_true, tupleOperator] using h Finset.univ

theorem stage_le_of_cyclic_slot_stability
    (v : ∀ i, V i) (hv : tupleOrbitSpan op v = ⊤)
    (M : Submodule ℂ (PiTensorProduct ℂ V))
    (hM : ∀ i a x, x ∈ M → tensorSlot i (op i a) x ∈ M)
    (hseed : PiTensorProduct.tprod ℂ v ∈ M) : M = ⊤ := by
  apply top_unique
  rw [← hv]
  apply Submodule.span_le.mpr
  rintro y ⟨a, rfl⟩
  exact tupleOperator_mem_of_slot_stable op M hM a _ hseed
end Algebraic

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

def NativeSlotComparisons (D : Faithful R N) : Prop :=
  ∀ t : RestrictedTensorSimple.Level D.bad,
    let L := D.coreMap.comp (RestrictedTensorSimple.stageInclusion _ D.references D.bad t)
    (∀ (w : NumberField.InfinitePlace F) (hw : Sum.inl w ∈ t.val)
      (k : KPCplxCharacterHaar.ComplexSU2),
      ∃ a : Group R, ∀ x,
        L (tensorSlot ⟨Sum.inl w, hw⟩ (complexGenerator (Sum.inl k)) x) =
          KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a (L x)) ∧
    (∀ (w : NumberField.InfinitePlace F) (hw : Sum.inl w ∈ t.val) (b : Fin 6),
      ∃ j : Fin (KPContActualSphericalRightFieldIdentification.groupDimension F), ∀ x,
        L (tensorSlot ⟨Sum.inl w, hw⟩ (complexGenerator (Sum.inr b)) x) =
          KPContActualSphericalRightFieldIdentification.actualRight
            F R.A.zeta12 R.A.primitive_zeta12 j (L x)) ∧
    (∀ (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val) (b : LocalOperation R (Sum.inr q)),
      ∃ a : Group R, ∀ x,
        L (tensorSlot ⟨Sum.inr q, hq⟩ (localOperation R D.finiteData (Sum.inr q) b) x) =
          KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a (L x))

theorem tensorSlot_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (i : ι) : tensorSlot i (LinearMap.id : Module.End ℂ (V i)) = LinearMap.id := by
  unfold tensorSlot
  rw [Function.update_eq_self, PiTensorProduct.map_id]

theorem tensorSlot_comp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (i : ι) (A B : Module.End ℂ (V i)) :
    tensorSlot i (A.comp B) = (tensorSlot i A).comp (tensorSlot i B) := by
  rw [tensorSlot, tensorSlot, tensorSlot, ← PiTensorProduct.map_comp]
  congr 1
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem complex_word_slot_stable (D : Faithful R N) (hD : NativeSlotComparisons D)
    (t : RestrictedTensorSimple.Level D.bad)
    (w : NumberField.InfinitePlace F) (hw : Sum.inl w ∈ t.val)
    (a : List ComplexGenerator)
    (x : RestrictedTensorSimple.Stage (actualLocal R D.finiteData) t.val)
    (hx : D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad t x) ∈
      hcHeckeSpan D.realization) :
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad t
      (tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
        ⟨Sum.inl w, hw⟩ (complexWord a) x)) ∈ hcHeckeSpan D.realization := by
  let L := D.coreMap.comp (RestrictedTensorSimple.stageInclusion _ D.references D.bad t)
  change L (tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
    ⟨Sum.inl w, hw⟩ (complexWord a) x) ∈ hcHeckeSpan D.realization
  induction a with
  | nil =>
    change L (tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
      ⟨Sum.inl w, hw⟩ LinearMap.id x) ∈ hcHeckeSpan D.realization
    rw [tensorSlot_id]
    exact hx
  | cons b a ih =>
    let y := tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
      ⟨Sum.inl w, hw⟩ (complexWord a) x
    have he : tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
        ⟨Sum.inl w, hw⟩ (complexWord (b :: a)) x =
        tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
          ⟨Sum.inl w, hw⟩ (complexGenerator b) y := by
      rw [complexWord, tensorSlot_comp]
      rfl
    exact (congrArg (fun z => z ∈ hcHeckeSpan D.realization) (congrArg L he)).mpr (by
      cases b with
      | inl k =>
        obtain ⟨g, hg⟩ := (hD t).1 w hw k
        exact (congrArg (fun z => z ∈ hcHeckeSpan D.realization) (hg y)).mpr
          (hcHeckeSpan_right D.realization ih g)
      | inr b =>
        obtain ⟨j, hj⟩ := (hD t).2.1 w hw b
        exact (congrArg (fun z => z ∈ hcHeckeSpan D.realization) (hj y)).mpr
          (hcHeckeSpan_actualRight D.realization ih j))

theorem generated_of_native_slot_comparisons (D : Faithful R N)
    (hD : NativeSlotComparisons D) : ∀ x, D.coreMap x ∈ hcHeckeSpan D.realization := by
  obtain ⟨s, v, hs, hseed, _, hv⟩ := D.initial_pure_nonzero
  apply generated_of_detected_seed_orbits D.toDictionary s v hs hv
  intro t a
  let L := D.coreMap.comp (RestrictedTensorSimple.stageInclusion _ D.references D.bad t)
  let M := (hcHeckeSpan D.realization).comap L
  have hM : ∀ (i : t.val) (a : LocalOperation R i)
      (x : RestrictedTensorSimple.Stage (actualLocal R D.finiteData) t.val), x ∈ M →
      tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
        i (localOperation R D.finiteData i a) x ∈ M := by
    rintro ⟨i, hi⟩ a x hx
    cases i with
    | inl w =>
      change D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad t
        (tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
          ⟨Sum.inl w, hi⟩ (complexWord a) x)) ∈ hcHeckeSpan D.realization
      exact complex_word_slot_stable D hD t w hi a x hx
    | inr q =>
      obtain ⟨g, hg⟩ := (hD t).2.2 q hi a
      change L (tensorSlot (V := fun i : t.val => actualLocal R D.finiteData i.val)
        ⟨Sum.inr q, hi⟩ (localOperation R D.finiteData (Sum.inr q) a) x) ∈ hcHeckeSpan D.realization
      exact (congrArg (fun z => z ∈ hcHeckeSpan D.realization) (hg x)).mpr
        (hcHeckeSpan_right D.realization hx g)
  apply tupleOperator_mem_of_slot_stable (fun i : t.val => localOperation R D.finiteData i) M hM
  change L (PiTensorProduct.tprod ℂ (insertedSeed D.toDictionary s t v)) ∈ hcHeckeSpan D.realization
  change D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad t
    (PiTensorProduct.tprod ℂ (insertedSeed D.toDictionary s t v))) ∈ _
  rw [insertedSeed_pin D.toDictionary s t hs v hseed, D.selected_eq]
  exact scalarWordSpan_le_hcHeckeSpan D.realization
    (Submodule.subset_span ⟨(D.probe, []), rfl⟩)

def faithfulGeneratedOfNativeSlots (D : Faithful R N) (hD : NativeSlotComparisons D) :
    Generated R N where
  toFaithful := D
  generated := generated_of_native_slot_comparisons D hD

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
