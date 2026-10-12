module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.ScalarTensorEquivalence
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.IndependentSlicesAndUniformBands

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.NativeScalarMixedTensorGeneration
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open KPLiteralScalarArchIndependentSlices KPLiteralScalarArchUniformBands
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices renaming harmonicBand_finite → harmonicBand_finite
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices renaming finite_interpolation → finite_interpolation
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarInverse renaming scalarSections → scalarSections
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarInverse renaming scalarTensorEquiv → scalarTensorEquiv
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarInverse renaming scalarTensorEquiv_pure → scalarTensorEquiv_pure

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι]

def familyTranslate (k : ι → ComplexSU2) :
    (Y → multiPrincipalSeries positiveParameter ι) →ₗ[ℂ]
      (Y → multiPrincipalSeries positiveParameter ι) :=
  LinearMap.pi (fun y => (multiTranslate positiveParameter k).comp (LinearMap.proj y))

def familyOrbit (h : Y → multiPrincipalSeries positiveParameter ι) :
    Submodule ℂ (Y → multiPrincipalSeries positiveParameter ι) :=
  Submodule.span ℂ (Set.range (fun k => familyTranslate k h))

open _root_.DedekindZetaZeroFree.KPLiteralScalarArchUniformBands renaming multiTranslate_mul → multiTranslate_mul
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchUniformBands renaming harmonicBand_mono → harmonicBand_mono

omit [Fintype ι] in
private theorem familyTranslate_mul (k l : ι → ComplexSU2)
    (h : Y → multiPrincipalSeries positiveParameter ι) :
    familyTranslate k (familyTranslate l h) = familyTranslate (k * l) h := by
  funext y
  exact multiTranslate_mul positiveParameter k l (h y)

omit [Fintype ι] in
private theorem familyOrbit_stable (h : Y → multiPrincipalSeries positiveParameter ι)
    (k : ι → ComplexSU2) (v : Y → multiPrincipalSeries positiveParameter ι)
    (hv : v ∈ familyOrbit h) : familyTranslate k v ∈ familyOrbit h := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    rw [familyTranslate_mul]
    exact Submodule.subset_span ⟨k * l, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

theorem familyOrbit_uniform_bands (h : Y → multiPrincipalSeries positiveParameter ι)
    [FiniteDimensional ℂ (familyOrbit h)] (y : Y) (i : ι)
    (a : ι → ComplexGL2) :
    evaluateSlice positiveParameter i a (h y) ∈
      harmonicBand positiveParameter (Module.finrank ℂ (familyOrbit h)) := by
  let L := ((evaluateSlice positiveParameter i a).comp (LinearMap.proj y)).comp
    (familyOrbit h).subtype
  have hinv : IsKInvariant positiveParameter L.range := by
    intro k f hf
    obtain ⟨v, rfl⟩ := hf
    obtain ⟨u, hu⟩ := k.property
    refine ⟨⟨familyTranslate (Function.update (fun _ => 1) i u) v.val,
      familyOrbit_stable h _ v.val v.property⟩, ?_⟩
    change evaluateSlice positiveParameter i a
      (multiTranslate positiveParameter (Function.update (fun _ => 1) i u) (v.val y)) = _
    rw [slice_slot_translate]
    change Matrix.ProjGenLinGroup.mk (complexSU2Embedding u) = k.val at hu
    rw [hu]
    rfl
  have hmem : h ∈ familyOrbit h := by
    have heq : familyTranslate (fun _ => 1) h = h := by
      funext y
      apply Subtype.ext
      funext a
      change (h y).val (fun j => a j * complexSU2Embedding 1) = (h y).val a
      simp
    exact Submodule.subset_span ⟨fun _ => 1, heq⟩
  have hr : evaluateSlice positiveParameter i a (h y) ∈ L.range := ⟨⟨h, hmem⟩, rfl⟩
  exact harmonicBand_mono positiveParameter (LinearMap.finrank_range_le L)
    (invariant_subspace_le_band positiveParameter L.range hinv hr)

 def bandInclusion (N : ℕ) :
    harmonicBand positiveParameter N →ₗ[ℂ] KPLiteralTensor.harmonicPlus :=
  (harmonicBand positiveParameter N).inclusion (by
    apply Finset.sup_le
    intro ℓ _
    exact le_iSup _ ℓ)

def bandTensorEvaluation (N : ℕ) :
    PiTensorProduct ℂ (fun _ : ι => harmonicBand positiveParameter N) →ₗ[ℂ]
      ((ι → ComplexGL2) → ℂ) :=
  plusTensorEvaluation.comp (PiTensorProduct.map (fun _ => bandInclusion N))

omit [DecidableEq ι] in
private theorem bandTensorEvaluation_finite (N : ℕ) :
    Module.Finite ℂ (bandTensorEvaluation (ι := ι) N).range := by
  let : ∀ _ : ι, Module.Finite ℂ (harmonicBand positiveParameter N) :=
    fun _ => harmonicBand_finite _ _
  let : Module.Finite ℂ (PiTensorProduct ℂ (fun _ : ι => harmonicBand positiveParameter N)) :=
    @PiTensorProduct.finite ℂ _ ι _ (fun _ : ι => harmonicBand positiveParameter N)
      (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => harmonicBand_finite _ _)
  exact Module.Finite.range (bandTensorEvaluation N)

theorem family_value_mem_band_range (h : Y → multiPrincipalSeries positiveParameter ι)
    [FiniteDimensional ℂ (familyOrbit h)] (y : Y) :
    (h y).val ∈ (bandTensorEvaluation (Module.finrank ℂ (familyOrbit h))).range := by
  let N := Module.finrank ℂ (familyOrbit h)
  let S : Submodule ℂ (ComplexGL2 → ℂ) := (harmonicBandEvaluation positiveParameter N).range
  let : Module.Finite ℂ (harmonicBand positiveParameter N) := harmonicBand_finite _ _
  have hs : ∀ i a, (fun x => (h y).val (Function.update a i x)) ∈ S := by
    intro i a
    exact ⟨⟨evaluateSlice positiveParameter i a (h y), familyOrbit_uniform_bands h y i a⟩, rfl⟩
  have hp := independent_slices_mem_product_span (fun _ : ι => S) (h y).val hs
  apply (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨f, rfl⟩
  choose b hb using fun i => (f i).property
  refine ⟨PiTensorProduct.tprod ℂ b, ?_⟩
  funext a
  simp only [bandTensorEvaluation, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    plusTensorEvaluation_pure]
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (hb i) (a i)

theorem family_finite_interpolation (h : Y → multiPrincipalSeries positiveParameter ι)
    [FiniteDimensional ℂ (familyOrbit h)] :
    ∃ (n : ℕ) (a : Fin n → (ι → ComplexGL2))
      (t : Fin n → PiTensorProduct ℂ (fun _ : ι => KPLiteralTensor.harmonicPlus)),
      ∀ y x, (h y).val x = ∑ j, (h y).val (a j) * plusTensorEvaluation (t j) x := by
  let L := bandTensorEvaluation (ι := ι) (Module.finrank ℂ (familyOrbit h))
  let : Module.Finite ℂ L.range := bandTensorEvaluation_finite _
  obtain ⟨n, a, b, hb⟩ := finite_interpolation L.range
  choose t ht using fun j => (b j).property
  refine ⟨n, a, fun j => PiTensorProduct.map (fun _ => bandInclusion _) (t j), ?_⟩
  intro y x
  have hi := hb ⟨(h y).val, family_value_mem_band_range h y⟩ x
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrFun (ht j) x

section ActualFinitePlaces
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local instance (q : S) : AddCommGroup (Source F ζ hζ M S q) :=
  FourierContinuation.SourceReconstruction.localPlusAdd F ζ hζ M (Sum.inr q.val)
local instance (q : S) : Module ℂ (Source F ζ hζ M S q) :=
  FourierContinuation.SourceReconstruction.localPlusModule F ζ hζ M (Sum.inr q.val)

def finiteTensorEvaluation : PiTensorProduct ℂ (Source F ζ hζ M S) →ₗ[ℂ]
    (ProductCover F ζ hζ S → ℂ) :=
  (scalarSections F ζ hζ M S).subtype.comp (scalarTensorEquiv F ζ hζ M S).toLinearMap

def mixedTensorEvaluation :
    (PiTensorProduct ℂ (fun _ : ι => KPLiteralTensor.harmonicPlus)) ⊗[ℂ]
      (PiTensorProduct ℂ (Source F ζ hζ M S)) →ₗ[ℂ]
        ((ι → ComplexGL2) → ProductCover F ζ hζ S → ℂ) :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun v a g => plusTensorEvaluation u a * finiteTensorEvaluation F ζ hζ M S v g
          map_add' := by intro v w; ext a g; simp [mul_add]
          map_smul' := by intro c v; ext a g; simp [mul_left_comm] }
      map_add' := by intro u w; ext v a g; simp [add_mul]
      map_smul' := by intro c u; ext v a g; simp [mul_assoc] }

omit [DecidableEq ι] in
@[simp] theorem mixedTensorEvaluation_tmul
    (u : PiTensorProduct ℂ (fun _ : ι => KPLiteralTensor.harmonicPlus))
    (v : PiTensorProduct ℂ (Source F ζ hζ M S))
    (a : ι → ComplexGL2) (g : ProductCover F ζ hζ S) :
    mixedTensorEvaluation F ζ hζ M S (u ⊗ₜ[ℂ] v) a g =
      plusTensorEvaluation u a * finiteTensorEvaluation F ζ hζ M S v g := rfl

theorem mixed_tensor_exists
    (h : ProductCover F ζ hζ S → multiPrincipalSeries positiveParameter ι)
    [FiniteDimensional ℂ (familyOrbit h)]
    (hfinite : ∀ a : ι → ComplexGL2,
      (fun g => (h g).val a) ∈ scalarSections F ζ hζ M S) :
    ∃ t : (PiTensorProduct ℂ (fun _ : ι => KPLiteralTensor.harmonicPlus)) ⊗[ℂ]
        (PiTensorProduct ℂ (Source F ζ hζ M S)),
      ∀ a g, mixedTensorEvaluation F ζ hζ M S t a g = (h g).val a := by
  obtain ⟨n, a, u, hu⟩ := family_finite_interpolation h
  let v : Fin n → PiTensorProduct ℂ (Source F ζ hζ M S) := fun j =>
    (scalarTensorEquiv F ζ hζ M S).symm ⟨fun g => (h g).val (a j), hfinite (a j)⟩
  have hv (j : Fin n) (g : ProductCover F ζ hζ S) :
      finiteTensorEvaluation F ζ hζ M S (v j) g = (h g).val (a j) := by
    have he := (scalarTensorEquiv F ζ hζ M S).apply_symm_apply
      ⟨fun g => (h g).val (a j), hfinite (a j)⟩
    exact congrArg (fun f : scalarSections F ζ hζ M S => f.val g) he
  refine ⟨∑ j, u j ⊗ₜ[ℂ] v j, ?_⟩
  intro x g
  simp only [map_sum, Finset.sum_apply, mixedTensorEvaluation_tmul, hv]
  simpa only [mul_comm] using (hu g x).symm

abbrev mixedSource : ι ⊕ S → Type :=
  Sum.elim (fun _ => KPLiteralTensor.harmonicPlus) (Source F ζ hζ M S)

local instance (j : ι ⊕ S) : AddCommGroup (mixedSource (ι := ι) F ζ hζ M S j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance
local instance (j : ι ⊕ S) : Module ℂ (mixedSource (ι := ι) F ζ hζ M S j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance

def allSlotEvaluation : PiTensorProduct ℂ (mixedSource (ι := ι) F ζ hζ M S) →ₗ[ℂ]
    ((ι → ComplexGL2) → ProductCover F ζ hζ S → ℂ) :=
  (mixedTensorEvaluation F ζ hζ M S).comp
    (PiTensorProduct.tmulEquivDep ℂ (mixedSource (ι := ι) F ζ hζ M S)).symm.toLinearMap

@[simp] theorem allSlotEvaluation_pure
    (x : ∀ j : ι ⊕ S, mixedSource (ι := ι) F ζ hζ M S j)
    (a : ι → ComplexGL2) (g : ProductCover F ζ hζ S) :
    allSlotEvaluation F ζ hζ M S (PiTensorProduct.tprod ℂ x) a g =
      (∏ i, (x (Sum.inl i)).val (a i)) *
        ∏ q : S, ((x (Sum.inr q)).val (g q)).val 1 := by
  change mixedTensorEvaluation F ζ hζ M S
    ((PiTensorProduct.tmulEquivDep ℂ (mixedSource (ι := ι) F ζ hζ M S)).symm
      (PiTensorProduct.tprod ℂ x)) a g = _
  rw [PiTensorProduct.tmulEquivDep_symm_apply, mixedTensorEvaluation_tmul]
  change plusTensorEvaluation (PiTensorProduct.tprod ℂ
      (fun i : ι => (x (Sum.inl i) : KPLiteralTensor.harmonicPlus))) a *
    finiteTensorEvaluation F ζ hζ M S (PiTensorProduct.tprod ℂ
      (fun q : S => (x (Sum.inr q) : Source F ζ hζ M S q))) g = _
  rw [plusTensorEvaluation_pure]
  congr 1
  exact scalarTensorEquiv_pure F ζ hζ M S (fun q => x (Sum.inr q)) g

theorem allSlotEvaluation_finite_action
    (q : S) (b : Cover F ζ hζ S q)
    (t : PiTensorProduct ℂ (mixedSource (ι := ι) F ζ hζ M S))
    (a : ι → ComplexGL2) (g : ProductCover F ζ hζ S) :
    allSlotEvaluation F ζ hζ M S
      (PiTensorProduct.map (Function.update
        (fun _j => LinearMap.id : ∀ j : ι ⊕ S,
          mixedSource (ι := ι) F ζ hζ M S j →ₗ[ℂ] mixedSource (ι := ι) F ζ hζ M S j)
        (Sum.inr q) (KPLocalPrincipalSeries.IPlus (M q.val).borel
          (M q.val).polarization b)) t) a g =
      allSlotEvaluation F ζ hζ M S t a
        (g * Function.update (fun j : S => (1 : Cover F ζ hζ S j)) q b) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [PiTensorProduct.map_tprod]
    simp only [allSlotEvaluation_pure]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro i _
      simp only [Function.update_of_ne (Sum.inl_ne_inr), LinearMap.id_apply]
    · apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = q
      · subst j
        simp only [Function.update_self, Pi.mul_apply]
        rfl
      · have hsum : (Sum.inr j : ι ⊕ S) ≠ Sum.inr q := fun h => hj (Sum.inr.inj h)
        simp only [Function.update_of_ne hsum, LinearMap.id_apply,
          Pi.mul_apply, Function.update_of_ne hj, mul_one]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) hx hy

theorem all_slot_tensor_exists
    (h : ProductCover F ζ hζ S → multiPrincipalSeries positiveParameter ι)
    [FiniteDimensional ℂ (familyOrbit h)]
    (hfinite : ∀ a : ι → ComplexGL2,
      (fun g => (h g).val a) ∈ scalarSections F ζ hζ M S) :
    ∃ t : PiTensorProduct ℂ (mixedSource (ι := ι) F ζ hζ M S),
      ∀ a g, allSlotEvaluation F ζ hζ M S t a g = (h g).val a := by
  obtain ⟨t, ht⟩ := mixed_tensor_exists F ζ hζ M S h hfinite
  refine ⟨PiTensorProduct.tmulEquivDep ℂ (mixedSource (ι := ι) F ζ hζ M S) t, ?_⟩
  intro a g
  change mixedTensorEvaluation F ζ hζ M S
    ((PiTensorProduct.tmulEquivDep ℂ (mixedSource (ι := ι) F ζ hζ M S)).symm
      ((PiTensorProduct.tmulEquivDep ℂ (mixedSource (ι := ι) F ζ hζ M S)) t)) a g = _
  rw [LinearEquiv.symm_apply_apply]
  exact ht a g

end ActualFinitePlaces
end DedekindZetaZeroFree.NativeScalarMixedTensorGeneration

end
