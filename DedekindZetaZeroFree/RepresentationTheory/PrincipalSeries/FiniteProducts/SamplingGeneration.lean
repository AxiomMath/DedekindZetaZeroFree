module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.FixedTensorSections
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.CovariantSlices

@[expose] public section

noncomputable section
open scoped TensorProduct
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.NativeScalarFiniteSamplingGeneration
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductCovariantSlices renaming contraction → contraction
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductCovariantSlices renaming contractionMultilinear → contractionMultilinear
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductCovariantSlices renaming contraction_mapSingle → contraction_mapSingle

section Algebra
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable {κ : ι → Type} (b : ∀ i, Module.Basis (κ i) ℂ (V i))

private theorem contraction_coordinate (q : ι) (p : ∀ i, κ i)
    (x : PiTensorProduct ℂ V) :
    (b q).coord (p q) (contraction q (fun i => (b i).coord (p i)) x) =
      (Basis.piTensorProduct b).repr x p := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, contraction, PiTensorProduct.lift.tprod,
      Module.Basis.coord_apply, Basis.piTensorProduct_repr_tprod_apply,
      Finsupp.smul_apply, smul_eq_mul]
    change c * ((b q).repr ((∏ i ∈ Finset.univ.erase q, (b i).coord (p i) (x i)) • x q)) (p q) = _
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ q)]
  | add x y hx hy =>
    simpa only [map_add, Finsupp.add_apply] using congrArg₂ (· + ·) hx hy

include b in
private theorem mapSingle_eq_of_contractions (q : ι) (A : V q →ₗ[ℂ] V q)
    (x : PiTensorProduct ℂ V)
    (hx : ∀ p : ∀ i, κ i,
      A (contraction q (fun i => (b i).coord (p i)) x) =
        contraction q (fun i => (b i).coord (p i)) x) :
    PiTensorProduct.map (Function.update
      (fun _i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A) x = x := by
  apply (Basis.piTensorProduct b).repr.injective
  ext p
  rw [← contraction_coordinate b q p, ← contraction_coordinate b q p,
    contraction_mapSingle, hx]

private theorem map_eq_of_mapSingle (A : ∀ i, V i →ₗ[ℂ] V i)
    (x : PiTensorProduct ℂ V)
    (hx : ∀ q, PiTensorProduct.map (Function.update
      (fun _i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q (A q)) x = x) :
    PiTensorProduct.map A x = x := by
  have h (s : Finset ι) :
      PiTensorProduct.map (fun i => if i ∈ s then A i else LinearMap.id) x = x := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, ↓reduceIte, PiTensorProduct.map_id,
        LinearMap.id_apply]
    | @insert q s hq hs =>
      have he : (fun i => if i ∈ insert q s then A i else LinearMap.id) =
          fun i => (if i ∈ s then A i else LinearMap.id).comp
            (Function.update (fun _i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q (A q) i) := by
        funext i
        by_cases hi : i = q
        · subst i
          simp [hq]
        · simp [hi]
      rw [he, PiTensorProduct.map_comp, LinearMap.comp_apply, hx q, hs]
  simpa using h Finset.univ
end Algebra

section Functions
variable {ι : Type} [Fintype ι] [DecidableEq ι] {C : ι → Type} [∀ i, Fintype (C i)]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

 def functionTensorEquiv :
    PiTensorProduct ℂ (fun i => C i → V i) ≃ₗ[ℂ]
      ((∀ i, C i) → PiTensorProduct ℂ V) :=
  (PiTensorProduct.congr (fun i =>
    (Finsupp.linearEquivFunOnFinite ℂ (V i) (C i)).symm)).trans
    (PiTensorProduct.ofFinsuppEquiv.trans
      (Finsupp.linearEquivFunOnFinite ℂ (PiTensorProduct ℂ V) (∀ i, C i)))

 theorem functionTensorEquiv_formula
    (x : PiTensorProduct ℂ (fun i => C i → V i)) (c : ∀ i, C i) :
    functionTensorEquiv x c =
      PiTensorProduct.map (fun i => LinearMap.proj (c i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul]
    change r • functionTensorEquiv (PiTensorProduct.tprod ℂ x) c = _
    simp only [functionTensorEquiv, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
      PiTensorProduct.map_tprod, PiTensorProduct.ofFinsuppEquiv_apply,
      Finsupp.linearEquivFunOnFinite_apply, Finsupp.linearEquivFunOnFinite_symm_apply,
      LinearMap.proj_apply]
  | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

private theorem function_contraction_formula (q : ι)
    (l : ∀ i, V i →ₗ[ℂ] ℂ) (c : ∀ i, C i)
    (x : PiTensorProduct ℂ (fun i => C i → V i)) (a : C q) :
    contraction q (fun i => (l i).comp (LinearMap.proj (c i))) x a =
      contraction q l (functionTensorEquiv x (Function.update c q a)) := by
  rw [functionTensorEquiv_formula]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, PiTensorProduct.map_tprod, contraction, PiTensorProduct.lift.tprod]
    change r • ((∏ i ∈ Finset.univ.erase q, l i (x i (c i))) • x q a) =
      r • ((∏ i ∈ Finset.univ.erase q,
        l i (x i (Function.update c q a i))) • x q (Function.update c q a q))
    rw [Function.update_self]
    congr 2
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy
end Functions

section Actual
open scoped NumberField
open NumberField
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Fiber → Fiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFiber → ProductFiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFunctions → ProductFunctions
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation → tensorEvaluation
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming evaluation → evaluation
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming productCovariance → productCovariance
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation_covariant → tensorEvaluation_covariant
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation_smooth → tensorEvaluation_smooth
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming LocalCosets → LocalCosets
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming localCosets_finite → localCosets_finite
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming localFixedLevel → localFixedLevel
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming localSampling → localSampling
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming localSampling_injective → localSampling_injective
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming tensorCosetSampling → tensorCosetSampling
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming tensorCosetSampling_formula → tensorCosetSampling_formula
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming tensorEvaluation_injective → tensorEvaluation_injective
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductFixedLevel renaming productFixedLevel → productFixedLevel
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductFixedLevel renaming compactCosetSampling → compactCosetSampling
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductFixedLevel renaming productSection_mem_finite_level → productSection_mem_finite_level
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductCovariantSlices renaming contractedColumn_mem_sampling_range → contractedColumn_mem_sampling_range
open _root_.DedekindZetaZeroFree.NativeScalarFiniteFixedTensorSection renaming fixedTensorSection → fixedTensorSection
open _root_.DedekindZetaZeroFree.NativeScalarFiniteFixedTensorSection renaming fixedTensorSection_mem_range_iff → fixedTensorSection_mem_range_iff

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

local instance (q : S) : AddCommGroup (Source F ζ hζ M S q) :=
  FourierContinuation.SourceReconstruction.localPlusAdd F ζ hζ M (Sum.inr q.val)
local instance (q : S) : Module ℂ (Source F ζ hζ M S q) :=
  FourierContinuation.SourceReconstruction.localPlusModule F ζ hζ M (Sum.inr q.val)

local instance (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    Fintype (LocalCosets F ζ hζ M S U q) :=
  @Fintype.ofFinite _ (localCosets_finite F ζ hζ M S U q)

private theorem tensorSampling_eq_functionTensor
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (x : PiTensorProduct ℂ (fun q => localFixedLevel F ζ hζ M S U q)) :
    tensorCosetSampling F ζ hζ M S U x =
      functionTensorEquiv (PiTensorProduct.map (fun q => localSampling F ζ hζ M S U q) x) := by
  funext c
  rw [tensorCosetSampling_formula, functionTensorEquiv_formula]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, PiTensorProduct.mapIncl, PiTensorProduct.map_tprod]
    change r • PiTensorProduct.map
        (fun q => evaluation F ζ hζ M S q
          ((c q).out : Cover F ζ hζ S q))
        (PiTensorProduct.tprod ℂ (fun q => (x q).val)) = _
    simp only [PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

private theorem compactSampling_mem_tensorSampling
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (f : productFixedLevel F ζ hζ M S U) :
    compactCosetSampling F ζ hζ M S U f ∈ (tensorCosetSampling F ζ hζ M S U).range := by
  let sample q := localSampling F ζ hζ M S U q
  let retract q := LinearMap.leftInverse (K := ℂ) (sample q)
  have hleft q : (retract q).comp (sample q) = LinearMap.id :=
    LinearMap.leftInverse_comp_of_inj (K := ℂ)
      (LinearMap.ker_eq_bot.mpr (localSampling_injective F ζ hζ M S U q))
  let A q := (sample q).comp (retract q)
  have hfix q (v : LocalCosets F ζ hζ M S U q → Fiber F ζ hζ M S q)
      (hv : v ∈ (sample q).range) : A q v = v := by
    obtain ⟨w, rfl⟩ := hv
    change sample q (((retract q).comp (sample q)) w) = _
    rw [hleft, LinearMap.id_apply]
  let b q := Module.Basis.ofVectorSpace ℂ (Fiber F ζ hζ M S q)
  let B q := Pi.basis (fun _ : LocalCosets F ζ hζ M S U q => b q)
  let φ := compactCosetSampling F ζ hζ M S U f
  let x := functionTensorEquiv.symm φ
  have hx : functionTensorEquiv x = φ := LinearEquiv.apply_symm_apply _ _
  have hsingle q : PiTensorProduct.map (Function.update
      (fun i => LinearMap.id : ∀ i : S,
        (LocalCosets F ζ hζ M S U i → Fiber F ζ hζ M S i) →ₗ[ℂ]
        (LocalCosets F ζ hζ M S U i → Fiber F ζ hζ M S i)) q (A q)) x = x := by
    apply mapSingle_eq_of_contractions B q (A q) x
    intro p
    have hcoords : (fun i => (B i).coord (p i)) = fun i =>
        ((b i).coord (p i).2).comp (LinearMap.proj (p i).1) := by
      funext i
      ext v
      rfl
    rw [hcoords]
    apply hfix
    have hc := contractedColumn_mem_sampling_range F ζ hζ M S U q
      (fun i => (b i).coord (p i).2)
      (fun i => ((p i).1.out : Cover F ζ hζ S i)) f
    convert hc using 1
    funext a
    rw [function_contraction_formula, hx]
    change contraction q (fun i => (b i).coord (p i).2)
      (f.val (fun i => ((Function.update (fun i => (p i).1) q a i).out : Cover F ζ hζ S i))) = _
    apply congrArg (contraction q (fun i => (b i).coord (p i).2))
    apply congrArg f.val
    funext i
    by_cases hi : i = q
    · subst i
      simp
    · simp [hi]
  have hA : PiTensorProduct.map A x = x := map_eq_of_mapSingle A x hsingle
  refine ⟨PiTensorProduct.map retract x, ?_⟩
  rw [tensorSampling_eq_functionTensor]
  change functionTensorEquiv (((PiTensorProduct.map sample).comp (PiTensorProduct.map retract)) x) = φ
  rw [← PiTensorProduct.map_comp, hA, hx]

private theorem fixedTensorSection_surjective
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    Function.Surjective (fixedTensorSection F ζ hζ M S U) := by
  intro f
  exact (fixedTensorSection_mem_range_iff F ζ hζ M S U f).mpr
    (compactSampling_mem_tensorSampling F ζ hζ M S U f)

private theorem tensorEvaluation_surjective_sections
    (f : ProductFunctions F ζ hζ M S)
    (hcov : f ∈ productCovariance F ζ hζ M S)
    (hf : SmoothVector KPLocalPrincipalSeries.vectorRightTranslation f) :
    ∃ x : PiTensorProduct ℂ (Source F ζ hζ M S),
      tensorEvaluation F ζ hζ M S x = f := by
  obtain ⟨U, hU, _⟩ := productSection_mem_finite_level F ζ hζ M S f hcov hf
  obtain ⟨x, hx⟩ := fixedTensorSection_surjective F ζ hζ M S U ⟨f, hU⟩
  refine ⟨PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S U q) x, ?_⟩
  exact congrArg Subtype.val hx

 def productSections : Submodule ℂ (ProductFunctions F ζ hζ M S) where
  carrier := { f | f ∈ productCovariance F ζ hζ M S ∧
    SmoothVector KPLocalPrincipalSeries.vectorRightTranslation f }
  zero_mem' := ⟨(productCovariance F ζ hζ M S).zero_mem,
    (mem_smoothSubmodule _ _).mp (Submodule.zero_mem _)⟩
  add_mem' := by
    intro f h hf hh
    exact ⟨(productCovariance F ζ hζ M S).add_mem hf.1 hh.1,
      (mem_smoothSubmodule _ _).mp (Submodule.add_mem _
        ((mem_smoothSubmodule _ _).mpr hf.2) ((mem_smoothSubmodule _ _).mpr hh.2))⟩
  smul_mem' := by
    intro c f hf
    exact ⟨(productCovariance F ζ hζ M S).smul_mem c hf.1,
      (mem_smoothSubmodule _ _).mp (Submodule.smul_mem _ c
        ((mem_smoothSubmodule _ _).mpr hf.2))⟩

 def actualTensorSections :
    PiTensorProduct ℂ (Source F ζ hζ M S) →ₗ[ℂ] productSections F ζ hζ M S :=
  (tensorEvaluation F ζ hζ M S).codRestrict (productSections F ζ hζ M S)
    (fun x => ⟨tensorEvaluation_covariant F ζ hζ M S x,
      tensorEvaluation_smooth F ζ hζ M S x⟩)

 theorem actualTensorSections_bijective :
    Function.Bijective (actualTensorSections F ζ hζ M S) := by
  constructor
  · intro x y h
    exact tensorEvaluation_injective F ζ hζ M S (congrArg Subtype.val h)
  · intro f
    obtain ⟨x, hx⟩ := tensorEvaluation_surjective_sections F ζ hζ M S f.val
      f.property.1 f.property.2
    exact ⟨x, Subtype.ext hx⟩

end Actual
end DedekindZetaZeroFree.NativeScalarFiniteSamplingGeneration

end
