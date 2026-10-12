module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.FixedLevelSections
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.LocalFixedLevelSampling

@[expose] public section

noncomputable section
open scoped TensorProduct
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.NativeScalarFiniteProductCovariantSlices
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
 def contractionMultilinear [DecidableEq ι] (q : ι) (l : ∀ i, V i →ₗ[ℂ] ℂ) : MultilinearMap ℂ V (V q) :=
  .mk' (fun x => (∏ i ∈ Finset.univ.erase q, l i (x i)) • x q)
    (by
    intro x i a b
    by_cases hi : i = q
    · subst i
      have hh (z : V q) : (∏ j ∈ Finset.univ.erase q, l j (Function.update x q z j)) = ∏ j ∈ Finset.univ.erase q, l j (x j) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hh (a + b), hh a, hh b]
      simp only [Function.update_self, smul_add]
    · have hm : i ∈ Finset.univ.erase q := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
      have hh (z : V i) : (∏ j ∈ Finset.univ.erase q, l j (Function.update x i z j)) =
          l i z * ∏ j ∈ (Finset.univ.erase q).erase i, l j (x j) := by
        rw [← Finset.mul_prod_erase _ _ hm]
        simp only [Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hh (a + b), hh a, hh b]
      simp only [Function.update_of_ne (Ne.symm hi), map_add, add_mul, add_smul]
    )
    (by
    intro x i c a
    by_cases hi : i = q
    · subst i
      have hh (z : V q) : (∏ j ∈ Finset.univ.erase q, l j (Function.update x q z j)) = ∏ j ∈ Finset.univ.erase q, l j (x j) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hh (c • a), hh a]
      simp only [Function.update_self, smul_smul, mul_comm]
    · have hm : i ∈ Finset.univ.erase q := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
      have hh (z : V i) : (∏ j ∈ Finset.univ.erase q, l j (Function.update x i z j)) =
          l i z * ∏ j ∈ (Finset.univ.erase q).erase i, l j (x j) := by
        rw [← Finset.mul_prod_erase _ _ hm]
        simp only [Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hh (c • a), hh a]
      simp only [Function.update_of_ne (Ne.symm hi), map_smul, smul_eq_mul, mul_assoc, mul_smul]
    )
 def contraction [DecidableEq ι] (q : ι) (l : ∀ i, V i →ₗ[ℂ] ℂ) := PiTensorProduct.lift (contractionMultilinear q l)
 theorem contraction_mapSingle [DecidableEq ι] (q : ι) (l : ∀ i, V i →ₗ[ℂ] ℂ) (A : V q →ₗ[ℂ] V q) (x : PiTensorProduct ℂ V) :
  contraction q l (PiTensorProduct.map (Function.update (fun i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A) x) = A (contraction q l x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, PiTensorProduct.map_tprod, contraction, PiTensorProduct.lift.tprod, map_smul]
    change c • ((∏ i ∈ Finset.univ.erase q, l i (Function.update (fun i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A i (x i))) • (Function.update (fun i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A q (x q))) = _
    have hh : (∏ i ∈ Finset.univ.erase q, l i (Function.update (fun i => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) q A i (x i))) = ∏ i ∈ Finset.univ.erase q, l i (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Function.update_of_ne (Finset.ne_of_mem_erase hi), LinearMap.id_apply]
    rw [hh, Function.update_self]
    change c • _ = c • A ((∏ i ∈ Finset.univ.erase q, l i (x i)) • x q)
    rw [map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

section Actual
open scoped NumberField
open NumberField
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Fiber → Fiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFiber → ProductFiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFunctions → ProductFunctions
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming productCovariance → productCovariance
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming localFixedLevel → localFixedLevel
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming localSampling → localSampling
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel renaming LocalCosets → LocalCosets
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductFixedLevel renaming productFixedLevel → productFixedLevel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

 def sliceFunction (q : S) (l : ∀ i : S, Fiber F ζ hζ M S i →ₗ[ℂ] ℂ)
    (g : ProductCover F ζ hζ S) (f : ProductFunctions F ζ hζ M S) :
    Cover F ζ hζ S q → Fiber F ζ hζ M S q :=
  fun a => contraction q l (f (Function.update g q a))

 theorem sliceFunction_covariant
    (q : S) (l : ∀ i : S, Fiber F ζ hζ M S i →ₗ[ℂ] ℂ)
    (g : ProductCover F ζ hζ S) (f : ProductFunctions F ζ hζ M S)
    (hf : f ∈ productCovariance F ζ hζ M S)
    (b : (M q.val).borel.B) (a : Cover F ζ hζ S q) :
    sliceFunction F ζ hζ M S q l g f (b * a) =
      KPLocalPrincipalSeries.inducingAction (M q.val).borel
        (M q.val).polarization .plus 0 b
        (sliceFunction F ζ hζ M S q l g f a) := by
  classical
  let bs : ∀ i : S, (M i.val).borel.B := Function.update (fun i => 1) q b
  have hg : (fun i => (bs i : Cover F ζ hζ S i) * Function.update g q a i) =
      Function.update g q (b * a) := by
    funext i
    by_cases hi : i = q
    · subst i
      simp [bs]
    · simp [bs, Function.update_of_ne hi]
  have hA : (fun i => KPLocalPrincipalSeries.inducingAction (M i.val).borel
      (M i.val).polarization .plus 0 (bs i)) =
      Function.update (fun i => LinearMap.id : ∀ i : S, Fiber F ζ hζ M S i →ₗ[ℂ] Fiber F ζ hζ M S i)
        q (KPLocalPrincipalSeries.inducingAction (M q.val).borel
          (M q.val).polarization .plus 0 b) := by
    funext i
    by_cases hi : i = q
    · subst i
      simp [bs]
    · simp [bs, Function.update_of_ne hi, map_one]
      rfl
  unfold sliceFunction
  rw [← hg, hf bs (Function.update g q a), hA]
  exact contraction_mapSingle (V := Fiber F ζ hζ M S) q l
    (KPLocalPrincipalSeries.inducingAction (M q.val).borel
      (M q.val).polarization .plus 0 b) (f (Function.update g q a))

 theorem sliceFunction_fixed
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (q : S) (l : ∀ i : S, Fiber F ζ hζ M S i →ₗ[ℂ] ℂ)
    (g : ProductCover F ζ hζ S) (f : productFixedLevel F ζ hζ M S U)
    (j : Cover F ζ hζ S q) (hj : j ∈ U q) (a : Cover F ζ hζ S q) :
    sliceFunction F ζ hζ M S q l g f.val (a * j) =
      sliceFunction F ζ hζ M S q l g f.val a := by
  let js : ProductCover F ζ hζ S := Function.update (fun i => 1) q j
  have hjs : ∀ i, js i ∈ U i := by
    intro i
    by_cases hi : i = q
    · subst i
      simpa [js] using hj
    · simp [js, Function.update_of_ne hi]
  have hg : Function.update g q a * js = Function.update g q (a * j) := by
    funext i
    by_cases hi : i = q
    · subst i
      simp [js]
    · simp [js, Function.update_of_ne hi]
  unfold sliceFunction
  rw [← hg, f.property.2 js hjs]

 def covariantSlice
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (q : S) (l : ∀ i : S, Fiber F ζ hζ M S i →ₗ[ℂ] ℂ)
    (g : ProductCover F ζ hζ S) (f : productFixedLevel F ζ hζ M S U) :
    localFixedLevel F ζ hζ M S U q := by
  let φ := sliceFunction F ζ hζ M S q l g f.val
  have hφ : ∀ j ∈ U q, ∀ a, φ (a * j) = φ a :=
    sliceFunction_fixed F ζ hζ M S U q l g f
  refine ⟨⟨φ, ?_⟩, hφ⟩
  refine ⟨sliceFunction_covariant F ζ hζ M S q l g f.val f.property.1, ?_⟩
  refine ⟨U q, ?_⟩
  intro j hj
  funext a
  exact hφ j hj a

private theorem covariantSlice_formula
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (q : S) (l : ∀ i : S, Fiber F ζ hζ M S i →ₗ[ℂ] ℂ)
    (g : ProductCover F ζ hζ S) (f : productFixedLevel F ζ hζ M S U)
    (a : Cover F ζ hζ S q) :
    (covariantSlice F ζ hζ M S U q l g f).val.val a =
      contraction q l (f.val (Function.update g q a)) := rfl

 theorem contractedColumn_mem_sampling_range
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (q : S) (l : ∀ i : S, Fiber F ζ hζ M S i →ₗ[ℂ] ℂ)
    (g : ProductCover F ζ hζ S) (f : productFixedLevel F ζ hζ M S U) :
    (fun c : LocalCosets F ζ hζ M S U q =>
      contraction q l (f.val (Function.update g q (c.out : Cover F ζ hζ S q)))) ∈
      (localSampling F ζ hζ M S U q).range := by
  refine LinearMap.mem_range.mpr ⟨covariantSlice F ζ hζ M S U q l g f, ?_⟩
  funext c
  exact covariantSlice_formula F ζ hζ M S U q l g f _

end Actual
end DedekindZetaZeroFree.NativeScalarFiniteProductCovariantSlices

end
