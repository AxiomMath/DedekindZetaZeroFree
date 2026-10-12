module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.IntegralTensorEquivalence

@[expose] public section

noncomputable section
open scoped NumberField TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TraceBaseChange

variable (F : Type*) [Field F] [NumberField F]

instance fieldIntegerAlgebra (p : Nat.Primes) (v : PlacesAbove F p) :
    Algebra ℤ_[p] (v.val.adicCompletion F) :=
  ((fieldScalarMap F p v).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

instance fieldIntegerTower (p : Nat.Primes) (v : PlacesAbove F p) :
    IsScalarTower ℤ_[p] ℚ_[p] (v.val.adicCompletion F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def localTraceAt (p : Nat.Primes) (v : PlacesAbove F p) :
    v.val.adicCompletion F →ₗ[ℚ_[p]] ℚ_[p] :=
  Algebra.trace ℚ_[p] (v.val.adicCompletion F)

def productTrace (p : Nat.Primes) : FieldProduct F p →ₗ[ℚ_[p]] ℚ_[p] :=
  ∑ v : PlacesAbove F p, (localTraceAt F p v).comp (LinearMap.proj (R := ℚ_[p]) v)

def padicIntegerLattice (p : Nat.Primes) : Submodule ℤ_[p] ℚ_[p] :=
  LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])

def localTraceDual (p : Nat.Primes) (v : PlacesAbove F p) :
    Submodule ℤ_[p] (v.val.adicCompletion F) :=
  ⨅ y : v.val.adicCompletionIntegers F,
    (padicIntegerLattice p).comap
      (((localTraceAt F p v).comp (LinearMap.mulRight ℚ_[p] (y : v.val.adicCompletion F))).restrictScalars ℤ_[p])

def integralProductInclusion (p : Nat.Primes) : IntegralProduct F p →+* FieldProduct F p :=
  RingHom.pi fun v => (v.val.adicCompletionIntegers F).subtype.comp
    (Pi.evalRingHom (fun w : PlacesAbove F p => w.val.adicCompletionIntegers F) v)

def productTraceDual (p : Nat.Primes) : Submodule ℤ_[p] (FieldProduct F p) :=
  ⨅ y : IntegralProduct F p,
    (padicIntegerLattice p).comap
      (((productTrace F p).comp
        (LinearMap.mulRight ℚ_[p] (integralProductInclusion F p y))).restrictScalars ℤ_[p])

def productTraceDualFactors (p : Nat.Primes) : Submodule ℤ_[p] (FieldProduct F p) :=
  ⨅ v : PlacesAbove F p,
    (localTraceDual F p v).comap ((LinearMap.proj (R := ℚ_[p]) v).restrictScalars ℤ_[p])

def globalTraceDual : FractionalIdeal (𝓞 F)⁰ F :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)

def globalCodifferentSpan (p : Nat.Primes) (v : PlacesAbove F p) :
    Submodule ℤ_[p] (v.val.adicCompletion F) :=
  Submodule.span ℤ_[p]
    (algebraMap F (v.val.adicCompletion F) '' (globalTraceDual F : Set F))

def globalCodifferentIntegralSpan (p : Nat.Primes) (v : PlacesAbove F p) :
    Submodule (v.val.adicCompletionIntegers F) (v.val.adicCompletion F) :=
  Submodule.span (v.val.adicCompletionIntegers F)
    (algebraMap F (v.val.adicCompletion F) '' (globalTraceDual F : Set F))

theorem trace_pi_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (b : ∀ i, Module.Basis (κ i) R (A i))
    (x : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (R := R) (Pi.basis b) x]
  rw [Matrix.trace]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.trace_eq_matrix_trace (R := R) (b i) (x i)]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.diag_apply]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [Pi.basis_repr]
  congr 2
  simp [Pi.basis_apply]

theorem fieldTensorEquiv_tmul (p : Nat.Primes) (a : ℚ_[p]) (x : F)
    (v : PlacesAbove F p) :
    fieldTensorEquiv F p (a ⊗ₜ[ℚ] x) v =
      fieldScalarMap F p v a * algebraMap F (v.val.adicCompletion F) x := by
  letI : Algebra ℚ ((Rat.HeightOneSpectrum.primesEquiv.symm p).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
  change finitePlaceTensorRingEquivAboveAdic (K := ℚ) (L := F) _
    ((Algebra.TensorProduct.congr (Padic.adicCompletionEquiv (𝓞 ℚ) p).toAlgEquiv
      (AlgEquiv.refl : F ≃ₐ[ℚ] F)) (a ⊗ₜ[ℚ] x)) v = _
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rw [finitePlaceTensorRingEquivAboveAdic_tmul]
  rfl

def fieldTensorAlgEquiv (p : Nat.Primes) :
    (ℚ_[p] ⊗[ℚ] F) ≃ₐ[ℚ_[p]] FieldProduct F p :=
  { fieldTensorEquiv F p with
    commutes' := fun a => by
      apply funext
      intro v
      rw [Algebra.TensorProduct.algebraMap_apply]
      change fieldTensorEquiv F p (a ⊗ₜ[ℚ] (1 : F)) v = fieldScalarMap F p v a
      rw [fieldTensorEquiv_tmul, map_one, mul_one] }

theorem traceBaseChange_eq_sum (p : Nat.Primes) (x : ℚ_[p] ⊗[ℚ] F) :
    Algebra.trace ℚ_[p] (ℚ_[p] ⊗[ℚ] F) x =
      productTrace F p (fieldTensorEquiv F p x) := by
  classical
  let e := fieldTensorAlgEquiv F p
  letI : FiniteDimensional ℚ_[p] (FieldProduct F p) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  letI (v : PlacesAbove F p) : FiniteDimensional ℚ_[p] (v.val.adicCompletion F) :=
    Module.Finite.of_surjective
      (LinearMap.proj (R := ℚ_[p]) (φ := fun w : PlacesAbove F p => w.val.adicCompletion F) v)
      (LinearMap.proj_surjective (R := ℚ_[p]) (φ := fun w : PlacesAbove F p => w.val.adicCompletion F) v)
  rw [← Algebra.trace_eq_of_algEquiv e]
  exact (trace_pi_apply (R := ℚ_[p]) (fun v : PlacesAbove F p => v.val.adicCompletion F)
    (fun v => Module.Free.chooseBasis ℚ_[p] (v.val.adicCompletion F)) (e x)).trans
      (by simp [productTrace, localTraceAt, e, fieldTensorAlgEquiv])

theorem trace_tensor_tmul (p : Nat.Primes) (a : ℚ_[p]) (x : F) :
    Algebra.trace ℚ_[p] (ℚ_[p] ⊗[ℚ] F) (a ⊗ₜ[ℚ] x) =
      a * algebraMap ℚ ℚ_[p] (Algebra.trace ℚ F x) := by
  have h := LinearMap.trace_baseChange (Algebra.lmul ℚ F x) ℚ_[p]
  rw [Algebra.baseChange_lmul] at h
  change Algebra.trace ℚ_[p] (ℚ_[p] ⊗[ℚ] F) (1 ⊗ₜ[ℚ] x) = _ at h
  rw [show a ⊗ₜ[ℚ] x = a • (1 ⊗ₜ[ℚ] x) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, h]
  rfl

theorem globalTraceDual_eq_span_traceDual :
    (globalTraceDual F).coeToSubmodule.restrictScalars ℤ =
      Submodule.span ℤ (Set.range (integralBasis F).traceDual) := by
  rw [globalTraceDual, FractionalIdeal.coe_dual_one]
  apply Submodule.traceDual_span_of_basis
  ext x
  simpa using (NumberField.mem_span_integralBasis (K := F) (x := x)).symm

theorem mem_localTraceDual (p : Nat.Primes) (v : PlacesAbove F p)
    (x : v.val.adicCompletion F) :
    x ∈ localTraceDual F p v ↔ ∀ y : v.val.adicCompletionIntegers F,
      localTraceAt F p v (x * y) ∈ padicIntegerLattice p := by
  simp [localTraceDual, LinearMap.mulRight_apply]

theorem mem_productTraceDual (p : Nat.Primes) (x : FieldProduct F p) :
    x ∈ productTraceDual F p ↔ ∀ y : IntegralProduct F p,
      (∑ v, localTraceAt F p v (x v * y v)) ∈ padicIntegerLattice p := by
  simp [productTraceDual, productTrace, LinearMap.mulRight_apply, integralProductInclusion]

theorem productTraceDual_eq_factors (p : Nat.Primes) :
    productTraceDual F p = productTraceDualFactors F p := by
  classical
  ext x
  rw [mem_productTraceDual]
  simp only [productTraceDualFactors, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, LinearMap.proj_apply]
  simp only [mem_localTraceDual]
  constructor
  · intro h v y
    have hv := h (Pi.single v y)
    have hs : (∑ w : PlacesAbove F p, localTraceAt F p w (x w * ((Pi.single v y : IntegralProduct F p) w))) =
        localTraceAt F p v (x v * y) := by
      rw [Finset.sum_eq_single v]
      · simp
      · intro w _ hw
        rw [Pi.single_eq_of_ne hw]
        simp
      · simp
    rw [hs] at hv
    exact hv
  · intro h y
    exact Submodule.sum_mem _ (fun v _ => h v (y v))

 abbrev TraceBasisIndex := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
 def productIntegralFieldBasis (p : Nat.Primes) : Module.Basis (TraceBasisIndex F) ℚ_[p] (FieldProduct F p) :=
  (Algebra.TensorProduct.basis ℚ_[p] (integralBasis F)).map (fieldTensorAlgEquiv F p).toLinearEquiv
 def productCodifferentFieldBasis (p : Nat.Primes) : Module.Basis (TraceBasisIndex F) ℚ_[p] (FieldProduct F p) :=
  (Algebra.TensorProduct.basis ℚ_[p] (integralBasis F).traceDual).map (fieldTensorAlgEquiv F p).toLinearEquiv

private theorem productIntegralFieldBasis_apply (p : Nat.Primes) (i : TraceBasisIndex F) (v : PlacesAbove F p) :
    productIntegralFieldBasis F p i v = algebraMap F (v.val.adicCompletion F) (integralBasis F i) := by
  simp [productIntegralFieldBasis, Algebra.TensorProduct.basis_apply, fieldTensorAlgEquiv, fieldTensorEquiv_tmul]

private theorem productCodifferentFieldBasis_apply (p : Nat.Primes) (i : TraceBasisIndex F) (v : PlacesAbove F p) :
    productCodifferentFieldBasis F p i v = algebraMap F (v.val.adicCompletion F) ((integralBasis F).traceDual i) := by
  simp [productCodifferentFieldBasis, Algebra.TensorProduct.basis_apply, fieldTensorAlgEquiv, fieldTensorEquiv_tmul]

private theorem productTrace_basis_pair (p : Nat.Primes) (i j : TraceBasisIndex F) :
    productTrace F p (productCodifferentFieldBasis F p i * productIntegralFieldBasis F p j) = if j = i then 1 else 0 := by
  classical
  simp only [productCodifferentFieldBasis, productIntegralFieldBasis, Module.Basis.map_apply,
    Algebra.TensorProduct.basis_apply, LinearEquiv.coe_coe]
  change productTrace F p ((fieldTensorEquiv F p) (1 ⊗ₜ[ℚ] ((integralBasis F).traceDual i)) *
    (fieldTensorEquiv F p) (1 ⊗ₜ[ℚ] (integralBasis F j))) = _
  rw [← map_mul]
  rw [← traceBaseChange_eq_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    trace_tensor_tmul, one_mul, Module.Basis.trace_traceDual_mul]
  split <;> simp_all

private theorem productCodifferentFieldBasis_repr (p : Nat.Primes) (x : FieldProduct F p) (i : TraceBasisIndex F) :
    (productCodifferentFieldBasis F p).repr x i = productTrace F p (x * productIntegralFieldBasis F p i) := by
  classical
  conv_rhs => rw [← (productCodifferentFieldBasis F p).sum_repr x]
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, productTrace_basis_pair, smul_eq_mul]
  simp

theorem integerScalarMap_completion_coe (p : Nat.Primes) (v : PlacesAbove F p) (a : ℤ_[p]) :
    (integerScalarMap F p v a : v.val.adicCompletion F) = fieldScalarMap F p v (a : ℚ_[p]) := by
  unfold integerScalarMap fieldScalarMap
  change finitePlaceAdicCompletionMap ℚ F _ v
    (((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p) a :
      (Rat.HeightOneSpectrum.primesEquiv.symm p).adicCompletion ℚ)) =
    finitePlaceAdicCompletionMap ℚ F _ v ((Padic.adicCompletionEquiv (𝓞 ℚ) p) (a : ℚ_[p]))
  congr 1
  exact PadicInt.coe_adicCompletionIntegersEquiv_apply (𝓞 ℚ) p a

theorem integralProductInclusion_smul (p : Nat.Primes) (a : ℤ_[p]) (y : IntegralProduct F p) :
    integralProductInclusion F p (a • y) = a • integralProductInclusion F p y := by
  apply funext
  intro v
  change ((a • y v : v.val.adicCompletionIntegers F) : v.val.adicCompletion F) = a • (y v : v.val.adicCompletion F)
  simp only [Algebra.smul_def, Subring.coe_mul]
  change (integerScalarMap F p v a : v.val.adicCompletion F) * _ = fieldScalarMap F p v (a : ℚ_[p]) * _
  rw [integerScalarMap_completion_coe]

private theorem integralProductInclusion_range (p : Nat.Primes) :
    Set.range (integralProductInclusion F p) =
      (Submodule.span ℤ_[p] (Set.range (productIntegralFieldBasis F p)) : Set (FieldProduct F p)) := by
  classical
  let b := Algebra.TensorProduct.basis ℤ_[p] (RingOfIntegers.basis F)
  have hb (i : TraceBasisIndex F) : integralProductInclusion F p (integralTensorEquiv F p (b i)) =
      productIntegralFieldBasis F p i := by
    ext v
    simp [b, Algebra.TensorProduct.basis_apply, integralTensorEquiv, integralTensorMap,
      integralProductInclusion, integralDiagonalAt, productIntegralFieldBasis_apply, integralBasis_apply,
      Pi.ringHom_apply]
    rfl
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (integralTensorEquiv F p).surjective y
    rw [← b.sum_repr z]
    have : integralProductInclusion F p (integralTensorEquiv F p
        (∑ i, (b.repr z i) • b i)) =
        ∑ i, (b.repr z i) • productIntegralFieldBasis F p i := by
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [integralProductInclusion_smul, hb]
    rw [this]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ⟨_, hb i⟩
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy hx' hy' =>
        obtain ⟨a, rfl⟩ := hx'
        obtain ⟨b, rfl⟩ := hy'
        exact ⟨a + b, map_add _ _ _⟩
    | smul a x hx hx' =>
        obtain ⟨y, rfl⟩ := hx'
        exact ⟨a • y, integralProductInclusion_smul F p a y⟩
private theorem productTraceDual_eq_span (p : Nat.Primes) :
    productTraceDual F p = Submodule.span ℤ_[p] (Set.range (productCodifferentFieldBasis F p)) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← (productCodifferentFieldBasis F p).sum_repr x]
    apply Submodule.sum_mem
    intro i _
    have hi : productTrace F p (x * productIntegralFieldBasis F p i) ∈ padicIntegerLattice p := by
      obtain ⟨y, hy⟩ := (integralProductInclusion_range F p).symm.subset
        (Submodule.subset_span (⟨i, rfl⟩ : productIntegralFieldBasis F p i ∈ Set.range (productIntegralFieldBasis F p)))
      rw [mem_productTraceDual] at hx
      have h := hx y
      have he : productTrace F p (x * integralProductInclusion F p y) =
          ∑ v, localTraceAt F p v (x v * y v) := by
        simp [productTrace, integralProductInclusion]
      rw [← he] at h
      simpa [hy] using h
    obtain ⟨a, ha⟩ := hi
    rw [productCodifferentFieldBasis_repr, ← ha]
    change (algebraMap ℤ_[p] ℚ_[p] a) • _ ∈ _
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change productCodifferentFieldBasis F p i ∈ productTraceDual F p
    apply (mem_productTraceDual F p _).mpr
    intro y
    have hy := (integralProductInclusion_range F p).subset ⟨y, rfl⟩
    have he : productTrace F p (productCodifferentFieldBasis F p i * integralProductInclusion F p y) =
        ∑ v, localTraceAt F p v (productCodifferentFieldBasis F p i v * y v) := by
      simp [productTrace, integralProductInclusion]
    rw [← he]
    generalize integralProductInclusion F p y = z at hy ⊢
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        rw [productTrace_basis_pair]
        split
        · exact ⟨1, (algebraMap ℤ_[p] ℚ_[p]).map_one⟩
        · exact Submodule.zero_mem _
    | zero => simp
    | add a b ha hb ha' hb' => simpa [mul_add] using add_mem ha' hb'
    | smul a b hb hb' =>
        simpa [mul_smul_comm] using (padicIntegerLattice p).smul_mem a hb'
theorem localTraceDual_eq_projection (p : Nat.Primes) (v : PlacesAbove F p) :
    localTraceDual F p v = (productTraceDual F p).map
      ((LinearMap.proj (R := ℚ_[p]) v).restrictScalars ℤ_[p]) := by
  classical
  ext x
  constructor
  · intro hx
    apply Submodule.mem_map.mpr
    refine ⟨Pi.single v x, ?_, by simp⟩
    rw [productTraceDual_eq_factors]
    simp only [productTraceDualFactors, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, LinearMap.proj_apply]
    intro w
    by_cases hw : w = v
    · subst w; simpa using hx
    · rw [Pi.single_eq_of_ne hw]
      exact Submodule.zero_mem _
  · rintro ⟨y, hy, hxy⟩
    rw [productTraceDual_eq_factors] at hy
    change y ∈ productTraceDualFactors F p at hy
    simp only [productTraceDualFactors, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, LinearMap.proj_apply] at hy
    simpa [← hxy] using hy v

private theorem localTraceDual_eq_basis_span (p : Nat.Primes) (v : PlacesAbove F p) :
    localTraceDual F p v = Submodule.span ℤ_[p]
      (Set.range fun i : TraceBasisIndex F => algebraMap F (v.val.adicCompletion F) ((integralBasis F).traceDual i)) := by
  rw [localTraceDual_eq_projection, productTraceDual_eq_span, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, LinearMap.restrictScalars_apply,
    LinearMap.proj_apply]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (productCodifferentFieldBasis_apply F p i v).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, productCodifferentFieldBasis_apply F p i v⟩

private theorem globalCodifferentSpan_eq_basis_span (p : Nat.Primes) (v : PlacesAbove F p) :
    globalCodifferentSpan F p v = Submodule.span ℤ_[p]
      (Set.range fun i : TraceBasisIndex F => algebraMap F (v.val.adicCompletion F) ((integralBasis F).traceDual i)) := by
  apply le_antisymm
  · rw [globalCodifferentSpan, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span ℤ (Set.range (integralBasis F).traceDual) := by
      rw [← globalTraceDual_eq_span_traceDual]
      exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y hx hy hx' hy' => simpa using add_mem hx' hy'
    | smul a x hx hx' =>
        have hs : (a : ℤ_[p]) • (algebraMap F (v.val.adicCompletion F) x) =
            (algebraMap F (v.val.adicCompletion F)) (a • x) := by
          simp only [Algebra.smul_def, map_mul]
          change fieldScalarMap F p v ((a : ℤ_[p]) : ℚ_[p]) * _ =
            (algebraMap F (v.val.adicCompletion F)) (a : F) * _
          simp
        simpa [hs] using Submodule.smul_mem (Submodule.span ℤ_[p] _) (a : ℤ_[p]) hx'
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨_, ?_, rfl⟩
    change (integralBasis F).traceDual i ∈ (globalTraceDual F).coeToSubmodule.restrictScalars ℤ
    rw [globalTraceDual_eq_span_traceDual]
    exact Submodule.subset_span ⟨i, rfl⟩
theorem localTraceDual_eq_globalCodifferentSpan (p : Nat.Primes) (v : PlacesAbove F p) :
    localTraceDual F p v = globalCodifferentSpan F p v := by
  rw [localTraceDual_eq_basis_span, globalCodifferentSpan_eq_basis_span]

theorem traceDual_baseChange (p : Nat.Primes) :
    productTraceDual F p = productTraceDualFactors F p ∧
    ∀ v : PlacesAbove F p, localTraceDual F p v = globalCodifferentSpan F p v := by
  exact ⟨productTraceDual_eq_factors F p, localTraceDual_eq_globalCodifferentSpan F p⟩

private theorem integerScalarMap_coe (p : Nat.Primes) (v : PlacesAbove F p)
    (a : ℤ_[p]) :
    (integerScalarMap F p v a : v.val.adicCompletion F) =
      fieldScalarMap F p v (a : ℚ_[p]) := by
  have h := congrFun (integralTensorMap_field_square F p (a ⊗ₜ[ℤ] (1 : 𝓞 F))) v
  change fieldTensorEquiv F p ((a : ℚ_[p]) ⊗ₜ[ℚ] (1 : F)) v =
    (integerScalarMap F p v a : v.val.adicCompletion F) * 1 at h
  simpa [fieldTensorEquiv_tmul] using h.symm

private theorem localTraceDual_integer_smul (p : Nat.Primes) (v : PlacesAbove F p)
    (a : v.val.adicCompletionIntegers F) (x : v.val.adicCompletion F)
    (hx : x ∈ localTraceDual F p v) :
    a • x ∈ localTraceDual F p v := by
  rw [mem_localTraceDual] at hx ⊢
  intro y
  simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using hx (a * y)

theorem traceDual_localIntegralSpan (p : Nat.Primes) (v : PlacesAbove F p) :
    (localTraceDual F p v : Set (v.val.adicCompletion F)) =
      (globalCodifferentIntegralSpan F p v : Set (v.val.adicCompletion F)) := by
  have hb := (traceDual_baseChange F p).2 v
  let D : Submodule (v.val.adicCompletionIntegers F) (v.val.adicCompletion F) :=
    { carrier := localTraceDual F p v
      zero_mem' := (localTraceDual F p v).zero_mem
      add_mem' := fun hx hy => (localTraceDual F p v).add_mem hx hy
      smul_mem' := fun a x hx => localTraceDual_integer_smul F p v a x hx }
  apply Set.Subset.antisymm
  · intro x hx
    rw [hb] at hx
    refine Submodule.span_induction (p := fun x _ => x ∈ globalCodifferentIntegralSpan F p v)
      (fun x hx => Submodule.subset_span hx) (Submodule.zero_mem _)
      (fun x y _ _ hx hy => Submodule.add_mem _ hx hy) ?_ hx
    intro a x _ hx
    have hsm : a • x = integerScalarMap F p v a • x := by
      simp only [Algebra.smul_def]
      rw [show algebraMap ℤ_[p] (v.val.adicCompletion F) a =
        fieldScalarMap F p v (a : ℚ_[p]) from rfl]
      rw [← integerScalarMap_coe F p v a]
      rfl
    rw [hsm]
    exact Submodule.smul_mem _ _ hx
  · intro x hx
    have hle : globalCodifferentIntegralSpan F p v ≤ D := by
      apply Submodule.span_le.mpr
      intro z hz
      change z ∈ localTraceDual F p v
      rw [hb]
      exact Submodule.subset_span hz
    exact hle hx

end DedekindZetaZeroFree.TraceBaseChange

end
