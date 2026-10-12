module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceBaseChange.IntegralApproximation
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceDecomposition

@[expose] public section

noncomputable section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TraceBaseChange

variable (F : Type*) [Field F] [NumberField F]

abbrev PlacesAbove (p : Nat.Primes) :=
  FinitePlacesAbove ℚ F (Rat.HeightOneSpectrum.primesEquiv.symm p)

instance primeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

noncomputable instance placesAboveFintype (p : Nat.Primes) : Fintype (PlacesAbove F p) :=
  finitePlacesAboveRationalPrimeFintype F p

abbrev IntegralProduct (p : Nat.Primes) :=
  (v : PlacesAbove F p) → v.val.adicCompletionIntegers F

abbrev FieldProduct (p : Nat.Primes) :=
  (v : PlacesAbove F p) → v.val.adicCompletion F

def fieldScalarMap (p : Nat.Primes) (v : PlacesAbove F p) :
    ℚ_[p] →+* v.val.adicCompletion F :=
  letI : Algebra ℚ ((Rat.HeightOneSpectrum.primesEquiv.symm p).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
  (finitePlaceAdicCompletionMap ℚ F _ v).comp
    (Padic.adicCompletionEquiv (𝓞 ℚ) p).toRingEquiv.toRingHom

instance fieldAlgebra (p : Nat.Primes) (v : PlacesAbove F p) :
    Algebra ℚ_[p] (v.val.adicCompletion F) := (fieldScalarMap F p v).toAlgebra

def integerScalarMap (p : Nat.Primes) (v : PlacesAbove F p) :
    ℤ_[p] →+* v.val.adicCompletionIntegers F :=
  ((finitePlaceAdicCompletionMap ℚ F _ v).comp
    (((Rat.HeightOneSpectrum.primesEquiv.symm p).adicCompletionIntegers ℚ).subtype.comp
      (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).toRingEquiv.toRingHom)).codRestrict
        (v.val.adicCompletionIntegers F) (by
          intro z
          apply mem_adicCompletionIntegers_of_norm_le_one
          apply (finitePlaceAdicCompletionMap_norm_le_one_iff ℚ F _ v _).mpr
          exact norm_le_one_of_mem_adicCompletionIntegers _
            ((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p) z).property)

instance integerAlgebra (p : Nat.Primes) (v : PlacesAbove F p) :
    Algebra ℤ_[p] (v.val.adicCompletionIntegers F) := (integerScalarMap F p v).toAlgebra

instance integerTower (p : Nat.Primes) (v : PlacesAbove F p) :
    IsScalarTower ℤ ℤ_[p] (v.val.adicCompletionIntegers F) :=
  IsScalarTower.of_algebraMap_eq fun z => by simp

def integralDiagonalAt (p : Nat.Primes) : 𝓞 F →+* IntegralProduct F p :=
  Pi.ringHom fun v => algebraMap (𝓞 F) (v.val.adicCompletionIntegers F)

abbrev IntegralTensor (p : Nat.Primes) := ℤ_[p] ⊗[ℤ] 𝓞 F

instance integralTensorTopology (p : Nat.Primes) : TopologicalSpace (IntegralTensor F p) :=
  moduleTopology ℤ_[p] (IntegralTensor F p)

def integralTensorMap (p : Nat.Primes) :
    IntegralTensor F p →ₐ[ℤ_[p]] IntegralProduct F p :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (integralDiagonalAt F p).toIntAlgHom (fun _ _ => Commute.all _ _)

def fieldTensorEquiv (p : Nat.Primes) :
    (ℚ_[p] ⊗[ℚ] F) ≃+* FieldProduct F p :=
  letI : Algebra ℚ ((Rat.HeightOneSpectrum.primesEquiv.symm p).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
  (Algebra.TensorProduct.congr (Padic.adicCompletionEquiv (𝓞 ℚ) p).toAlgEquiv
    (AlgEquiv.refl : F ≃ₐ[ℚ] F)).toRingEquiv.trans
      (finitePlaceTensorRingEquivAboveAdic (K := ℚ) (L := F) _)

def integralToFieldTensor (p : Nat.Primes) :
    IntegralTensor F p →ₗ[ℤ] (ℚ_[p] ⊗[ℚ] F) :=
  (TensorProduct.mapOfCompatibleSMul ℚ ℤ ℤ ℚ_[p] F).comp
    (TensorProduct.map (algebraMap ℤ_[p] ℚ_[p]).toIntAlgHom.toLinearMap
      (algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap)

theorem scalarMap_continuous (p : Nat.Primes) (v : PlacesAbove F p) :
    Continuous (integerScalarMap F p v) := by
  unfold integerScalarMap
  apply Continuous.subtype_mk
  refine (finitePlaceAdicCompletionMap_continuous (K := ℚ) (L := F)
    (Rat.HeightOneSpectrum.primesEquiv.symm p) v).comp ?_
  exact continuous_subtype_val.comp (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).continuous

theorem scalarMap_continuousSMul (p : Nat.Primes) (v : PlacesAbove F p) :
    ContinuousSMul ℤ_[p] (v.val.adicCompletionIntegers F) := by
  refine ⟨?_⟩
  have hcont := scalarMap_continuous F p v
  rw [show (fun q : ℤ_[p] × v.val.adicCompletionIntegers F => q.1 • q.2) =
      fun q => integerScalarMap F p v q.1 * q.2 from by
    funext q; rw [Algebra.smul_def]; rfl]
  exact (hcont.comp continuous_fst).mul continuous_snd

instance integralProduct_continuousSMul (p : Nat.Primes) :
    ContinuousSMul ℤ_[p] (IntegralProduct F p) := by
  haveI : ∀ v : PlacesAbove F p, ContinuousSMul ℤ_[p] (v.val.adicCompletionIntegers F) :=
    fun v => scalarMap_continuousSMul F p v
  exact inferInstance

theorem integralTensorMap_field_square (p : Nat.Primes) (x : IntegralTensor F p) :
    fieldTensorEquiv F p (integralToFieldTensor F p x) =
      fun v => ((integralTensorMap F p x v : v.val.adicCompletionIntegers F) :
        v.val.adicCompletion F) := by
  letI : Algebra ℚ ((Rat.HeightOneSpectrum.primesEquiv.symm p).adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
  induction x using TensorProduct.induction_on with
  | zero => funext v; simp
  | add x y hx hy => funext v; simp_all
  | tmul a b =>
    funext v
    change finitePlaceTensorRingEquivAboveAdic (K := ℚ) (L := F) _
      (((Padic.adicCompletionEquiv (𝓞 ℚ) p) (a : ℚ_[p])) ⊗ₜ[ℚ] (b : F)) v = _
    rw [finitePlaceTensorRingEquivAboveAdic_tmul]
    simp only [integralTensorMap, Algebra.TensorProduct.lift_tmul,
      Algebra.ofId_apply, RingHom.toIntAlgHom_apply, integralDiagonalAt, Pi.ringHom_apply,
      Subring.coe_mul]
    change _ = (integerScalarMap F p v a : v.val.adicCompletion F) *
      algebraMap F (v.val.adicCompletion F) (b : F)
    congr 1
    exact (PadicInt.coe_adicCompletionIntegersEquiv_apply (𝓞 ℚ) p a).symm ▸ rfl

theorem integralTensorMap_topology_bijective (p : Nat.Primes) :
    Module.Free ℤ_[p] (IntegralTensor F p) ∧
    Module.Finite ℤ_[p] (IntegralTensor F p) ∧
    CompactSpace (IntegralTensor F p) ∧
    Continuous (integralTensorMap F p) ∧
    IsClosed (Set.range (integralTensorMap F p)) ∧
    DenseRange (integralTensorMap F p) ∧
    Function.Bijective (integralTensorMap F p) := by
  classical
  letI : IsModuleTopology ℤ_[p] (IntegralTensor F p) := ⟨rfl⟩
  letI := IsModuleTopology.toContinuousAdd ℤ_[p] (IntegralTensor F p)
  letI : CompactSpace (IntegralTensor F p) :=
    Module.Finite.compactSpace ℤ_[p] (IntegralTensor F p)
  letI : ∀ v : PlacesAbove F p, ContinuousSMul ℤ_[p] (v.val.adicCompletionIntegers F) :=
    fun v => ⟨by
      change Continuous (fun z : ℤ_[p] × v.val.adicCompletionIntegers F =>
        integerScalarMap F p v z.1 * z.2)
      have h : Continuous (integerScalarMap F p v) := by
        apply continuous_induced_rng.mpr
        exact (finitePlaceAdicCompletionMap_continuous ℚ F _ v).comp
          (continuous_subtype_val.comp (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).continuous)
      exact (h.comp continuous_fst).mul continuous_snd⟩
  have hc : Continuous (integralTensorMap F p) :=
    IsModuleTopology.continuous_of_linearMap (integralTensorMap F p).toLinearMap
  have hclosed : IsClosed (Set.range (integralTensorMap F p)) :=
    (isCompact_range hc).isClosed
  have hd : DenseRange (integralTensorMap F p) := by
    let r : DedekindZetaZeroFree.finiteIntegralAdeles F → IntegralProduct F p :=
      fun x v => x v.val
    have hr : Function.Surjective r := by
      intro y
      refine ⟨fun v => if h : finitePlaceBelow (K := ℚ) v =
        Rat.HeightOneSpectrum.primesEquiv.symm p then y ⟨v, h⟩ else 0, ?_⟩
      funext v
      simp [r, v.property]
    have hd := hr.denseRange.comp (integralProduct_dense F)
      (by fun_prop : Continuous r)
    apply Dense.mono _ hd
    rintro _ ⟨a, rfl⟩
    refine ⟨1 ⊗ₜ[ℤ] a, ?_⟩
    funext v
    simp [r, DedekindZetaZeroFree.integralDiagonal, integralTensorMap, integralDiagonalAt,
      Pi.ringHom_apply]
    rfl
  have hi : Function.Injective (integralToFieldTensor F p) := by
    letI : TensorProduct.CompatibleSMul ℤ ℚ ℚ_[p] F :=
      IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors ℤ) ℚ ℚ_[p] F
    apply Function.Injective.comp
      (TensorProduct.equivOfCompatibleSMul ℚ ℤ ℤ ℚ_[p] F).injective
    apply TensorProduct.map_injective_of_flat_flat
    · exact Subtype.coe_injective
    · exact RingOfIntegers.coe_injective
  refine ⟨inferInstance, inferInstance, inferInstance, hc, hclosed, hd, ?_, ?_⟩
  · intro x y hxy
    apply hi
    apply (fieldTensorEquiv F p).injective
    rw [integralTensorMap_field_square, integralTensorMap_field_square, hxy]
  · rw [← Set.range_eq_univ]
    rw [← hclosed.closure_eq]
    exact hd.closure_range

def integralTensorEquiv (p : Nat.Primes) :
    IntegralTensor F p ≃ₐ[ℤ_[p]] IntegralProduct F p :=
  AlgEquiv.ofBijective (integralTensorMap F p)
    (integralTensorMap_topology_bijective F p).2.2.2.2.2.2

end DedekindZetaZeroFree.TraceBaseChange

end
