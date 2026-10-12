module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ComplexHarishChandraCyclicity
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DifferentialWordCyclicSpan

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources NumberField KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q Q' : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T) (T' : Realization R Q')

theorem tensor_finite_slot_word_recovery (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (hx : x ⟨Sum.inr q,hq⟩ ≠ 0)
    (hm : _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T')
    (z : actualLocal R D.finiteData (Sum.inr q)) :
    _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inr q,hq⟩ z) ∈ wordRecovery R T' := by
  let m := (D.coreMap.comp (RestrictedTensorSimple.stageInclusion _ D.references D.bad s)).compMultilinearMap
    (PiTensorProduct.tprod ℂ)
  let j : s.val := ⟨Sum.inr q,hq⟩
  let L := m.toLinearMap x j
  have hz : z ∈ Submodule.span ℂ (Set.range (fun a => _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.actualFiniteAction R D q a (x j))) := by
    rw [_root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.actualFinite_orbit_span R D q (x j) hx]
    trivial
  change L z ∈ wordRecovery R T'
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a,rfl⟩ := hz
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective
      (KPPGLLocalCover.splitScalarSubgroup F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) a
    change KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) b = a at hb
    rw [← hb]
    change tensorFunction R D s (Function.update x j _) ∈ _
    have he : tensorFunction R D s (Function.update x j _) =
        KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
          (DedekindZetaZeroFree.FiniteWhittakerProjectors.finiteInjection R q b) (tensorFunction R D s x) :=
      funext (fun g => D.finite_intertwining q b s hq x g)
    rw [he]
    exact wordRecovery_finite R T' ⟨_,DedekindZetaZeroFree.FiniteWhittakerProjectors.finiteInjection_mem_finitePart R q b⟩ hm
  | zero => simpa using (Submodule.zero_mem (wordRecovery R T'))
  | add z w hz hw ihz ihw => simpa only [map_add] using Submodule.add_mem _ ihz ihw
  | smul c z hz ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem tensor_complex_slot_word_recovery
    (B : Fin 6 → Module.End ℂ complexCore)
    (hcyc : ∀ v : complexCore, v ≠ 0 →
      Submodule.span ℂ (Set.range (fun a : NativeComplexHCSource.algebra B => a.val v)) = ⊤)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (hcompact : ∀ k z,
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩ z) ∈ wordRecovery R T' →
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
        (complexCoreCompactLinearMap k z)) ∈ wordRecovery R T')
    (hderiv : ∀ i z,
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩ z) ∈ wordRecovery R T' →
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩ (B i z)) ∈ wordRecovery R T')
    (hx : x ⟨Sum.inl w,hw⟩ ≠ 0)
    (hm : _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T') (z : complexCore) :
    _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩ z) ∈ wordRecovery R T' := by
  let m := (D.coreMap.comp (RestrictedTensorSimple.stageInclusion _ D.references D.bad s)).compMultilinearMap
    (PiTensorProduct.tprod ℂ)
  let L : complexCore →ₗ[ℂ] Functions R := m.toLinearMap x ⟨Sum.inl w,hw⟩
  apply complexHC_recovery B hcyc L (wordRecovery R T') hcompact hderiv
    (x ⟨Sum.inl w,hw⟩) hx
  change _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩ (x ⟨Sum.inl w,hw⟩)) ∈ wordRecovery R T'
  simpa only [Function.update_eq_self] using hm

theorem tensor_slots_word_recovery
    (B : Fin 6 → Module.End ℂ complexCore)
    (hcyc : ∀ v : complexCore, v ≠ 0 →
      Submodule.span ℂ (Set.range (fun a : NativeComplexHCSource.algebra B => a.val v)) = ⊤)
    (s : RestrictedTensorSimple.Level D.bad)
    (hcompact : ∀ (x : ∀ p : s.val, actualLocal R D.finiteData p)
      (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) k,
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T' →
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
        (complexCoreCompactLinearMap k (x ⟨Sum.inl w,hw⟩))) ∈ wordRecovery R T')
    (hderiv : ∀ (x : ∀ p : s.val, actualLocal R D.finiteData p)
      (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) i,
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T' →
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
        (B i (x ⟨Sum.inl w,hw⟩))) ∈ wordRecovery R T')
    (x y : ∀ p : s.val, actualLocal R D.finiteData p)
    (C : Finset s.val) (hy : ∀ p ∈ C, y p ≠ 0)
    (hm : tensorFunction R D s y ∈ wordRecovery R T') :
    tensorFunction R D s (fun p => if p ∈ C then x p else y p) ∈ wordRecovery R T' := by
  induction C using Finset.induction_on with
  | empty => simpa using hm
  | @insert j C hj ih =>
    let u := fun p : s.val => if p ∈ C then x p else y p
    have hu := ih (fun p hp => hy p (Finset.mem_insert_of_mem hp))
    have hj0 : u j ≠ 0 := by
      simpa [u,hj] using hy j (Finset.mem_insert_self _ _)
    have he : (fun p : s.val => if p ∈ insert j C then x p else y p) =
        Function.update u j (x j) := by
      funext p
      by_cases hp : p = j
      · subst p; simp
      · simp [u,hp,Function.update_of_ne hp]
    rw [he]
    obtain ⟨j,hjmem⟩ := j
    cases j with
    | inr q =>
      exact tensor_finite_slot_word_recovery R D T' s u q hjmem hj0 hu _
    | inl w =>
      apply tensor_complex_slot_word_recovery R D T' B hcyc s u w hjmem
        (fun k z hz => ?_) (fun i z hz => ?_) hj0 hu
      · have h := hcompact (Function.update u ⟨Sum.inl w,hjmem⟩ z) w hjmem k hz
        simpa only [Function.update_self, Function.update_idem] using h
      · have h := hderiv (Function.update u ⟨Sum.inl w,hjmem⟩ z) w hjmem i hz
        simpa only [Function.update_self, Function.update_idem] using h

theorem tensor_stage_word_recovery
    (B : Fin 6 → Module.End ℂ complexCore)
    (hcyc : ∀ v : complexCore, v ≠ 0 →
      Submodule.span ℂ (Set.range (fun a : NativeComplexHCSource.algebra B => a.val v)) = ⊤)
    (s : RestrictedTensorSimple.Level D.bad)
    (hcompact : ∀ (x : ∀ p : s.val, actualLocal R D.finiteData p)
      (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) k,
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T' →
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
        (complexCoreCompactLinearMap k (x ⟨Sum.inl w,hw⟩))) ∈ wordRecovery R T')
    (hderiv : ∀ (x : ∀ p : s.val, actualLocal R D.finiteData p)
      (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) i,
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T' →
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
        (B i (x ⟨Sum.inl w,hw⟩))) ∈ wordRecovery R T')
    (y : ∀ p : s.val, actualLocal R D.finiteData p) (hy : ∀ p, y p ≠ 0)
    (hm : _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s y ∈ wordRecovery R T')
    (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T' := by
  simpa [_root_.DedekindZetaZeroFree.RootDerivatives.tensorFunction,
    _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction] using
    tensor_slots_word_recovery R D T' B hcyc s hcompact hderiv x y
    Finset.univ (fun p _ => hy p) hm

end DedekindZetaZeroFree.RootDerivatives

end
