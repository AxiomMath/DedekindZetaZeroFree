module

public import DedekindZetaZeroFree.Theta.Periods.Wild.EnlargedFiniteWordKernels
public import DedekindZetaZeroFree.Adeles.Approximation.RestrictedProductTruncation

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open WildCurrentGlobalMap KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance rawFiniteDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def rawGlobal : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 →* Group R :=
  (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12)

def rawWord (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) :
    List (KPHilbert.Place F) → Group R
  | [] => 1
  | p :: l => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (localInjection F R.A.zeta12 R.A.primitive_zeta12 p (a p)) * rawWord a l

theorem rawWord_eq (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (l : List (KPHilbert.Place F)) :
    rawWord (R := R) a l = rawGlobal (R := R)
      (WildRestrictedTruncation.word _ (compact F R.A.zeta12 R.A.primitive_zeta12) a l) := by
  induction l with
  | nil => simp [rawWord, WildRestrictedTruncation.word]
  | cons p l ih =>
    simp only [rawWord, WildRestrictedTruncation.word, map_mul, ← ih]
    apply congrArg (fun y : Group R ↦ y * rawWord (R := R) a l)
    change rawGlobal (R := R) (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 p (a p)) = _
    apply congrArg (rawGlobal (R := R))
    apply RestrictedProduct.ext
    intro j
    by_cases hj : j = p
    · subst j
      simp [localToRestricted, RestrictedProduct.mulSingleMonoidHom, RestrictedProduct.mulSingle]
    · simp [localToRestricted, RestrictedProduct.mulSingleMonoidHom, RestrictedProduct.mulSingle, hj]

theorem exists_tame_word (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (t : RestrictedTensorSimple.Level D.bad)
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : ∀ p, a p ≠ 1 → ∃ q : KPFinitePlace F, p = Sum.inr q ∧
      Sum.inr q ∉ places W ∧ WildCurrentTameExterior.tameSlot (Sum.inr q))
    (l : List (KPHilbert.Place F)) (hl : ∀ p ∈ l, p ∈ t.val) :
    ∃ m : List (TameAction D W t), wordGroup D W t m = rawWord (R := R) a l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons p l ih =>
    obtain ⟨m, hm⟩ := ih (fun j hj ↦ hl j (List.mem_cons_of_mem p hj))
    by_cases hp : a p = 1
    · refine ⟨m, ?_⟩
      simpa only [rawWord, hp, map_one, one_mul] using hm
    · obtain ⟨q, hq, ho, ht⟩ := ha p hp
      subst p
      let b : TameAction D W t := ⟨q, hl _ (List.mem_cons_self), ho, ht, a (Sum.inr q)⟩
      refine ⟨b :: m, ?_⟩
      change _ * wordGroup D W t m = _ * rawWord (R := R) a l
      rw [hm]

theorem rawWord_kernel (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : ∀ p, a p ≠ 1 → ∃ q : KPFinitePlace F, p = Sum.inr q ∧
      Sum.inr q ∉ places W ∧ WildCurrentTameExterior.tameSlot (Sum.inr q))
    (l : List (KPHilbert.Place F)) (z : AmbientTensor F W (fiber D.toTensorActions W))
    (hz : WildCurrentJointPeriod.period D.toTensorActions W s hW x z = 0) :
    fourier R D.sources.dq (globalMap D.toTensorActions W s hW x z) (rawWord (R := R) a l) = 0 := by
  let t : RestrictedTensorSimple.Level D.bad :=
    ⟨s.val ∪ l.toFinset, s.property.trans (Finset.subset_union_left)⟩
  obtain ⟨m, hm⟩ := exists_tame_word D.toTensorActions W t a ha l (by
    intro p hp
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr hp))
  rw [← hm]
  exact enlarged_finite_word_right_kernel D W s t hW (Finset.subset_union_left) x hx m z hz
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
