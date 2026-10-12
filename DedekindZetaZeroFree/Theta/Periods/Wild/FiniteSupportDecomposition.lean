module

public import DedekindZetaZeroFree.Theta.Periods.Wild.BorelWordFourierAction

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
local instance finiteRawSplitDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def insideRaw (W : Finset (KPFinitePlace F))
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) :=
  WildRestrictedTruncation.truncate _ (compact F R.A.zeta12 R.A.primitive_zeta12) a (places W)

def outsideRaw (W : Finset (KPFinitePlace F))
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) := a * (insideRaw (R := R) W a)⁻¹

def insideActions (W : Finset (KPFinitePlace F))
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : ∀ q : W, KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr q.val) (a (Sum.inr q.val)) ∈
      KPKirillovGenuineSectionCharts.P F R.A.zeta12 R.A.primitive_zeta12 q.val) :
    List (BorelAction R W) :=
  (Finset.univ.toList : List W).map (fun q ↦ ⟨q, a (Sum.inr q.val), ha q⟩)

theorem insideActions_group (W : Finset (KPFinitePlace F))
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : ∀ q : W, KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr q.val) (a (Sum.inr q.val)) ∈
      KPKirillovGenuineSectionCharts.P F R.A.zeta12 R.A.primitive_zeta12 q.val) :
    insideGroup (insideActions W a ha) = rawGlobal (R := R) (insideRaw W a) := by
  let e : W → KPHilbert.Place F := fun q ↦ Sum.inr q.val
  have hinj : Function.Injective e := by
    intro q r h
    exact Subtype.ext (Sum.inr_injective h)
  have hword (l : List W) :
      insideGroup (l.map (fun q ↦ (⟨q, a (Sum.inr q.val), ha q⟩ : BorelAction R W))) =
        rawWord (R := R) a (l.map e) := by
    induction l with
    | nil => rfl
    | cons q l ih => simpa only [List.map_cons, insideGroup, rawWord] using congrArg (fun z ↦
        scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) (a (Sum.inr q.val))) * z) ih
  have hn : ((Finset.univ.toList : List W).map e).Nodup :=
    (Finset.nodup_toList Finset.univ).map hinj
  have hs : ((Finset.univ.toList : List W).map e).toFinset = places W := by
    ext p
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    cases p with
    | inl w => simp [e, places]
    | inr q =>
      constructor
      · rintro ⟨r, hr⟩
        have he : r.val = q := Sum.inr_injective hr
        exact Finset.mem_image.mpr ⟨r.val, r.property, congrArg Sum.inr he⟩
      · intro hq
        have hq' : q ∈ W := by simpa [places] using hq
        exact ⟨⟨q, hq'⟩, rfl⟩
  rw [insideActions, hword, rawWord_eq]
  apply congrArg (rawGlobal (R := R))
  have ht := WildRestrictedTruncation.truncate_list _
    (compact F R.A.zeta12 R.A.primitive_zeta12) a _ hn
  rw [hs] at ht
  exact ht.symm

theorem outsideRaw_support (W : Finset (KPFinitePlace F))
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : ∀ w : InfinitePlace F, a (Sum.inl w) = 1)
    (ht : ∀ q : KPFinitePlace F, Sum.inr q ∉ places W →
      WildCurrentTameExterior.tameSlot (Sum.inr q)) :
    ∀ p, outsideRaw W a p ≠ 1 → ∃ q : KPFinitePlace F, p = Sum.inr q ∧
      Sum.inr q ∉ places W ∧ WildCurrentTameExterior.tameSlot (Sum.inr q) := by
  intro p hp
  have hout : p ∉ places W := by
    intro hm
    apply hp
    change a p * (if p ∈ places W then a p else 1)⁻¹ = 1
    rw [ite_eq_left hm, mul_inv_cancel]
  cases p with
  | inl w =>
    exfalso
    apply hp
    change a (Sum.inl w) * (if Sum.inl w ∈ places W then a (Sum.inl w) else 1)⁻¹ = 1
    rw [ite_eq_right hout, ha]
    simp
  | inr q => exact ⟨q, rfl, hout, ht q hout⟩

theorem raw_split (W : Finset (KPFinitePlace F))
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : ∀ q : W, KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr q.val) (a (Sum.inr q.val)) ∈
      KPKirillovGenuineSectionCharts.P F R.A.zeta12 R.A.primitive_zeta12 q.val) :
    rawGlobal (R := R) (outsideRaw W a) * insideGroup (insideActions W a ha) =
      rawGlobal (R := R) a := by
  rw [insideActions_group, ← map_mul]
  apply congrArg (rawGlobal (R := R))
  exact inv_mul_cancel_right a (insideRaw W a)
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
