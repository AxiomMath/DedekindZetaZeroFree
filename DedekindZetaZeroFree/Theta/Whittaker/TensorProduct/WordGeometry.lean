module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.CompactTensorWord
public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.FiniteBaseImage
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedWeylIdentification

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct KPLiteralScalarHCCompactOrbit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {N : TraceHaarTransport R} {C : JointDigitDescentSources R N}

theorem FrozenTensor.finite_of_mem {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ X.level.val) : q ∈ R.A.Sf := by
  have h := X.frozen ▸ hq
  rw [C.factorization.bad_exact] at h
  simpa only [Sum.inr_ne_inl,false_and,exists_false,false_or,Sum.inr.injEq,exists_eq_left'] using h

def FrozenTensor.placeEquiv {v : R.A.UnitQuotient} (X : FrozenTensor R C v) :
    (InfinitePlace F ⊕ R.A.Sf) ≃ X.level.val where
  toFun p := match p with
    | Sum.inl w => ⟨Sum.inl w,X.arch_mem w⟩
    | Sum.inr q => ⟨Sum.inr q.val,X.finite_mem q⟩
  invFun p := match h : p.val with
    | Sum.inl w => Sum.inl w
    | Sum.inr q => Sum.inr ⟨q,by
        exact X.finite_of_mem q (h ▸ p.property)⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨p,hp⟩; cases p <;> rfl

def restrictedEval (p : KPHilbert.Place F) : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 →*
    KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p where
  toFun u := u p
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restricted_list_single_eval {I : Type*}
    (e : I → KPHilbert.Place F)
    (a : ∀ i, KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (e i))
    (l : List I) (p : KPHilbert.Place F) :
    ((l.map (fun i => localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (e i) (a i))).prod) p =
    ((l.map (fun i => Pi.mulSingle (e i) (a i))).prod) p := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons,List.prod_cons,RestrictedProduct.mul_apply,Pi.mul_apply]
    rw [ih]
    rfl

def finiteTuple
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
  (Finset.univ.toList.map (fun q : R.A.Sf =>
    localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) (a q.val))).prod

def finiteBase
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 :=
  openCellFiniteFactor F R.A.zeta12 R.A.primitive_zeta12 (finiteTuple (R := R) a)

theorem finiteTuple_at (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (q : R.A.Sf) : finiteTuple (R := R) a (Sum.inr q.val) = a q.val := by
  have h := list_single_product (G := fun p => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (fun q : R.A.Sf => Sum.inr q.val) (fun x y h => Subtype.ext (Sum.inr.inj h))
    (fun q => a q.val) Finset.univ.toList (Finset.nodup_toList _) q
  simp only [Finset.mem_toList,Finset.mem_univ,ite_true] at h
  unfold finiteTuple
  rw [restricted_list_single_eval]
  exact h

theorem finiteTuple_off (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (p : KPHilbert.Place F) (hp : ∀ q : R.A.Sf, p ≠ Sum.inr q.val) :
    finiteTuple (R := R) a p = 1 := by
  have h := list_single_product_off (G := fun p => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (fun q : R.A.Sf => Sum.inr q.val) (fun q => a q.val) Finset.univ.toList p (fun q _ => hp q)
  unfold finiteTuple
  rw [restricted_list_single_eval]
  exact h

theorem finiteBase_val (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    (finiteBase (R := R) a).val = scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 (finiteTuple (R := R) a)) := by
  change scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12
      (openCellFiniteTuple F R.A.zeta12 R.A.primitive_zeta12 (finiteTuple (R := R) a))) = _
  congr 2
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inr q => rfl
  | inl w => exact (finiteTuple_off a (Sum.inl w) (fun _ => Sum.inl_ne_inr)).symm

theorem FrozenTensor.mixed_word_geometry {v : R.A.UnitQuotient} (X : FrozenTensor R C v)
    (k : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    (Finset.univ.toList.map (fun p : X.level.val => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val)))).prod =
    (finiteBase (R := R) a).val * archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
      (fun w => KPCplxCharacterHaar.complexSU2Embedding (k w)) := by
  let φ := (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  rw [finiteBase_val]
  change (Finset.univ.toList.map (fun p : X.level.val => φ
      (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val)))).prod =
    φ (finiteTuple (R := R) a) * φ (KPLiteralChamber.sectionTuple F R.A.zeta12 R.A.primitive_zeta12
      (fun w => KPCplxCharacterHaar.complexSU2Embedding (k w)))
  rw [← map_mul]
  have hm := map_list_prod φ (Finset.univ.toList.map (fun p : X.level.val =>
    localToRestricted F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val)))
  simp only [List.map_map,Function.comp_def] at hm
  rw [← hm]
  apply congrArg φ
  apply RestrictedProduct.ext
  intro p
  rw [restricted_list_single_eval]
  have hin (i : X.level.val) := list_single_product
    (G := fun p => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (fun p : X.level.val => p.val) Subtype.val_injective
    (fun p => mixedRaw (R := R) k a p.val) Finset.univ.toList (Finset.nodup_toList _) i
  have hout (hp : p ∉ X.level.val) := list_single_product_off
    (G := fun p => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (fun p : X.level.val => p.val) (fun p => mixedRaw (R := R) k a p.val) Finset.univ.toList p
    (fun i _ h => hp (h ▸ i.property))
  cases p with
  | inl w =>
    have h := hin ⟨Sum.inl w,X.arch_mem w⟩
    simp only [Finset.mem_toList,Finset.mem_univ,ite_true] at h
    change _ = finiteTuple (R := R) a (Sum.inl w) * _
    rw [finiteTuple_off a (Sum.inl w) (fun _ => Sum.inl_ne_inr),one_mul]
    exact h
  | inr q =>
    change _ = finiteTuple (R := R) a (Sum.inr q) * 1
    rw [mul_one]
    by_cases hq : q ∈ R.A.Sf
    · have h := hin ⟨Sum.inr q,X.finite_mem ⟨q,hq⟩⟩
      simp only [Finset.mem_toList,Finset.mem_univ,ite_true] at h
      rw [finiteTuple_at a ⟨q,hq⟩]
      exact h
    · rw [finiteTuple_off a (Sum.inr q) (fun p h => hq (Sum.inr.inj h ▸ p.property))]
      apply hout
      rw [X.frozen,C.factorization.bad_exact]
      simpa only [Sum.inr_ne_inl,false_and,exists_false,false_or,Sum.inr.injEq,exists_eq_left'] using hq

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
