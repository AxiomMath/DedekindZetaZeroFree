module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.WordGeometry
public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.ProductFaithfulness

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.SheetRescaling.EarlyProductFactorization
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct
open KPLiteralScalarHCCompactOrbit KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open WeylTensorTransport
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

 def archCoefficient (R : PrincipalMellin.ActualRecipe S η)
    (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (v : R.A.UnitQuotient) (w : InfinitePlace F) (g : ComplexGL2) : ℂ :=
  fourier R Q.dq (T.theta v)
    (archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 (Function.update 1 w g)) /
      fourier R Q.dq (T.theta v) 1

variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}

 def slotAction (D : SourceFactorization R Q T)
    (k : InfinitePlace F → ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (p : KPHilbert.Place F) : actualLocal R D.finiteData p → actualLocal R D.finiteData p :=
  match p with
  | Sum.inl w => KPGlobalResidualConstruction.complexCoreSU2Action (k w)
  | Sum.inr q => KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
      (D.finiteData q).haar (D.finiteData q).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (a q))

private theorem slot_intertwining (D : SourceFactorization R Q T)
    (k : InfinitePlace F → ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (s : RestrictedTensorSimple.Level D.bad) (p : s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) (g : Group R) :
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (Function.update x p (slotAction D k a p.val (x p))))) g =
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ x))
      (g * scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val))) := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl w => exact D.complex_intertwining w (k w) s hp x g
  | inr q => exact D.finite_intertwining q (a q) s hp x g

private theorem stage_word_exact (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (k : InfinitePlace F → ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (l : List s.val) (hl : l.Nodup) :
    fourier R Q.dq
      (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
        (PiTensorProduct.tprod ℂ x)))
      ((l.map (fun p => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val)))).prod) =
      ∏ p : s.val, D.ell p (if p ∈ l then slotAction D k a p.val (x p) else x p) := by
  let E := fun y => D.coreMap (RestrictedTensorSimple.stageInclusion _
    D.references D.bad s (PiTensorProduct.tprod ℂ y))
  let L := fun p : s.val => slotAction D k a p.val
  let A := fun p : s.val => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val))
  have ht (g : Group R) := independent_slot_word E L A
    (slot_intertwining D k a s) l.reverse (List.nodup_reverse.mpr hl) x g
  simp only [List.mem_reverse, List.reverse_reverse] at ht
  have hf : E (fun p => if p ∈ l then L p (x p) else x p) =
      fun g => E x (g * (l.map A).prod) := by
    funext g
    exact ht g
  rw [← D.product_exact s (fun p => if p ∈ l then L p (x p) else x p)]
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with q
  rw [show D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (fun p => if p ∈ l then L p (x p) else x p))) =
      E (fun p => if p ∈ l then L p (x p) else x p) from rfl, hf, mul_one]

private theorem stage_normalized_single (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hn : ∀ p : s.val, D.ell p (x p) ≠ 0)
    (k : InfinitePlace F → ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (i : s.val) :
    fourier R Q.dq
      (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
        (PiTensorProduct.tprod ℂ x)))
      (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (localInjection F R.A.zeta12 R.A.primitive_zeta12 i.val (mixedRaw (R := R) k a i.val))) /
      fourier R Q.dq
        (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
          (PiTensorProduct.tprod ℂ x))) 1 =
      D.ell i (slotAction D k a i.val (x i)) / D.ell i (x i) := by
  have he := stage_word_exact D s x k a [i] (by simp)
  simp only [List.map_singleton, List.prod_singleton, List.mem_singleton] at he
  rw [he, D.product_exact s x, ← Finset.prod_div_distrib]
  simpa only [eq_self, ite_true] using
    (Finset.prod_eq_single (s := Finset.univ)
      (f := fun p : s.val =>
        D.ell p (if p = i then slotAction D k a p.val (x p) else x p) / D.ell p (x p)) i
      (by
        intro p _ hp
        rw [if_neg hp]
        exact div_self (hn p)) (by simp))

 theorem arch_mem (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (w : InfinitePlace F) : Sum.inl w ∈ s.val := by
  rw [hs, D.bad_exact]
  exact Or.inl ⟨w, rfl⟩

 theorem finite_mem (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (q : R.A.Sf) : Sum.inr q.val ∈ s.val := by
  rw [hs, D.bad_exact]
  exact Or.inr ⟨q.val, rfl, q.property⟩

 theorem finite_of_mem (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val) : q ∈ R.A.Sf := by
  have h := hs ▸ hq
  rw [D.bad_exact] at h
  simpa only [Sum.inr_ne_inl, false_and, exists_false, false_or,
    Sum.inr.injEq, exists_eq_left'] using h

 def placeEquiv (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad) :
    (InfinitePlace F ⊕ R.A.Sf) ≃ s.val where
  toFun p := match p with
    | Sum.inl w => ⟨Sum.inl w, arch_mem D s hs w⟩
    | Sum.inr q => ⟨Sum.inr q.val, finite_mem D s hs q⟩
  invFun p := match h : p.val with
    | Sum.inl w => Sum.inl w
    | Sum.inr q => Sum.inr ⟨q, by
        exact finite_of_mem D s hs q (h ▸ p.property)⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨p, hp⟩; cases p <;> rfl

private theorem word_geometry (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad) (hs : s.val = D.bad)
    (k : InfinitePlace F → ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    (Finset.univ.toList.map (fun p : s.val => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (localInjection F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val)))).prod =
    (finiteBase (R := R) a).val * archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
      (fun w => complexSU2Embedding (k w)) := by
  let φ := (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  rw [finiteBase_val]
  change (Finset.univ.toList.map (fun p : s.val => φ
      (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val)))).prod =
    φ (finiteTuple (R := R) a) * φ (KPLiteralChamber.sectionTuple F R.A.zeta12 R.A.primitive_zeta12
      (fun w => complexSU2Embedding (k w)))
  rw [← map_mul]
  have hm := map_list_prod φ (Finset.univ.toList.map (fun p : s.val =>
    localToRestricted F R.A.zeta12 R.A.primitive_zeta12 p.val (mixedRaw (R := R) k a p.val)))
  simp only [List.map_map, Function.comp_def] at hm
  rw [← hm]
  apply congrArg φ
  apply RestrictedProduct.ext
  intro p
  rw [restricted_list_single_eval]
  have hin (i : s.val) := list_single_product
    (G := fun p => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (fun p : s.val => p.val) Subtype.val_injective
    (fun p => mixedRaw (R := R) k a p.val) Finset.univ.toList (Finset.nodup_toList _) i
  have hout (hp : p ∉ s.val) := list_single_product_off
    (G := fun p => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p)
    (fun p : s.val => p.val) (fun p => mixedRaw (R := R) k a p.val) Finset.univ.toList p
    (fun i _ h => hp (h ▸ i.property))
  cases p with
  | inl w =>
    have h := hin ⟨Sum.inl w, arch_mem D s hs w⟩
    simp only [Finset.mem_toList, Finset.mem_univ, ite_true] at h
    change _ = finiteTuple (R := R) a (Sum.inl w) * _
    rw [finiteTuple_off a (Sum.inl w) (fun _ => Sum.inl_ne_inr), one_mul]
    exact h
  | inr q =>
    change _ = finiteTuple (R := R) a (Sum.inr q) * 1
    rw [mul_one]
    by_cases hq : q ∈ R.A.Sf
    · have h := hin ⟨Sum.inr q, finite_mem D s hs ⟨q, hq⟩⟩
      simp only [Finset.mem_toList, Finset.mem_univ, ite_true] at h
      rw [finiteTuple_at a ⟨q, hq⟩]
      exact h
    · rw [finiteTuple_off a (Sum.inr q) (fun p h => hq (Sum.inr.inj h ▸ p.property))]
      apply hout
      rw [hs, D.bad_exact]
      simpa only [Sum.inr_ne_inl, false_and, exists_false, false_or,
        Sum.inr.injEq, exists_eq_left'] using hq

private theorem compact_mixed_product (D : SourceFactorization R Q T)
    (v : R.A.UnitQuotient) (hperiod : fourier R Q.dq (T.theta v) 1 ≠ 0)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hs : s.val = D.bad)
    (htheta : D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ x)) = T.theta v)
    (k : InfinitePlace F → ComplexSU2)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    fourier R Q.dq (T.theta v)
      ((finiteBase (R := R) a).val * archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
        (fun w => complexSU2Embedding (k w))) =
      fourier R Q.dq (T.theta v) 1 *
        (∏ q : R.A.Sf, fourier R Q.dq (T.theta v) (finiteLift q.val (a q.val)) /
          fourier R Q.dq (T.theta v) 1) *
        ∏ w : InfinitePlace F, archCoefficient R Q T v w (complexSU2Embedding (k w)) := by
  have hforward : fourier R Q.dq (T.theta v) 1 = ∏ p : s.val, D.ell p (x p) := by
    rw [← htheta]
    exact D.product_exact s x
  have hlocal (p : s.val) : D.ell p (x p) ≠ 0 := by
    have hn : (∏ p : s.val, D.ell p (x p)) ≠ 0 := by
      rw [← hforward]
      exact hperiod
    exact (Finset.prod_ne_zero_iff.mp hn) p (Finset.mem_univ p)
  have hp := stage_word_exact D s x k a Finset.univ.toList (Finset.nodup_toList _)
  simp only [Finset.mem_toList, Finset.mem_univ, ite_true] at hp
  rw [htheta, word_geometry D s hs k a] at hp
  rw [hp]
  have hratio : (∏ p : s.val, D.ell p (slotAction D k a p.val (x p))) =
      (∏ p : s.val, D.ell p (x p)) *
      ∏ p : s.val, D.ell p (slotAction D k a p.val (x p)) / D.ell p (x p) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    field_simp [hlocal p]
  rw [hratio, ← hforward]
  have he := Equiv.prod_comp (placeEquiv D s hs) (fun p : s.val =>
    D.ell p (slotAction D k a p.val (x p)) / D.ell p (x p))
  rw [← he, Fintype.prod_sum_type]
  have hc : (∏ w : InfinitePlace F,
      D.ell (Sum.inl w) (slotAction D k a (Sum.inl w) (x (placeEquiv D s hs (Sum.inl w)))) /
        D.ell (Sum.inl w) (x (placeEquiv D s hs (Sum.inl w)))) =
      ∏ w : InfinitePlace F, archCoefficient R Q T v w (complexSU2Embedding (k w)) := by
    apply Finset.prod_congr rfl
    intro w _
    unfold archCoefficient
    rw [KPLiteralScalarHCCompactAction.archMatrixInsertion_compact_single]
    have h := stage_normalized_single D s x hlocal k a ⟨Sum.inl w, arch_mem D s hs w⟩
    rw [htheta] at h
    simpa only [slotAction, placeEquiv, Equiv.coe_fn_mk, mixedRaw,
      KPGlobalResidualConstruction.complexCompactLift] using h.symm
  have hfin : (∏ q : R.A.Sf,
      D.ell (Sum.inr q.val) (slotAction D k a (Sum.inr q.val) (x (placeEquiv D s hs (Sum.inr q)))) /
        D.ell (Sum.inr q.val) (x (placeEquiv D s hs (Sum.inr q)))) =
      ∏ q : R.A.Sf, fourier R Q.dq (T.theta v) (finiteLift q.val (a q.val)) /
        fourier R Q.dq (T.theta v) 1 := by
    apply Finset.prod_congr rfl
    intro q _
    have h := stage_normalized_single D s x hlocal k a ⟨Sum.inr q.val, finite_mem D s hs q⟩
    rw [htheta] at h
    simpa only [slotAction, placeEquiv, Equiv.coe_fn_mk, mixedRaw, finiteLift] using h.symm
  simp only [placeEquiv, Equiv.coe_fn_mk] at hc hfin ⊢
  rw [hc, hfin]
  ring

private theorem archCoefficient_image
    (R : PrincipalMellin.ActualRecipe S η) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (v : R.A.UnitQuotient) (w : InfinitePlace F) :
    archCoefficient R Q T v w ∈ KPCplxJacquetFunctional.jacquetEvaluation.range := by
  obtain ⟨f, hf⟩ := selected_residue_jacquet_image R Q T v w
  refine ⟨(fourier R Q.dq (T.theta v) 1)⁻¹ • f, ?_⟩
  funext g
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, archCoefficient, div_eq_mul_inv]
  change _ * KPCplxJacquetFunctional.jacquetEvaluation f g =
    fourier R Q.dq (T.theta v)
      (archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 (Function.update (fun _ => 1) w g)) * _
  rw [hf]
  exact mul_comm _ _

theorem selected_fullMatrix_product
    (R : PrincipalMellin.ActualRecipe S η) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (D : SourceFactorization R Q T)
    (v : R.A.UnitQuotient) (hperiod : fourier R Q.dq (T.theta v) 1 ≠ 0)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (g : InfinitePlace F → ComplexGL2) :
    fourier R Q.dq (T.theta v)
      ((finiteBase (R := R) a).val * archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 g) =
      fourier R Q.dq (T.theta v) 1 *
        (∏ q : R.A.Sf, fourier R Q.dq (T.theta v) (finiteLift q.val (a q.val)) /
          fourier R Q.dq (T.theta v) 1) *
        ∏ w : InfinitePlace F, fourier R Q.dq (T.theta v)
          (archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 (Function.update 1 w (g w))) /
          fourier R Q.dq (T.theta v) 1 := by
  obtain ⟨s, x, hs, hselected⟩ := D.selected_frozen_stage v
  have htheta : D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ x)) = T.theta v := by
    rw [← hselected]
    exact D.selected_eq v
  let P := fun g : InfinitePlace F → ComplexGL2 => fourier R Q.dq (T.theta v)
    ((finiteBase (R := R) a).val * archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 g)
  let b := fourier R Q.dq (T.theta v) 1 *
    ∏ q : R.A.Sf, fourier R Q.dq (T.theta v) (finiteLift q.val (a q.val)) /
      fourier R Q.dq (T.theta v) 1
  let H := fun g : InfinitePlace F → ComplexGL2 => b * ∏ w, archCoefficient R Q T v w (g w)
  have he : P = H := by
    apply product_eq_of_compact_slices
    · intro w g₀
      obtain ⟨f, hf⟩ := finiteBase_residue_jacquet_image R Q T v w (finiteBase (R := R) a) g₀
      exact ⟨f, funext (fun g => (hf g).symm)⟩
    · intro w g₀
      obtain ⟨f, hf⟩ := archCoefficient_image R Q T v w
      let c := b * ∏ u ∈ Finset.univ.erase w, archCoefficient R Q T v u (g₀ u)
      refine ⟨c • f, ?_⟩
      funext g
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      rw [hf]
      dsimp only [H]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      simp only [Function.update_self]
      have hr : (∏ u ∈ Finset.univ.erase w, archCoefficient R Q T v u (Function.update g₀ w g u)) =
          ∏ u ∈ Finset.univ.erase w, archCoefficient R Q T v u (g₀ u) := by
        apply Finset.prod_congr rfl
        intro u hu
        rw [Function.update_of_ne (Finset.mem_erase.mp hu).1]
      rw [hr]
      dsimp only [c]
      ring
    · intro k
      exact compact_mixed_product D v hperiod s x hs htheta k a
  exact congrFun he g

end DedekindZetaZeroFree.SheetRescaling.EarlyProductFactorization
end
