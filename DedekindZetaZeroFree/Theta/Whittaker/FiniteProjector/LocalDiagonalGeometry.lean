module

public import DedekindZetaZeroFree.Theta.Periods.FiniteTensorStabilizers

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open NumberField MomentSources KPAdelicCoverRestrictedProduct
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

private theorem eval_localIdele_units (v w : KPHilbert.Place F)
    (z : (KPHilbert.Completion F v)ˣ) :
    Units.map (adeleEval F w).toMonoidHom (KPRationalAdelicSplitting.localIdele F v z) =
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) v z w := by
  apply Units.ext
  exact congrArg Units.val (eval_localIdele F v w z)

attribute [local simp] eval_localIdele_units

theorem selected_localIdele_finite (y : R.A.G) (q : R.A.Sf) :
    Units.map (adeleEval F (Sum.inr q.val)).toMonoidHom (MomentSources.localIdele R y) = y.2 q := by
  unfold MomentSources.localIdele
  simp only [map_mul, map_prod]
  have he (p : KPHilbert.Place F) (z : (KPHilbert.Completion F p)ˣ) :
      Units.map (adeleEval F (Sum.inr q.val)).toMonoidHom (KPRationalAdelicSplitting.localIdele F p z) =
        Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) p z (Sum.inr q.val) :=
    eval_localIdele_units p (Sum.inr q.val) z
  simp only [he]
  have ha : (∏ w : InfinitePlace F, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
      (Sum.inl w) (y.1 w) (Sum.inr q.val)) = 1 := by
    apply Finset.prod_eq_one
    intro w _
    exact Pi.mulSingle_eq_of_ne (by simp) _
  rw [ha, one_mul, Finset.prod_eq_single q]
  · simp
  · intro p _ hpq
    exact Pi.mulSingle_eq_of_ne (Sum.inr_injective.ne (Subtype.val_injective.ne hpq.symm)) _
  · simp

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end

section

noncomputable section
open scoped Classical NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MomentSources KPAdelicCoverRestrictedProduct
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

private theorem eval_localIdele_units (v w : KPHilbert.Place F)
    (z : (KPHilbert.Completion F v)ˣ) :
    Units.map (adeleEval F w).toMonoidHom (KPRationalAdelicSplitting.localIdele F v z) =
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) v z w := by
  apply Units.ext
  exact congrArg Units.val (eval_localIdele F v w z)

attribute [local simp] eval_localIdele_units

theorem selected_localIdele_arch (y : R.A.G) (w : InfinitePlace F) :
    Units.map (adeleEval F (Sum.inl w)).toMonoidHom (MomentSources.localIdele R y) = y.1 w := by
  unfold MomentSources.localIdele
  simp only [map_mul, map_prod]
  have he (p : KPHilbert.Place F) (z : (KPHilbert.Completion F p)ˣ) :
      Units.map (adeleEval F (Sum.inl w)).toMonoidHom (KPRationalAdelicSplitting.localIdele F p z) =
        Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) p z (Sum.inl w) :=
    eval_localIdele_units p (Sum.inl w) z
  simp only [he]
  have hf : (∏ p : R.A.Sf, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
      (Sum.inr p.val) (y.2 p) (Sum.inl w)) = 1 := by
    apply Finset.prod_eq_one
    intro p _
    exact Pi.mulSingle_eq_of_ne (by simp) _
  rw [hf, mul_one, Finset.prod_eq_single w]
  · simp
  · intro b _ hbw
    exact Pi.mulSingle_eq_of_ne (Sum.inl_injective.ne hbw.symm) _
  · simp

theorem selected_localIdele_finite (y : R.A.G) (q : R.A.Sf) :
    Units.map (adeleEval F (Sum.inr q.val)).toMonoidHom (MomentSources.localIdele R y) = y.2 q := by
  unfold MomentSources.localIdele
  simp only [map_mul, map_prod]
  have he (p : KPHilbert.Place F) (z : (KPHilbert.Completion F p)ˣ) :
      Units.map (adeleEval F (Sum.inr q.val)).toMonoidHom (KPRationalAdelicSplitting.localIdele F p z) =
        Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) p z (Sum.inr q.val) :=
    eval_localIdele_units p (Sum.inr q.val) z
  simp only [he]
  have ha : (∏ w : InfinitePlace F, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
      (Sum.inl w) (y.1 w) (Sum.inr q.val)) = 1 := by
    apply Finset.prod_eq_one
    intro w _
    exact Pi.mulSingle_eq_of_ne (by simp) _
  rw [ha, one_mul, Finset.prod_eq_single q]
  · simp
  · intro p _ hpq
    exact Pi.mulSingle_eq_of_ne (Sum.inr_injective.ne (Subtype.val_injective.ne hpq.symm)) _
  · simp

theorem selected_localIdele_exterior (y : R.A.G) (q : KPFinitePlace F) (hq : q ∉ R.A.Sf) :
    Units.map (adeleEval F (Sum.inr q)).toMonoidHom (MomentSources.localIdele R y) = 1 := by
  unfold MomentSources.localIdele
  simp only [map_mul, map_prod]
  have he (p : KPHilbert.Place F) (z : (KPHilbert.Completion F p)ˣ) :
      Units.map (adeleEval F (Sum.inr q)).toMonoidHom (KPRationalAdelicSplitting.localIdele F p z) =
        Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) p z (Sum.inr q) :=
    eval_localIdele_units p (Sum.inr q) z
  simp only [he]
  have ha : (∏ w : InfinitePlace F, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
      (Sum.inl w) (y.1 w) (Sum.inr q)) = 1 := by
    apply Finset.prod_eq_one
    intro w _
    exact Pi.mulSingle_eq_of_ne (by simp) _
  have hf : (∏ p : R.A.Sf, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
      (Sum.inr p.val) (y.2 p) (Sum.inr q)) = 1 := by
    apply Finset.prod_eq_one
    intro p _
    apply Pi.mulSingle_eq_of_ne
    intro he
    exact hq ((Sum.inr_injective he) ▸ p.property)
  rw [ha, hf, one_mul]

private theorem list_product_single {I M : Type*} [DecidableEq I] [Monoid M]
    (l : List I) (hl : l.Nodup) (i : I) (hi : i ∈ l) (f : I → M)
    (hf : ∀ j ∈ l, j ≠ i → f j = 1) : (l.map f).prod = f i := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    have hn := List.nodup_cons.mp hl
    by_cases hji : j = i
    · subst j
      have he : (l.map f).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
        exact hf k (List.mem_cons_of_mem _ hk) (fun he => hn.1 (he ▸ hk))
      simp [he]
    · have him : i ∈ l := (List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simp only [List.map_cons, List.prod_cons,
        hf j List.mem_cons_self hji, one_mul]
      exact ih hn.2 him (fun k hk => hf k (List.mem_cons_of_mem _ hk))

def finiteDiagonalTuple (l : List R.A.Sf)
    (u : ∀ q : R.A.Sf, (q.val.adicCompletion F)ˣ) : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
  (l.map (fun q => localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)
    (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) (u q)))).prod

theorem finiteDiagonalWord_tuple (l : List R.A.Sf)
    (u : ∀ q : R.A.Sf, (q.val.adicCompletion F)ˣ) :
    finiteDiagonalWord R l u = scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (amalgamation F R.A.zeta12 R.A.primitive_zeta12 (finiteDiagonalTuple R l u)) := by
  unfold finiteDiagonalWord finiteDiagonalTuple
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  rfl

theorem finiteDiagonalTuple_arch (u : ∀ q : R.A.Sf, (q.val.adicCompletion F)ˣ)
    (w : InfinitePlace F) : finiteDiagonalTuple R Finset.univ.toList u (Sum.inl w) = 1 := by
  change (RestrictedProduct.evalMonoidHom _ (Sum.inl w)) (finiteDiagonalTuple R _ u) = 1
  unfold finiteDiagonalTuple
  rw [map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  simp [localToRestricted]

theorem finiteDiagonalTuple_finite (u : ∀ q : R.A.Sf, (q.val.adicCompletion F)ˣ)
    (q : R.A.Sf) : finiteDiagonalTuple R Finset.univ.toList u (Sum.inr q.val) =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) (u q) := by
  change (RestrictedProduct.evalMonoidHom _ (Sum.inr q.val)) (finiteDiagonalTuple R _ u) = _
  unfold finiteDiagonalTuple
  rw [map_list_prod, List.map_map]
  rw [list_product_single Finset.univ.toList (Finset.nodup_toList _) q (by simp)]
  · simp [localToRestricted]
  · intro p _ hpq
    have hval : q.val ≠ p.val := (Subtype.val_injective.ne hpq).symm
    simp [localToRestricted, Sum.inr_injective.ne hval]

theorem finiteDiagonalTuple_exterior (u : ∀ q : R.A.Sf, (q.val.adicCompletion F)ˣ)
    (q : KPFinitePlace F) (hq : q ∉ R.A.Sf) :
    finiteDiagonalTuple R Finset.univ.toList u (Sum.inr q) = 1 := by
  change (RestrictedProduct.evalMonoidHom _ (Sum.inr q)) (finiteDiagonalTuple R _ u) = 1
  unfold finiteDiagonalTuple
  rw [map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  have hval : q ≠ p.val := fun he => hq (he.symm ▸ p.property)
  simp [localToRestricted, Sum.inr_injective.ne hval]

theorem diagonal_arch_finite (y : R.A.G) :
    diagonal R y = diagonal R (y.1, 1) * finiteDiagonalWord R Finset.univ.toList y.2 := by
  rw [finiteDiagonalWord_tuple]
  unfold diagonal KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A
  rw [← map_mul, ← map_mul]
  apply congrArg (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
  apply congrArg (amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inl w =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      (Units.map (adeleEval F (Sum.inl w)).toMonoidHom (MomentSources.localIdele R y)) =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
        (Units.map (adeleEval F (Sum.inl w)).toMonoidHom (MomentSources.localIdele R (y.1, 1))) *
          finiteDiagonalTuple R _ y.2 (Sum.inl w)
    rw [selected_localIdele_arch, selected_localIdele_arch, finiteDiagonalTuple_arch, mul_one]
  | inr q =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
      (Units.map (adeleEval F (Sum.inr q)).toMonoidHom (MomentSources.localIdele R y)) =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
        (Units.map (adeleEval F (Sum.inr q)).toMonoidHom (MomentSources.localIdele R (y.1, 1))) *
          finiteDiagonalTuple R _ y.2 (Sum.inr q)
    by_cases hq : q ∈ R.A.Sf
    · let p : R.A.Sf := ⟨q, hq⟩
      rw [selected_localIdele_finite R y p, selected_localIdele_finite R (y.1, 1) p,
        finiteDiagonalTuple_finite R y.2 p]
      simp only [Prod.snd, Pi.one_apply, KPStandardLocalRootLifts.A_one, one_mul]
      rfl
    · rw [selected_localIdele_exterior R y q hq, selected_localIdele_exterior R (y.1, 1) q hq,
        finiteDiagonalTuple_exterior R y.2 q hq, KPStandardLocalRootLifts.A_one, one_mul]

end DedekindZetaZeroFree.RootDerivatives

end
end
