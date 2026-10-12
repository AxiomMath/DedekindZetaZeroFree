module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.PGLCentralExtension

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] localTopology

def pglCompact (v : KPHilbert.Place F) : Subgroup (KPPGLLocalCover.CubicPGL2 F ζ hζ v) :=
  (compact F ζ hζ v).map (KPPGLLocalCover.coverQuotient F ζ hζ v)

def pglLocalTopology (v : KPHilbert.Place F) :
    TopologicalSpace (KPPGLLocalCover.CubicPGL2 F ζ hζ v) := inferInstance

attribute [local instance] pglLocalTopology

abbrev RestrictedPGLCover := RestrictedProduct
  (fun v : KPHilbert.Place F => KPPGLLocalCover.CubicPGL2 F ζ hζ v)
  (fun v => (pglCompact F ζ hζ v : Set _)) Filter.cofinite

def restrictedPGLQuotient : RestrictedCover F ζ hζ →* RestrictedPGLCover F ζ hζ :=
  RestrictedProduct.mapAlongMonoidHom _ _ id Filter.tendsto_id
    (fun v => KPPGLLocalCover.coverQuotient F ζ hζ v)
    (Filter.Eventually.of_forall (fun v => by
      intro g hg
      exact ⟨g, hg, rfl⟩))

def pglCentralTupleMap : CentralTuples F →* RestrictedPGLCover F ζ hζ :=
  (restrictedPGLQuotient F ζ hζ).comp (centralTupleMap F ζ hζ)

def pglM : Subgroup (RestrictedPGLCover F ζ hζ) :=
  (centralProduct F).ker.map (pglCentralTupleMap F ζ hζ)

theorem pglM_central : pglM F ζ hζ ≤ Subgroup.center (RestrictedPGLCover F ζ hζ) := by
  rintro x ⟨ε, hε, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply RestrictedProduct.ext
  intro v
  change y v * KPPGLLocalCover.centralInjection F ζ hζ v (ε v) =
    KPPGLLocalCover.centralInjection F ζ hζ v (ε v) * y v
  exact Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ v ⟨ε v, rfl⟩) (y v)

instance pglM_normal : (pglM F ζ hζ).Normal :=
  Subgroup.normal_of_le_center (pglM_central F ζ hζ)

abbrev AmalgamatedRestrictedPGLCover := RestrictedPGLCover F ζ hζ ⧸ pglM F ζ hζ

namespace ScalarAmalgamationHelpers

 theorem restrictedPGLQuotient_surjective :
    Function.Surjective (restrictedPGLQuotient F ζ hζ) := by
  intro x
  have hlift (v : KPHilbert.Place F) :
      ∃ g : KPLocalCover.CubicGL2Raw F ζ hζ v,
        KPPGLLocalCover.coverQuotient F ζ hζ v g = x v ∧
        (x v ∈ pglCompact F ζ hζ v → g ∈ compact F ζ hζ v) := by
    by_cases hx : x v ∈ pglCompact F ζ hζ v
    · obtain ⟨g, hg, he⟩ := hx
      exact ⟨g, he, fun _ => hg⟩
    · obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
        (KPPGLLocalCover.splitScalarSubgroup F ζ hζ v) (x v)
      exact ⟨g, hg, fun h => (hx h).elim⟩
  choose g hg hcompact using hlift
  refine ⟨⟨g, x.property.mono fun v hv => hcompact v hv⟩, ?_⟩
  ext v
  exact hg v

 theorem restrictedPGLQuotient_continuous :
    Continuous (restrictedPGLQuotient F ζ hζ) := by
  exact RestrictedProduct.mapAlong_continuous _ _ id Filter.tendsto_id
    (fun v => KPPGLLocalCover.coverQuotient F ζ hζ v)
    (Filter.Eventually.of_forall fun v g hg => show
      KPPGLLocalCover.coverQuotient F ζ hζ v g ∈ pglCompact F ζ hζ v from ⟨g, hg, rfl⟩)
    (fun _ => QuotientGroup.continuous_mk)

private theorem adele_ext {a b : Adeles F}
    (h : ∀ v, adeleEval F v a = adeleEval F v b) : a = b := by
  apply Prod.ext
  · funext w
    exact h (Sum.inl w)
  · apply RestrictedProduct.ext
    intro q
    exact h (Sum.inr q)

 theorem restrictedPGLQuotient_kernel :
    (restrictedPGLQuotient F ζ hζ).ker = (scalarTuple F ζ hζ).range := by
  apply le_antisymm
  · intro x hx
    have hlocal (v : KPHilbert.Place F) :
        ∃ z : (KPHilbert.Completion F v)ˣ,
          KPScalarSplitCentral.scalarHom F ζ hζ v z = x v := by
      change x v ∈ KPPGLLocalCover.splitScalarSubgroup F ζ hζ v
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg (fun y : RestrictedPGLCover F ζ hζ => y v) hx
    choose z hz using hlocal
    have hzval (v : KPHilbert.Place F) :
        adeleEval F v (matrixEntry F ζ hζ x 0 0) = (z v).val := by
      cases v <;> change (x _).g.val 0 0 = _
      all_goals rw [← hz]; rfl
    have hzinv (v : KPHilbert.Place F) :
        adeleEval F v (matrixEntry F ζ hζ x⁻¹ 0 0) = (z v).inv := by
      cases v <;> change ((x _)⁻¹).g.val 0 0 = _
      all_goals rw [← hz, ← map_inv]; rfl
    let u : Ideles F :=
      { val := matrixEntry F ζ hζ x 0 0
        inv := matrixEntry F ζ hζ x⁻¹ 0 0
        val_inv := by
          apply adele_ext F
          intro v
          rw [map_mul, hzval, hzinv, map_one]
          exact (z v).val_inv
        inv_val := by
          apply adele_ext F
          intro v
          rw [map_mul, hzval, hzinv, map_one]
          exact (z v).inv_val }
    refine ⟨u, ?_⟩
    apply RestrictedProduct.ext
    intro v
    change KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v) u) = x v
    have hu : Units.map (adeleEval F v) u = z v := by
      apply Units.ext
      exact hzval v
    rw [hu, hz]
  · rintro x ⟨z, rfl⟩
    change restrictedPGLQuotient F ζ hζ (scalarTuple F ζ hζ z) = 1
    ext v
    exact (QuotientGroup.eq_one_iff _).mpr ⟨Units.map (adeleEval F v) z, rfl⟩

 def principalHomeomorph {ι : Type*} (R : ι → Type*)
    (A : (i : ι) → Set (R i)) [∀ i, TopologicalSpace (R i)] (S : Set ι) :
    ((i : ι) → {x : R i // i ∈ S → x ∈ A i}) ≃ₜ
      RestrictedProduct R A (Filter.principal S) where
  toFun x := ⟨fun i => (x i).val, Filter.eventually_principal.mpr fun i hi => (x i).property hi⟩
  invFun x i := ⟨x i, fun hi => (Filter.eventually_principal.mp x.property) i hi⟩
  left_inv x := by funext i; rfl
  right_inv x := rfl
  continuous_toFun := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i =>
    (RestrictedProduct.continuous_eval i).subtype_mk _

 instance raw_local_group (v : KPHilbert.Place F) :
    IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  cases v with
  | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
  | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _
      (depth_admissible F ζ hζ q)).2.2

 def principalQuotient (S : Set (KPHilbert.Place F)) :
    RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (compact F ζ hζ v : Set _)) (Filter.principal S) →
    RestrictedProduct (fun v => KPPGLLocalCover.CubicPGL2 F ζ hζ v)
      (fun v => (pglCompact F ζ hζ v : Set _)) (Filter.principal S) :=
  RestrictedProduct.mapAlong _ _ id Filter.tendsto_id
    (fun v => KPPGLLocalCover.coverQuotient F ζ hζ v)
    (Filter.Eventually.of_forall fun v g hg => ⟨g, hg, rfl⟩)

private theorem principalQuotient_quotientMap (S : Set (KPHilbert.Place F)) :
    Topology.IsQuotientMap (principalQuotient F ζ hζ S) := by
  let Q := fun v => KPPGLLocalCover.coverQuotient F ζ hζ v
  let f := fun v => fun x : {g : KPLocalCover.CubicGL2Raw F ζ hζ v //
      v ∈ S → g ∈ compact F ζ hζ v} =>
    (⟨Q v x.val, fun hv => ⟨x.val, x.property hv, rfl⟩⟩ :
      {g : KPPGLLocalCover.CubicPGL2 F ζ hζ v // v ∈ S → g ∈ pglCompact F ζ hζ v})
  have ho (v : KPHilbert.Place F) : IsOpenMap (f v) := by
    apply IsOpenMap.subtype_map QuotientGroup.isOpenMap_coe
    · change IsOpen {g : KPLocalCover.CubicGL2Raw F ζ hζ v | v ∈ S → g ∈ compact F ζ hζ v}
      by_cases hv : v ∈ S
      · have he : {g : KPLocalCover.CubicGL2Raw F ζ hζ v | v ∈ S → g ∈ compact F ζ hζ v} =
            (compact F ζ hζ v : Set _) := by ext g; simp only [Set.mem_setOf_eq, hv, true_implies, SetLike.mem_coe]
        rw [he]
        exact compact_open F ζ hζ v
      · have he : {g : KPLocalCover.CubicGL2Raw F ζ hζ v | v ∈ S → g ∈ compact F ζ hζ v} =
            Set.univ := by ext g; simp only [Set.mem_setOf_eq, hv, false_implies, Set.mem_univ]
        rw [he]
        exact isOpen_univ
    · intro x hx hv
      exact ⟨x, hx hv, rfl⟩
  have hc (v : KPHilbert.Place F) : Continuous (f v) :=
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  have hs (v : KPHilbert.Place F) : Function.Surjective (f v) := by
    intro x
    by_cases hv : v ∈ S
    · obtain ⟨g, hg, he⟩ := x.property hv
      exact ⟨⟨g, fun _ => hg⟩, Subtype.ext he⟩
    · obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
        (KPPGLLocalCover.splitScalarSubgroup F ζ hζ v) x.val
      exact ⟨⟨g, fun h => (hv h).elim⟩, Subtype.ext hg⟩
  have hpi : Topology.IsQuotientMap (Pi.map f) :=
    (IsOpenMap.piMap ho (Filter.Eventually.of_forall hs)).isQuotientMap
      (continuous_pi fun v => (hc v).comp (continuous_apply v)) (by
        intro x
        choose y hy using fun v => hs v (x v)
        exact ⟨y, funext hy⟩)
  let e₁ := principalHomeomorph (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
    (fun v => (compact F ζ hζ v : Set _)) S
  let e₂ := principalHomeomorph (fun v => KPPGLLocalCover.CubicPGL2 F ζ hζ v)
    (fun v => (pglCompact F ζ hζ v : Set _)) S
  exact e₂.isQuotientMap.comp (hpi.comp e₁.symm.isQuotientMap)

 theorem restrictedPGLQuotient_continuous_iff {X : Type*} [TopologicalSpace X]
    (f : RestrictedPGLCover F ζ hζ → X) :
    Continuous f ↔ Continuous (f ∘ restrictedPGLQuotient F ζ hζ) := by
  refine ⟨fun h => h.comp (restrictedPGLQuotient_continuous F ζ hζ), fun h => ?_⟩
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  apply (principalQuotient_quotientMap F ζ hζ S).continuous_iff.mpr
  exact (RestrictedProduct.continuous_dom.mp h) S hS

 theorem pglM_eq_map : pglM F ζ hζ =
    (M F ζ hζ).map (restrictedPGLQuotient F ζ hζ) := by
  exact (Subgroup.map_map _ _ _).symm

 def amalgamatedPGLMap : CubicGL2Adelic F ζ hζ →*
    AmalgamatedRestrictedPGLCover F ζ hζ :=
  QuotientGroup.lift (M F ζ hζ)
    ((QuotientGroup.mk' (pglM F ζ hζ)).comp (restrictedPGLQuotient F ζ hζ)) (by
      intro x hx
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [pglM_eq_map]
      exact ⟨x, hx, rfl⟩)

 theorem amalgamatedPGLMap_kernel : (amalgamatedPGLMap F ζ hζ).ker =
    splitScalarSubgroup F ζ hζ := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (M F ζ hζ) y
    have hp : restrictedPGLQuotient F ζ hζ x ∈ pglM F ζ hζ :=
      (QuotientGroup.eq_one_iff _).mp hy
    rw [pglM_eq_map] at hp
    obtain ⟨m, hm, he⟩ := hp
    have hs : x * m⁻¹ ∈ (restrictedPGLQuotient F ζ hζ).ker := by
      change restrictedPGLQuotient F ζ hζ (x * m⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    rw [restrictedPGLQuotient_kernel] at hs
    obtain ⟨z, hz⟩ := hs
    refine ⟨z, ?_⟩
    change amalgamation F ζ hζ (scalarTuple F ζ hζ z) = amalgamation F ζ hζ x
    rw [hz, map_mul, map_inv]
    have hm1 : amalgamation F ζ hζ m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    rw [hm1, inv_one, mul_one]
  · rintro y ⟨z, rfl⟩
    change QuotientGroup.mk' (pglM F ζ hζ)
      (restrictedPGLQuotient F ζ hζ (scalarTuple F ζ hζ z)) = 1
    have hs : scalarTuple F ζ hζ z ∈ (restrictedPGLQuotient F ζ hζ).ker := by
      rw [restrictedPGLQuotient_kernel]
      exact ⟨z, rfl⟩
    rw [show restrictedPGLQuotient F ζ hζ (scalarTuple F ζ hζ z) = 1 from hs, map_one]

 def scalarAmalgamationEquiv : CubicPGL2Adelic F ζ hζ ≃*
    AmalgamatedRestrictedPGLCover F ζ hζ :=
  (QuotientGroup.quotientMulEquivOfEq (amalgamatedPGLMap_kernel F ζ hζ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (amalgamatedPGLMap F ζ hζ) (by
      intro y
      obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (pglM F ζ hζ) y
      obtain ⟨x, rfl⟩ := restrictedPGLQuotient_surjective F ζ hζ p
      exact ⟨amalgamation F ζ hζ x, rfl⟩))

 theorem scalarAmalgamationEquiv_mk (x : RestrictedCover F ζ hζ) :
    scalarAmalgamationEquiv F ζ hζ
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ x)) =
      QuotientGroup.mk' (pglM F ζ hζ) (restrictedPGLQuotient F ζ hζ x) := by
  rfl

 theorem scalarAmalgamationEquiv_continuous :
    Continuous (scalarAmalgamationEquiv F ζ hζ) := by
  apply (QuotientGroup.isQuotientMap_mk (splitScalarSubgroup F ζ hζ)).continuous_iff.mpr
  apply (QuotientGroup.isQuotientMap_mk (M F ζ hζ)).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp (restrictedPGLQuotient_continuous F ζ hζ)

 theorem scalarAmalgamationEquiv_symm_continuous :
    Continuous (scalarAmalgamationEquiv F ζ hζ).symm := by
  apply (QuotientGroup.isQuotientMap_mk (pglM F ζ hζ)).continuous_iff.mpr
  apply (restrictedPGLQuotient_continuous_iff F ζ hζ _).mpr
  have he : ((scalarAmalgamationEquiv F ζ hζ).symm ∘ QuotientGroup.mk) ∘
      restrictedPGLQuotient F ζ hζ =
      scalarQuotient F ζ hζ ∘ amalgamation F ζ hζ := by
    funext x
    exact (scalarAmalgamationEquiv F ζ hζ).symm_apply_apply
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ x))
  rw [he]
  exact QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk

end ScalarAmalgamationHelpers

theorem scalar_quotient_commutes_with_amalgamation :
    ∃ e : CubicPGL2Adelic F ζ hζ ≃* AmalgamatedRestrictedPGLCover F ζ hζ,
      Continuous e ∧ Continuous e.symm ∧
      ∀ x : RestrictedCover F ζ hζ,
        e (scalarQuotient F ζ hζ (amalgamation F ζ hζ x)) =
          QuotientGroup.mk' (pglM F ζ hζ) (restrictedPGLQuotient F ζ hζ x) := by
  exact ⟨ScalarAmalgamationHelpers.scalarAmalgamationEquiv F ζ hζ,
    ScalarAmalgamationHelpers.scalarAmalgamationEquiv_continuous F ζ hζ,
    ScalarAmalgamationHelpers.scalarAmalgamationEquiv_symm_continuous F ζ hζ,
    ScalarAmalgamationHelpers.scalarAmalgamationEquiv_mk F ζ hζ⟩

 def singleIdele (v : KPHilbert.Place F) :
    (KPHilbert.Completion F v)ˣ →* Ideles F :=
  match v with
  | Sum.inl w => NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
  | Sum.inr q => NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F q
private theorem eval_single_same (v : KPHilbert.Place F) (z : (KPHilbert.Completion F v)ˣ) :
    Units.map (adeleEval F v).toMonoidHom (singleIdele F v z) = z := by
  apply Units.ext
  cases v with
  | inl v => change Pi.mulSingle v z.val v = z.val; exact Pi.mulSingle_eq_same v _
  | inr v => change RestrictedProduct.mulSingle (fun q => q.adicCompletionIntegers F) v z.val v = z.val
             exact RestrictedProduct.mulSingle_eq_same _ _ _
private theorem eval_single_ne (v w : KPHilbert.Place F) (z : (KPHilbert.Completion F v)ˣ)
    (hw : w ≠ v) : Units.map (adeleEval F w).toMonoidHom (singleIdele F v z) = 1 := by
  apply Units.ext
  cases v with
  | inl v => cases w with
    | inl w => change Pi.mulSingle v z.val w = 1; exact Pi.mulSingle_eq_of_ne (fun h => hw (congrArg Sum.inl h)) _
    | inr w => rfl
  | inr v => cases w with
    | inl w => rfl
    | inr w => change RestrictedProduct.mulSingle (fun q => q.adicCompletionIntegers F) v z.val w = 1
               exact RestrictedProduct.mulSingle_eq_of_ne _ _ (fun h => hw (congrArg Sum.inr h))
private theorem scalarHom_single (v : KPHilbert.Place F) (z : (KPHilbert.Completion F v)ˣ) :
    scalarHom F ζ hζ (singleIdele F v z) =
      localInjection F ζ hζ v (KPScalarSplitCentral.scalarHom F ζ hζ v z) := by
  apply congrArg (amalgamation F ζ hζ)
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst w
    change KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v).toMonoidHom (singleIdele F v z)) = _
    rw [eval_single_same]
    exact (RestrictedProduct.mulSingle_eq_same _ _ _).symm
  · change KPScalarSplitCentral.scalarHom F ζ hζ w (Units.map (adeleEval F w).toMonoidHom (singleIdele F v z)) = _
    rw [eval_single_ne F v w z hw, map_one]
    exact (RestrictedProduct.mulSingle_eq_of_ne _ _ hw).symm

theorem local_pgl_injection (v : KPHilbert.Place F) :
    ∃ j : KPPGLLocalCover.CubicPGL2 F ζ hζ v →* CubicPGL2Adelic F ζ hζ,
      Function.Injective j ∧ Continuous j ∧
      ∀ g : KPLocalCover.CubicGL2Raw F ζ hζ v,
        j (KPPGLLocalCover.coverQuotient F ζ hζ v g) =
          scalarQuotient F ζ hζ (localInjection F ζ hζ v g) := by
  let f := (scalarQuotient F ζ hζ).comp (localInjection F ζ hζ v)
  have hf : KPPGLLocalCover.splitScalarSubgroup F ζ hζ v ≤ f.ker := by
    rintro g ⟨z, rfl⟩
    change scalarQuotient F ζ hζ (localInjection F ζ hζ v (KPScalarSplitCentral.scalarHom F ζ hζ v z)) = 1
    rw [← scalarHom_single]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
  let j := QuotientGroup.lift (KPPGLLocalCover.splitScalarSubgroup F ζ hζ v) f hf
  refine ⟨j, ?_, ?_, fun g => rfl⟩
  · apply (injective_iff_map_eq_one j).mpr
    intro x hx
    induction x using QuotientGroup.induction_on with | _ g =>
      obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).mp hx
      have hg : KPScalarSplitCentral.scalarMatrix F v (Units.map (adeleEval F v).toMonoidHom z) = g.g := by
        have hp := congrArg (fun a => matrixEval F v (projection F ζ hζ a)) hz
        rw [projection_scalarHom, projection_localInjection] at hp
        simpa [matrixEval, localToRestricted, RestrictedProduct.mulSingleMonoidHom,
          KPScalarSplitCentral.scalarMatrix, Matrix.GeneralLinearGroup.map_scalar] using hp
      have he : KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v).toMonoidHom z) *
          KPLocalCover.centralInjection F ζ hζ v g.epsilon = g := by
        cases g with | mk a e =>
          change KPScalarSplitCentral.scalarMatrix F v (Units.map (adeleEval F v).toMonoidHom z) = a at hg
          change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
          simpa [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
            KPLocalCover.sectionMap] using hg
      have hε : pglCentralInjection F ζ hζ g.epsilon = 1 := by
        have hmap := congrArg f he
        rw [map_mul] at hmap
        have hscalar : f (KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v).toMonoidHom z)) = 1 :=
          hf ⟨_, rfl⟩
        rw [hscalar, one_mul] at hmap
        change scalarQuotient F ζ hζ (localInjection F ζ hζ v (KPLocalCover.centralInjection F ζ hζ v g.epsilon)) = f g at hmap
        rw [localInjection_central] at hmap
        exact hmap.trans hx
      have hε1 : g.epsilon = 1 := (map_eq_one_iff _ (pglCentralInjection_injective F ζ hζ)).mp hε
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨Units.map (adeleEval F v).toMonoidHom z, ?_⟩
      simpa [hε1] using he
  · apply (QuotientGroup.isQuotientMap_mk (KPPGLLocalCover.splitScalarSubgroup F ζ hζ v)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp (localInjection_continuous F ζ hζ v)

end
end DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
