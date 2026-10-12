module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.CentralExtension

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain Topology

namespace DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] localTopology

abbrev Ideles := (Adeles F)ˣ

def scalarCoordinates (z : Ideles F) (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v) z)

theorem scalarTuple_restricted (z : Ideles F) :
    ∀ᶠ v in Filter.cofinite,
      scalarCoordinates F ζ hζ z v ∈ (compact F ζ hζ v : Set _) := by
 have he : ∀ᶠ q in Filter.cofinite,
     scalarCoordinates F ζ hζ z (Sum.inr q) ∈ (finiteCompact F ζ hζ q : Set _) := by
   filter_upwards [z.val.2.2, z.inv.2.2, (bad_finite F).eventually_cofinite_notMem] with q hz hi hb
   letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
   have hm (a : q.adicCompletion F) (ha : a ∈ q.adicCompletionIntegers F) : a ∈ KPTameCompact.O F q := by
     rw [Valuation.mem_integer_iff]
     rw [← map_one (ValuativeRel.valuation (KPLocalCube.LocalField F q)), ← Valuation.Compatible.vle_iff_le]
     change Valued.v a ≤ Valued.v (1 : q.adicCompletion F)
     simpa only [map_one, HeightOneSpectrum.mem_adicCompletionIntegers] using ha
   let u : (KPTameCompact.O F q)ˣ :=
     ⟨⟨z.val.2 q, hm _ hz⟩, ⟨z.inv.2 q, hm _ hi⟩,
       by apply Subtype.ext; exact congrArg (fun a : Adeles F => a.2 q) z.val_inv,
       by apply Subtype.ext; exact congrArg (fun a : Adeles F => a.2 q) z.inv_val⟩
   have hu : KPTameCompact.unitInclusion F q u = Units.map (adeleEval F (Sum.inr q)) z := Units.ext rfl
   have hb' : ¬ Bad F q := hb
   simp only [finiteCompact, dif_neg hb', SetLike.mem_coe]
   refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) u, ?_⟩
   change KPGoodCompactSplitting.kStar F ζ hζ q _ _ = _
   rw [show scalarCoordinates F ζ hζ z (Sum.inr q) =
      KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) from congrArg _ hu.symm]
   exact (KPScalarSplitCentral.good_compact_unit_scalar F ζ hζ q (fun h => hb' (Or.inr h)) u).symm
 rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
 constructor
 · exact Set.toFinite _
 · exact Filter.eventually_cofinite.mp he

def scalarTupleValue (z : Ideles F) : RestrictedCover F ζ hζ :=
  ⟨scalarCoordinates F ζ hζ z, scalarTuple_restricted F ζ hζ z⟩

theorem scalarTupleValue_one : scalarTupleValue F ζ hζ 1 = 1 := by
  apply RestrictedProduct.ext
  intro v
  change KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v).toMonoidHom 1) = 1
  simp

theorem scalarTupleValue_mul (z z' : Ideles F) :
    scalarTupleValue F ζ hζ (z * z') = scalarTupleValue F ζ hζ z * scalarTupleValue F ζ hζ z' := by
  apply RestrictedProduct.ext
  intro v
  change KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v) (z * z')) =
    KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v) z) *
      KPScalarSplitCentral.scalarHom F ζ hζ v (Units.map (adeleEval F v) z')
  simp

def scalarTuple : Ideles F →* RestrictedCover F ζ hζ where
  toFun := scalarTupleValue F ζ hζ
  map_one' := scalarTupleValue_one F ζ hζ
  map_mul' := scalarTupleValue_mul F ζ hζ

def scalarHom : Ideles F →* CubicGL2Adelic F ζ hζ :=
  (amalgamation F ζ hζ).comp (scalarTuple F ζ hζ)

theorem projection_scalarHom (z : Ideles F) :
    projection F ζ hζ (scalarHom F ζ hζ z) = Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · funext w
    change (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (adeleEval F (Sum.inl w)).toMonoidHom z)) i j = _
    by_cases h : i = j <;> simp [Matrix.scalar, Matrix.diagonal, adeleEval, h] <;> rfl
  · apply RestrictedProduct.ext
    intro q
    change (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (adeleEval F (Sum.inr q)).toMonoidHom z)) i j = _
    by_cases h : i = j <;> simp [Matrix.scalar, Matrix.diagonal, adeleEval, h] <;> rfl

private theorem test_scalar_embedding (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] :
    IsClosedEmbedding (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := R)) := by
  let f : R →+* Matrix (Fin 2) (Fin 2) R := Matrix.scalar (Fin 2)
  have hc : Continuous f := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases h : i = j <;> simp [f, Matrix.scalar, Matrix.diagonal, h]
    · exact continuous_id
    · exact continuous_const
  have hi : IsEmbedding f :=
    .of_leftInverse (f := fun a : Matrix (Fin 2) (Fin 2) R => a 0 0)
      (g := f) (by intro x; simp [f, Matrix.scalar])
      ((continuous_apply 0).comp (continuous_apply 0)) hc
  have hr : Set.range f = {a | a = f (a 0 0)} := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩; simp [f, Matrix.scalar]
    · intro h; exact ⟨a 0 0, h.symm⟩
  have hf : IsClosedEmbedding f := ⟨hi, hr ▸ isClosed_eq continuous_id (hc.comp ((continuous_apply 0).comp (continuous_apply 0)))⟩
  exact hf.units_map

private theorem eval_cont (v : KPHilbert.Place F) : Continuous (adeleEval F v) := by
  cases v with
  | inl w => exact (continuous_apply w).comp continuous_fst
  | inr q => exact (RestrictedProduct.continuous_eval q).comp continuous_snd

private theorem local_scalar_cont (v : KPHilbert.Place F) :
    Continuous (KPScalarSplitCentral.scalarHom F ζ hζ v) := by
  cases v with
  | inl w => exact (KPScalarSplitCentral.complex_continuous_closed F ζ hζ w).1
  | inr q => exact (KPScalarSplitCentral.finite_continuous_closed F ζ hζ q _ (depth_admissible F ζ hζ q)).1

private theorem coordinate_cont (v : KPHilbert.Place F) :
    Continuous (fun z : Ideles F => scalarCoordinates F ζ hζ z v) :=
  (local_scalar_cont F ζ hζ v).comp ((eval_cont F v).units_map _)

private theorem integral_scalar_mem (z : Ideles F) (q : HeightOneSpectrum (𝓞 F))
    (hz : z.val.2 q ∈ q.adicCompletionIntegers F)
    (hi : z.inv.2 q ∈ q.adicCompletionIntegers F) (hb : ¬ Bad F q) :
    scalarCoordinates F ζ hζ z (Sum.inr q) ∈ compact F ζ hζ (Sum.inr q) := by
  letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
  have hm (a : q.adicCompletion F) (ha : a ∈ q.adicCompletionIntegers F) : a ∈ KPTameCompact.O F q := by
    rw [Valuation.mem_integer_iff]
    rw [← map_one (ValuativeRel.valuation (KPLocalCube.LocalField F q)), ← Valuation.Compatible.vle_iff_le]
    change Valued.v a ≤ Valued.v (1 : q.adicCompletion F)
    simpa only [map_one, HeightOneSpectrum.mem_adicCompletionIntegers] using ha
  let u : (KPTameCompact.O F q)ˣ :=
    ⟨⟨z.val.2 q, hm _ hz⟩, ⟨z.inv.2 q, hm _ hi⟩,
      by apply Subtype.ext; exact congrArg (fun a : Adeles F => a.2 q) z.val_inv,
      by apply Subtype.ext; exact congrArg (fun a : Adeles F => a.2 q) z.inv_val⟩
  have hu : KPTameCompact.unitInclusion F q u = Units.map (adeleEval F (Sum.inr q)) z := Units.ext rfl
  simp only [compact, finiteCompact, dif_neg hb, SetLike.mem_coe]
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) u, ?_⟩
  change KPGoodCompactSplitting.kStar F ζ hζ q _ _ = _
  rw [show scalarCoordinates F ζ hζ z (Sum.inr q) =
    KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) from congrArg _ hu.symm]
  exact (KPScalarSplitCentral.good_compact_unit_scalar F ζ hζ q (fun h => hb (Or.inr h)) u).symm

private theorem tuple_cont : Continuous (scalarTuple F ζ hζ) := by
  letI : ∀ v : KPHilbert.Place F, IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
    intro v
    cases v with
    | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
    | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _ (depth_admissible F ζ hζ q)).2.2
  letI : Fact (∀ v, IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) := ⟨compact_open F ζ hζ⟩
  apply continuous_of_continuousAt_one (scalarTuple F ζ hζ)
  let U : Set (Ideles F) := {z | (∀ q, ¬Bad F q → z.val.2 q ∈ q.adicCompletionIntegers F) ∧
    (∀ q, ¬Bad F q → z.inv.2 q ∈ q.adicCompletionIntegers F)}
  have hO : ∀ q : HeightOneSpectrum (𝓞 F), IsOpen (q.adicCompletionIntegers F : Set (q.adicCompletion F)) := by
    intro q
    exact Valued.isOpen_valuationSubring _
  have hv : Continuous (fun z : Ideles F => z.val.2) :=
    continuous_snd.comp (Units.continuous_val (M := Adeles F))
  have hi : Continuous (fun z : Ideles F => z.inv.2) :=
    continuous_snd.comp (Units.continuous_coe_inv (M := Adeles F))
  have hU : IsOpen U :=
    ((RestrictedProduct.isOpen_forall_imp_mem hO).preimage hv).inter
      ((RestrictedProduct.isOpen_forall_imp_mem hO).preimage hi)
  have h1 : (1 : Ideles F) ∈ U := by
    constructor <;> intro q hq <;> exact one_mem _
  let S : Set (KPHilbert.Place F) := {v | match v with | .inl _ => True | .inr q => ¬Bad F q}
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ v in Filter.cofinite, v ∈ S
    rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    constructor
    · exact Set.toFinite _
    · simpa [S] using bad_finite F
  let f : U → RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (compact F ζ hζ v : Set _)) (Filter.principal S) :=
    fun z => ⟨scalarCoordinates F ζ hζ z, by
      intro v hv
      cases v with
      | inl w => exact Subgroup.mem_top _
      | inr q => exact integral_scalar_mem F ζ hζ z q (z.property.1 q hv) (z.property.2 q hv) hv⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi (fun v => (coordinate_cont F ζ hζ v).comp continuous_subtype_val))
  have hr : Continuous (U.domRestrict (scalarTuple F ζ hζ)) :=
    (RestrictedProduct.continuous_inclusion hS).comp hf
  exact (continuousOn_iff_continuous_restrict.mpr hr).continuousAt (hU.mem_nhds h1)

theorem scalarHom_continuous_closed : Continuous (scalarHom F ζ hζ) ∧
    IsClosed (Set.range (scalarHom F ζ hζ)) := by
  obtain ⟨ht, hl, hg, hp⟩ := adelic_topological_cover F ζ hζ
  letI := ht
  letI := hl
  letI := hg
  have hc : Continuous (scalarHom F ζ hζ) :=
    QuotientGroup.continuous_mk.comp (tuple_cont F ζ hζ)
  refine ⟨hc, ?_⟩
  letI : T2Space (Adeles F) := by
    change T2Space ((∀ w : InfinitePlace F, w.Completion) ×
      RestrictedProduct (fun q : HeightOneSpectrum (𝓞 F) => q.adicCompletion F)
        (fun q => (q.adicCompletionIntegers F : Set _)) Filter.cofinite)
    infer_instance
  have he : Topology.IsClosedEmbedding
      ((projection F ζ hζ) ∘ (scalarHom F ζ hζ)) := by
    have hh : (projection F ζ hζ) ∘ (scalarHom F ζ hζ) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) := by
      funext z
      exact projection_scalarHom F ζ hζ z
    rw [hh]
    exact test_scalar_embedding (Adeles F)
  exact (isProperMap_of_comp_of_t2 hc hp.continuous he.isProperMap).isClosed_range

theorem scalarHom_central :
    (scalarHom F ζ hζ).range ≤ Subgroup.center (CubicGL2Adelic F ζ hζ) := by
  rintro x ⟨z, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (M F ζ hζ) y
  change amalgamation F ζ hζ y * amalgamation F ζ hζ (scalarTuple F ζ hζ z) =
    amalgamation F ζ hζ (scalarTuple F ζ hζ z) * amalgamation F ζ hζ y
  rw [← map_mul, ← map_mul]
  congr 1
  apply RestrictedProduct.ext
  intro v
  exact Subgroup.mem_center_iff.mp
    (KPScalarSplitCentral.scalarHom_range_le_center F ζ hζ v
      (MonoidHom.mem_range.mpr ⟨Units.map (adeleEval F v) z, rfl⟩)) (y v)

def splitScalarSubgroup : Subgroup (CubicGL2Adelic F ζ hζ) := (scalarHom F ζ hζ).range

instance splitScalarSubgroup_normal : (splitScalarSubgroup F ζ hζ).Normal :=
  Subgroup.normal_of_le_center (scalarHom_central F ζ hζ)

abbrev CubicPGL2Adelic := CubicGL2Adelic F ζ hζ ⧸ splitScalarSubgroup F ζ hζ

def scalarQuotient : CubicGL2Adelic F ζ hζ →* CubicPGL2Adelic F ζ hζ :=
  QuotientGroup.mk' (splitScalarSubgroup F ζ hζ)

def scalarSubgroup : Subgroup (AdelicGL2 F) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 2) : Ideles F →* AdelicGL2 F).range

theorem scalarSubgroup_central : scalarSubgroup F ≤ Subgroup.center (AdelicGL2 F) := by
  rintro x ⟨z, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  exact (Matrix.GeneralLinearGroup.scalar_commute z y).symm

instance scalarSubgroup_normal : (scalarSubgroup F).Normal :=
  Subgroup.normal_of_le_center (scalarSubgroup_central F)

abbrev AdelicPGL2 := AdelicGL2 F ⧸ scalarSubgroup F

theorem splitScalar_le_ker : splitScalarSubgroup F ζ hζ ≤
    ((QuotientGroup.mk' (scalarSubgroup F)).comp (projection F ζ hζ)).ker := by
  rintro x ⟨z, rfl⟩
  change QuotientGroup.mk' (scalarSubgroup F) (projection F ζ hζ (scalarHom F ζ hζ z)) = 1
  rw [projection_scalarHom]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩

def pglProjection : CubicPGL2Adelic F ζ hζ →* AdelicPGL2 F :=
  QuotientGroup.lift (splitScalarSubgroup F ζ hζ)
    ((QuotientGroup.mk' (scalarSubgroup F)).comp (projection F ζ hζ))
    (splitScalar_le_ker F ζ hζ)

def pglCentralInjection : rootsOfUnity 3 F →* CubicPGL2Adelic F ζ hζ :=
  (scalarQuotient F ζ hζ).comp (centralInjection F ζ hζ)

private theorem projection_centralInjection (ε : rootsOfUnity 3 F) :
    projection F ζ hζ (centralInjection F ζ hζ ε) = 1 := by
  exact show centralInjection F ζ hζ ε ∈ (projection F ζ hζ).ker from
    (range_centralInjection_eq_ker F ζ hζ) ▸ (MonoidHom.mem_range.mpr ⟨ε, rfl⟩)

private theorem scalarMatrix_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Ideles F →* AdelicGL2 F) := by
  intro z z' h
  apply Units.ext
  have hh := congrArg (fun g : AdelicGL2 F => g 0 0) h
  simpa [Matrix.scalar] using hh

theorem pglCentralInjection_injective : Function.Injective (pglCentralInjection F ζ hζ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro ε hε
  have hm : centralInjection F ζ hζ ε ∈ splitScalarSubgroup F ζ hζ :=
    (QuotientGroup.eq_one_iff _).mp hε
  obtain ⟨z, hz⟩ := hm
  have hp := congrArg (projection F ζ hζ) hz
  rw [projection_scalarHom, projection_centralInjection] at hp
  have hz1 : z = 1 := scalarMatrix_injective F (hp.trans (map_one _).symm)
  subst z
  have hc : centralInjection F ζ hζ ε = centralInjection F ζ hζ 1 := by
    simpa using hz.symm
  exact centralInjection_injective F ζ hζ hc

theorem pglProjection_surjective : Function.Surjective (pglProjection F ζ hζ) := by
  unfold pglProjection
  apply QuotientGroup.lift_surjective_of_surjective
  exact (QuotientGroup.mk'_surjective (scalarSubgroup F)).comp (projection_surjective F ζ hζ)

theorem pglCentralInjection_kernel :
    (pglCentralInjection F ζ hζ).range = (pglProjection F ζ hζ).ker := by
  apply le_antisymm
  · rintro x ⟨ε, rfl⟩
    change QuotientGroup.mk' (scalarSubgroup F) (projection F ζ hζ (centralInjection F ζ hζ ε)) = 1
    rw [projection_centralInjection, map_one]
  · intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ) x
    have hy : projection F ζ hζ y ∈ scalarSubgroup F :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨z, hz⟩ := hy
    have hk : y * (scalarHom F ζ hζ z)⁻¹ ∈ (projection F ζ hζ).ker := by
      change projection F ζ hζ (y * (scalarHom F ζ hζ z)⁻¹) = 1
      rw [map_mul, map_inv, projection_scalarHom, hz, mul_inv_cancel]
    rw [← range_centralInjection_eq_ker F ζ hζ] at hk
    obtain ⟨ε, hε⟩ := hk
    refine ⟨ε, ?_⟩
    change scalarQuotient F ζ hζ (centralInjection F ζ hζ ε) = scalarQuotient F ζ hζ y
    rw [hε, map_mul, map_inv]
    have hs : scalarQuotient F ζ hζ (scalarHom F ζ hζ z) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
    rw [hs, inv_one, mul_one]

theorem pglCentralInjection_central :
    (pglCentralInjection F ζ hζ).range ≤ Subgroup.center (CubicPGL2Adelic F ζ hζ) := by
  rw [pglCentralInjection, MonoidHom.range_comp]
  exact le_trans (Subgroup.map_mono (centralInjection_central F ζ hζ))
    (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _))

theorem adelic_pgl_topological_cover :
    T2Space (CubicPGL2Adelic F ζ hζ) ∧ LocallyCompactSpace (CubicPGL2Adelic F ζ hζ) ∧
      IsTopologicalGroup (CubicPGL2Adelic F ζ hζ) ∧
      IsLocalHomeomorph (pglProjection F ζ hζ) := by
 obtain ⟨ht, hl, hg, hp⟩ := adelic_topological_cover F ζ hζ
 letI := ht
 letI := hl
 letI := hg
 letI : IsClosed (splitScalarSubgroup F ζ hζ : Set (CubicGL2Adelic F ζ hζ)) := (scalarHom_continuous_closed F ζ hζ).2
 refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
 have hq := QuotientGroup.isOpenQuotientMap_mk (N := splitScalarSubgroup F ζ hζ)
 have hc : Continuous (pglProjection F ζ hζ) := by
   rw [← hq.continuous_comp_iff]
   exact QuotientGroup.continuous_mk.comp hp.continuous
 have ho : IsOpenMap (pglProjection F ζ hζ) := by
   intro U hU
   have hr : pglProjection F ζ hζ '' U =
       QuotientGroup.mk '' (projection F ζ hζ '' (QuotientGroup.mk ⁻¹' U)) := by
     ext x
     constructor
     · rintro ⟨y, hy, rfl⟩
       obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
       exact ⟨projection F ζ hζ z, ⟨z, hy, rfl⟩, rfl⟩
     · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
       exact ⟨QuotientGroup.mk z, hz, rfl⟩
   rw [hr]
   exact QuotientGroup.isOpenMap_coe _ (hp.isOpenMap _ (hU.preimage QuotientGroup.continuous_mk))
 have hk : IsDiscrete ((pglProjection F ζ hζ).ker : Set (CubicPGL2Adelic F ζ hζ)) := by
   rw [← pglCentralInjection_kernel F ζ hζ]
   exact (Set.finite_range (pglCentralInjection F ζ hζ)).isDiscrete
 exact ((ho.isQuotientMap hc (pglProjection_surjective F ζ hζ)).isQuotientCoveringMap_of_isDiscrete_ker_monoidHom hk).isLocalHomeomorph

end
end DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
