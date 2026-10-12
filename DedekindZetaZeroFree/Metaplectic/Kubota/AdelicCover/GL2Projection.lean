module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.RestrictedCentralTuples

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

abbrev Adeles := NumberField.AdeleRing (𝓞 F) F
abbrev AdelicGL2 := Matrix.GeneralLinearGroup (Fin 2) (Adeles F)

def adeleEval (v : KPHilbert.Place F) : Adeles F →+* KPHilbert.Completion F v :=
  match v with
  | Sum.inl w => (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
  | Sum.inr q => (RestrictedProduct.evalRingHom (fun q : HeightOneSpectrum (𝓞 F) => q.adicCompletion F) q).comp (RingHom.snd _ _)

def matrixEval (v : KPHilbert.Place F) : AdelicGL2 F →* KPLocalCover.LocalGL2 F v :=
  Matrix.GeneralLinearGroup.map (adeleEval F v)

private theorem localIntegers_eq (q : HeightOneSpectrum (𝓞 F)) :
    KPLocalCube.LocalIntegers F q = (q.adicCompletionIntegers F).toSubring := by
  letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
  letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  ext a
  rw [Valuation.mem_integer_iff]
  rw [← Valuation.vle_one_iff]
  exact Valuation.vle_one_iff (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))

private theorem compact_entry (q : HeightOneSpectrum (𝓞 F))
    (x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (hx : x ∈ finiteCompact F ζ hζ q) (i j : Fin 2) :
    x.g i j ∈ q.adicCompletionIntegers F := by
  unfold finiteCompact at hx
  split_ifs at hx with hb
  · obtain ⟨g, hg⟩ := hx
    rw [← hg]
    obtain ⟨k, hk, he⟩ := g.property
    have he' : g.val = KPLocalCube.integerInclusion F q k := he.symm
    change g.val.val i j ∈ q.adicCompletionIntegers F
    rw [he']
    change (k.val i j).val ∈ (q.adicCompletionIntegers F).toSubring
    rw [← localIntegers_eq F q]
    exact (k.val i j).property
  · obtain ⟨g, hg⟩ := hx
    rw [← hg]
    change (g.val i j).val ∈ (q.adicCompletionIntegers F).toSubring
    rw [← localIntegers_eq F q]
    exact (g.val i j).property

theorem matrixEntry_integral (x : RestrictedCover F ζ hζ) (i j : Fin 2) :
    ∀ᶠ q in Filter.cofinite,
      (x (Sum.inr q)).g i j ∈ q.adicCompletionIntegers F := by
  have hx := Sum.inr_injective.tendsto_cofinite.eventually x.property
  filter_upwards [hx] with q hq
  exact compact_entry F ζ hζ q _ hq i j

def matrixEntry (x : RestrictedCover F ζ hζ) (i j : Fin 2) : Adeles F :=
  (fun w => (x (Sum.inl w)).g i j,
    RestrictedProduct.mk (fun q => (x (Sum.inr q)).g i j)
      (matrixEntry_integral F ζ hζ x i j))

def matrixValue (x : RestrictedCover F ζ hζ) : Matrix (Fin 2) (Fin 2) (Adeles F) :=
  fun i j => matrixEntry F ζ hζ x i j

private theorem adele_ext {a b : Adeles F}
    (h : ∀ v, adeleEval F v a = adeleEval F v b) : a = b := by
  apply Prod.ext
  · funext w
    exact h (Sum.inl w)
  · apply RestrictedProduct.ext
    intro q
    exact h (Sum.inr q)

private theorem matrixValue_eval (x : RestrictedCover F ζ hζ)
    (v : KPHilbert.Place F) (i j : Fin 2) :
    adeleEval F v (matrixValue F ζ hζ x i j) = (x v).g i j := by
  cases v <;> rfl

private theorem matrix_ext {a b : Matrix (Fin 2) (Fin 2) (Adeles F)}
    (h : ∀ v, a.map (adeleEval F v) = b.map (adeleEval F v)) : a = b := by
  ext i j
  apply adele_ext F
  intro v
  exact congrFun (congrFun (h v) i) j

private theorem matrixValue_map (x : RestrictedCover F ζ hζ)
    (v : KPHilbert.Place F) :
    (matrixValue F ζ hζ x).map (adeleEval F v) = (x v).g.val := by
  ext i j
  exact matrixValue_eval F ζ hζ x v i j

theorem matrixValue_inv (x : RestrictedCover F ζ hζ) :
    matrixValue F ζ hζ x * matrixValue F ζ hζ x⁻¹ = 1 := by
  apply matrix_ext F
  intro v
  rw [Matrix.map_mul, matrixValue_map, matrixValue_map]
  simpa using (x v).g.val_inv

theorem matrixValue_inv_left (x : RestrictedCover F ζ hζ) :
    matrixValue F ζ hζ x⁻¹ * matrixValue F ζ hζ x = 1 := by
  simpa using matrixValue_inv F ζ hζ x⁻¹

theorem matrixValue_one : matrixValue F ζ hζ 1 = 1 := by
  apply matrix_ext F
  intro v
  rw [matrixValue_map]
  simp

theorem matrixValue_mul (x y : RestrictedCover F ζ hζ) :
    matrixValue F ζ hζ (x * y) = matrixValue F ζ hζ x * matrixValue F ζ hζ y := by
  apply matrix_ext F
  intro v
  rw [Matrix.map_mul, matrixValue_map, matrixValue_map, matrixValue_map]
  rfl

def restrictedProjection : RestrictedCover F ζ hζ →* AdelicGL2 F where
  toFun x := ⟨matrixValue F ζ hζ x, matrixValue F ζ hζ x⁻¹,
    matrixValue_inv F ζ hζ x, matrixValue_inv_left F ζ hζ x⟩
  map_one' := Units.ext (matrixValue_one F ζ hζ)
  map_mul' x y := Units.ext (matrixValue_mul F ζ hζ x y)

theorem restrictedProjection_eval (x : RestrictedCover F ζ hζ) (v : KPHilbert.Place F) :
    matrixEval F v (restrictedProjection F ζ hζ x) =
      KPLocalCover.projection F ζ hζ v (x v) := by
  apply Units.ext
  exact matrixValue_map F ζ hζ x v

private theorem integral_matrix_lift (q : HeightOneSpectrum (𝓞 F))
    (g : KPLocalCover.LocalGL2 F (Sum.inr q))
    (hg : ∀ i j, g i j ∈ KPLocalCube.LocalIntegers F q)
    (hgi : ∀ i j, g.inv i j ∈ KPLocalCube.LocalIntegers F q) :
    ∃ k : KPTameCompact.K0 F q, KPTameCompact.inclusion F q k = g := by
  let a : Matrix (Fin 2) (Fin 2) (KPLocalCube.LocalIntegers F q) := fun i j => ⟨g i j, hg i j⟩
  let b : Matrix (Fin 2) (Fin 2) (KPLocalCube.LocalIntegers F q) := fun i j => ⟨g.inv i j, hgi i j⟩
  have ha : a.map (KPLocalCube.LocalIntegers F q).subtype = g.val := rfl
  have hb : b.map (KPLocalCube.LocalIntegers F q).subtype = g.inv := rfl
  have hinj : Function.Injective (fun c : Matrix (Fin 2) (Fin 2) (KPLocalCube.LocalIntegers F q) =>
      c.map (KPLocalCube.LocalIntegers F q).subtype) := by
    intro c d h
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    exact congrFun (congrFun h i) j
  have hab : a * b = 1 := by
    apply hinj
    dsimp only
    rw [Matrix.map_mul, ha, hb]
    simpa using g.val_inv
  have hba : b * a = 1 := by
    apply hinj
    dsimp only
    rw [Matrix.map_mul, hb, ha]
    simpa using g.inv_val
  exact ⟨⟨a, b, hab, hba⟩, Units.ext rfl⟩

private theorem adelic_integral (g : AdelicGL2 F) :
    ∀ᶠ q in Filter.cofinite, ∃ k : KPTameCompact.K0 F q,
      KPTameCompact.inclusion F q k = matrixEval F (Sum.inr q) g := by
  have hval : ∀ i j, ∀ᶠ q in Filter.cofinite,
      (g.val i j).2 q ∈ q.adicCompletionIntegers F := fun i j => (g.val i j).2.property
  have hinv : ∀ i j, ∀ᶠ q in Filter.cofinite,
      (g.inv i j).2 q ∈ q.adicCompletionIntegers F := fun i j => (g.inv i j).2.property
  have hval' := (Filter.eventually_all).mpr (fun i => Filter.eventually_all.mpr (hval i))
  have hinv' := (Filter.eventually_all).mpr (fun i => Filter.eventually_all.mpr (hinv i))
  filter_upwards [hval', hinv'] with q hq hqi
  apply integral_matrix_lift F q (matrixEval F (Sum.inr q) g)
  · intro i j
    rw [localIntegers_eq F q]
    exact hq i j
  · intro i j
    rw [localIntegers_eq F q]
    exact hqi i j

theorem restrictedProjection_surjective : Function.Surjective (restrictedProjection F ζ hζ) := by
  intro g
  have hc : ∀ᶠ v in Filter.cofinite, ∃ x : KPLocalCover.CubicGL2Raw F ζ hζ v,
      x ∈ compact F ζ hζ v ∧ KPLocalCover.projection F ζ hζ v x = matrixEval F v g := by
    have hf : ∀ᶠ q in Filter.cofinite, ∃ x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q),
        x ∈ compact F ζ hζ (Sum.inr q) ∧
          KPLocalCover.projection F ζ hζ (Sum.inr q) x = matrixEval F (Sum.inr q) g := by
      filter_upwards [adelic_integral F g, (bad_finite F).compl_mem_cofinite] with q hq hb
      change ¬ Bad F q at hb
      obtain ⟨k, hk⟩ := hq
      refine ⟨KPGoodCompactSplitting.kStar F ζ hζ q (fun h3 => hb (Or.inr h3)) k, ?_, hk⟩
      change _ ∈ finiteCompact F ζ hζ q
      rw [finiteCompact, dif_neg hb]
      exact ⟨k, rfl⟩
    rw [Filter.eventually_cofinite] at hf ⊢
    apply Set.Finite.subset (hf.image Sum.inr)
    intro v hv
    cases v with
    | inl w => exact False.elim (hv ⟨KPLocalCover.sectionMap F ζ hζ _ _, Subgroup.mem_top _, rfl⟩)
    | inr q => exact ⟨q, hv, rfl⟩
  let x : ∀ v, KPLocalCover.CubicGL2Raw F ζ hζ v := fun v =>
    if h : ∃ x : KPLocalCover.CubicGL2Raw F ζ hζ v,
        x ∈ compact F ζ hζ v ∧ KPLocalCover.projection F ζ hζ v x = matrixEval F v g
    then h.choose else KPLocalCover.sectionMap F ζ hζ v (matrixEval F v g)
  have hx : ∀ v, KPLocalCover.projection F ζ hζ v (x v) = matrixEval F v g := by
    intro v
    unfold x
    split_ifs with h
    · exact h.choose_spec.2
    · rfl
  let xr : RestrictedCover F ζ hζ := RestrictedProduct.mk x (by
    filter_upwards [hc] with v hv
    unfold x
    rw [dif_pos hv]
    exact hv.choose_spec.1)
  refine ⟨xr, ?_⟩
  apply Units.ext
  apply matrix_ext F
  intro v
  exact congrArg Units.val ((restrictedProjection_eval F ζ hζ xr v).trans (hx v))

private theorem projection_ext {a b : AdelicGL2 F}
    (h : ∀ v, matrixEval F v a = matrixEval F v b) : a = b := by
  apply Units.ext
  apply matrix_ext F
  intro v
  exact congrArg Units.val (h v)

private theorem kernel_local (x : (restrictedProjection F ζ hζ).ker)
    (v : KPHilbert.Place F) : (x.val v).g = 1 := by
  have h := congrArg (matrixEval F v) x.property
  rw [restrictedProjection_eval, map_one] at h
  exact h

private theorem kernel_eventually_one (x : (restrictedProjection F ζ hζ).ker) :
    ∀ᶠ v in Filter.cofinite, x.val v = 1 := by
  have hi : (Set.range (Sum.inl : InfinitePlace F → KPHilbert.Place F)).Finite :=
    Set.finite_range _
  filter_upwards [x.val.property, hi.compl_mem_cofinite] with v hv hfin
  have hlocal : x.val v ∈ (KPLocalCover.projection F ζ hζ v).ker := kernel_local F ζ hζ x v
  have hinr : v ∈ Set.range Sum.inr := by
    cases v with
    | inl w => exact False.elim (hfin ⟨w, rfl⟩)
    | inr q => exact ⟨q, rfl⟩
  have hbot : x.val v ∈ (⊥ : Subgroup _) := by
    rw [← compact_inf_kernel F ζ hζ v hinr]
    exact ⟨hv, hlocal⟩
  exact hbot

theorem restrictedProjection_kernel :
    (restrictedProjection F ζ hζ).ker = (centralTupleMap F ζ hζ).range := by
  apply le_antisymm
  · intro x hx
    let ε : CentralTuples F := RestrictedProduct.mk (fun v => (x v).epsilon) (by
      filter_upwards [kernel_eventually_one F ζ hζ ⟨x, hx⟩] with v hv
      change (x v).epsilon = 1
      rw [hv]
      rfl)
    refine ⟨ε, ?_⟩
    apply RestrictedProduct.ext
    intro v
    have hg : (x v).g = 1 := kernel_local F ζ hζ ⟨x, hx⟩ v
    change KPLocalCover.CubicGL2Raw.mk 1 (x v).epsilon = x v
    cases he : x v with
    | mk g e =>
      rw [he] at hg
      change g = 1 at hg
      simp_all
  · rintro x ⟨ε, rfl⟩
    change restrictedProjection F ζ hζ (centralTupleMap F ζ hζ ε) = 1
    apply projection_ext F
    intro v
    rw [restrictedProjection_eval, map_one]
    rfl

private theorem local_projection_continuous (v : KPHilbert.Place F) :
    Continuous (KPLocalCover.projection F ζ hζ v) := by
  cases v with
  | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.2.1.continuous
  | inr q => exact (KPLocalChartTopology.finite_projection F ζ hζ q _
      (depth_admissible F ζ hζ q)).1.continuous

 instance localCubicGL2Raw_isTopologicalGroup_GL2Projection (v : KPHilbert.Place F) :
    IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  cases v with
  | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
  | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _
      (depth_admissible F ζ hζ q)).2.2

private theorem entry_continuous (i j : Fin 2) : Continuous (matrixEntry F ζ hζ · i j) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w)))).comp ((local_projection_continuous F ζ hζ (Sum.inl w)).comp
        (RestrictedProduct.continuous_eval _))))
  · let φ := fun q : HeightOneSpectrum (𝓞 F) =>
      fun x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) => x.g i j
    have hm : ∀ᶠ q in Filter.cofinite, Set.MapsTo (φ q)
        (compact F ζ hζ (Sum.inr q)) (q.adicCompletionIntegers F) :=
      Filter.Eventually.of_forall (fun q x hx => compact_entry F ζ hζ q x hx i j)
    exact RestrictedProduct.mapAlong_continuous _ _ Sum.inr
      Sum.inr_injective.tendsto_cofinite φ hm (fun q =>
        (continuous_apply j).comp ((continuous_apply i).comp
          ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inr q)))).comp (local_projection_continuous F ζ hζ (Sum.inr q)))))

theorem restrictedProjection_continuous : Continuous (restrictedProjection F ζ hζ) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_pi (fun i => continuous_pi (fun j => entry_continuous F ζ hζ i j))
  · exact (continuous_pi (fun i => continuous_pi (fun j =>
      entry_continuous F ζ hζ i j))).comp continuous_inv

theorem restricted_kernel_discrete :
    DiscreteTopology (restrictedProjection F ζ hζ).ker ∧
      IsClosed ((restrictedProjection F ζ hζ).ker : Set (RestrictedCover F ζ hζ)) := by
  letI : Fact (∀ v : KPHilbert.Place F,
      IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) :=
    ⟨compact_open F ζ hζ⟩
  letI : IsTopologicalGroup (RestrictedCover F ζ hζ) :=
    RestrictedProduct.isTopologicalGroup
      (R := fun v => KPLocalCover.CubicGL2Raw F ζ hζ v) (B := compact F ζ hζ)
  letI : T2Space (Adeles F) := by
    change T2Space ((∀ w : InfinitePlace F, w.Completion) ×
      RestrictedProduct (fun q : HeightOneSpectrum (𝓞 F) => q.adicCompletion F)
        (fun q => (q.adicCompletionIntegers F : Set _)) Filter.cofinite)
    infer_instance
  letI : T2Space (AdelicGL2 F) := inferInstance
  constructor
  · apply discreteTopology_of_isOpen_singleton_one
    let U : Set (restrictedProjection F ζ hζ).ker :=
      {x | ∀ v, x.val v ∈ compact F ζ hζ v}
    have hu : IsOpen U :=
      (RestrictedProduct.isOpen_forall_mem (compact_open F ζ hζ)).preimage continuous_subtype_val
    let ev := fun w : InfinitePlace F =>
      fun x : (restrictedProjection F ζ hζ).ker =>
        (⟨x.val (Sum.inl w), kernel_local F ζ hζ x (Sum.inl w)⟩ :
          (KPLocalCover.projection F ζ hζ (Sum.inl w)).ker)
    have hev : ∀ w, Continuous (ev w) := fun w =>
      ((RestrictedProduct.continuous_eval (Sum.inl w)).comp continuous_subtype_val).subtype_mk _
    have ho : ∀ w, IsOpen {x : (restrictedProjection F ζ hζ).ker | ev w x = 1} := by
      intro w
      letI : DiscreteTopology (KPLocalCover.projection F ζ hζ (Sum.inl w)).ker :=
        (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.2.2.1
      exact (isOpen_discrete ({1} : Set (KPLocalCover.projection F ζ hζ (Sum.inl w)).ker)).preimage (hev w)
    have hV : IsOpen (⋂ w, {x : (restrictedProjection F ζ hζ).ker | ev w x = 1}) :=
      isOpen_iInter_of_finite ho
    convert hu.inter hV using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      subst x
      exact ⟨fun v => (compact F ζ hζ v).one_mem, fun w => rfl⟩
    · rintro ⟨hx, hw⟩
      apply Subtype.ext
      apply RestrictedProduct.ext
      intro v
      cases v with
      | inl w => exact congrArg Subtype.val (hw w)
      | inr q =>
        have hbot : x.val (Sum.inr q) ∈ (⊥ : Subgroup _) := by
          rw [← compact_inf_kernel F ζ hζ (Sum.inr q) ⟨q, rfl⟩]
          exact ⟨hx _, kernel_local F ζ hζ x _⟩
        exact hbot
  · exact isClosed_singleton.preimage (restrictedProjection_continuous F ζ hζ)

end
end DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
