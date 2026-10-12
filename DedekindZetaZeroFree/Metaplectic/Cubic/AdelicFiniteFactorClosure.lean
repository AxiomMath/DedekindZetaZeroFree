module

public import DedekindZetaZeroFree.Adeles.Quotients.ArchimedeanFiniteProduct

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualFiniteFactor
open NumberField IsDedekindDomain KPAdelicCoverRestrictedProduct
open scoped NumberField Classical Topology
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Cover := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ
abbrev ArchGroup := InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ

instance coverTopologicalGroup : IsTopologicalGroup (Cover F ζ hζ) :=
  (adelic_pgl_topological_cover F ζ hζ).2.2.1

def localInsertion (v : KPHilbert.Place F) :
    KPPGLLocalCover.CubicPGL2 F ζ hζ v →* Cover F ζ hζ :=
  (local_pgl_injection F ζ hζ v).choose

def finiteSubgroup : Subgroup (Cover F ζ hζ) :=
  (⨆ q : HeightOneSpectrum (𝓞 F), (localInsertion F ζ hζ (Sum.inr q)).range).topologicalClosure

abbrev tupleFactor := PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ
abbrev finiteTuples := PGLComplex.AdelicSlicesRaw.finiteTuples F ζ hζ
abbrev archProjection := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
abbrev archInsertion := PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ

 theorem localInsertion_coverQuotient (v : KPHilbert.Place F)
    (x : KPLocalCover.CubicGL2Raw F ζ hζ v) :
    localInsertion F ζ hζ v (KPPGLLocalCover.coverQuotient F ζ hζ v x) =
      scalarQuotient F ζ hζ (localInjection F ζ hζ v x) :=
  (local_pgl_injection F ζ hζ v).choose_spec.2.2 x

 theorem localInsertion_range (v : KPHilbert.Place F) :
    (localInsertion F ζ hζ v).range =
      ((scalarQuotient F ζ hζ).comp (localInjection F ζ hζ v)).range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (KPPGLLocalCover.splitScalarSubgroup F ζ hζ v) x
    exact ⟨y, (localInsertion_coverQuotient F ζ hζ v y).symm⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨KPPGLLocalCover.coverQuotient F ζ hζ v y, localInsertion_coverQuotient F ζ hζ v y⟩

 def truncation (x : RestrictedCover F ζ hζ) (s : Finset (KPHilbert.Place F)) :
    RestrictedCover F ζ hζ :=
  ⟨fun i => if i ∈ s then x i else 1, by
    filter_upwards [s.finite_toSet.compl_mem_cofinite] with i hi
    simp_all⟩

private theorem truncation_tendsto (x : RestrictedCover F ζ hζ) :
    Filter.Tendsto (truncation F ζ hζ x) Filter.atTop (𝓝 x) := by
  let R := fun v : KPHilbert.Place F => KPLocalCover.CubicGL2Raw F ζ hζ v
  let B := compact F ζ hζ
  let S : Set (KPHilbert.Place F) := {i | x i ∈ B i}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.mpr x.property
  let xp : RestrictedProduct R (fun i => (B i : Set (R i))) (Filter.principal S) :=
    ⟨x, Filter.eventually_principal.mpr fun _ hi => hi⟩
  let tp (s : Finset (KPHilbert.Place F)) :
      RestrictedProduct R (fun i => (B i : Set (R i))) (Filter.principal S) :=
    ⟨fun i => if i ∈ s then x i else 1, by
      apply Filter.eventually_principal.mpr
      intro i hi
      dsimp
      split_ifs <;> simp_all [S]⟩
  have ht : Filter.Tendsto tp Filter.atTop (𝓝 xp) := by
    apply RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply Filter.tendsto_congr' (show (fun s : Finset (KPHilbert.Place F) => tp s i) =ᶠ[Filter.atTop]
        (fun _ => x i) from ?_) |>.mpr tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop {i}] with s hs
    simp [tp, hs (Finset.mem_singleton_self i)]
  have heq : RestrictedProduct.inclusion R (fun i => (B i : Set (R i))) hS ∘ tp =
      truncation F ζ hζ x := rfl
  have hx : RestrictedProduct.inclusion R (fun i => (B i : Set (R i))) hS xp = x := by ext; rfl
  change Filter.Tendsto (truncation F ζ hζ x) Filter.atTop (𝓝 x)
  have hfinal := (RestrictedProduct.continuous_inclusion hS).tendsto xp |>.comp ht
  change Filter.Tendsto (RestrictedProduct.inclusion R (fun i => (B i : Set (R i))) hS ∘ tp) Filter.atTop
    (𝓝 (RestrictedProduct.inclusion R (fun i => (B i : Set (R i))) hS xp)) at hfinal
  rw [heq, hx] at hfinal
  exact hfinal

 theorem finiteSubgroup_le_tupleFactor : finiteSubgroup F ζ hζ ≤ tupleFactor F ζ hζ := by
  obtain ⟨_, _, _, _, hk, _, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  letI : IsClosed (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ) :
      Set (Matrix.GeneralLinearGroup (Fin 2) ℂ)) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (M := Matrix.GeneralLinearGroup (Fin 2) ℂ) Set.univ)
  letI : T2Space (Matrix.ProjGenLinGroup (Fin 2) ℂ) := inferInstanceAs
    (T2Space (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _))
  letI : T2Space (PGLComplex.AdelicSlicesRaw.ArchGroup F) :=
    inferInstanceAs (T2Space (InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ))
  have hclosed : IsClosed (tupleFactor F ζ hζ : Set (Cover F ζ hζ)) := by
    change IsClosed (PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ : Set (Cover F ζ hζ))
    rw [← hk]
    exact isClosed_eq (RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).2 continuous_const
  apply Subgroup.topologicalClosure_minimal _ _ hclosed
  apply iSup_le
  intro q
  rw [localInsertion_range]
  rintro _ ⟨x, rfl⟩
  refine ⟨localToRestricted F ζ hζ (Sum.inr q) x, ?_, rfl⟩
  intro w
  simp [localToRestricted, RestrictedProduct.mulSingleMonoidHom,
    RestrictedProduct.mulSingle_eq_of_ne]

 theorem tupleFactor_le_finiteSubgroup : tupleFactor F ζ hζ ≤ finiteSubgroup F ζ hζ := by
  rintro _ ⟨x, hx, rfl⟩
  let f := (scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)
  have hf : Continuous f :=
    QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk
  apply (Subgroup.isClosed_topologicalClosure _).mem_of_tendsto
    (hf.tendsto x |>.comp (truncation_tendsto F ζ hζ x))
  apply Filter.Eventually.of_forall
  intro s
  apply Subgroup.le_topologicalClosure
  change f (truncation F ζ hζ x s) ∈ _
  induction s using Finset.induction_on with
  | empty =>
    have hz : truncation F ζ hζ x ∅ = 1 := by ext v; simp [truncation]
    rw [hz, map_one]
    exact Subgroup.one_mem _
  | @insert a s ha ih =>
    have hind : truncation F ζ hζ x (insert a s) =
        localToRestricted F ζ hζ a (x a) * truncation F ζ hζ x s := by
      ext v
      change (if v ∈ insert a s then x v else 1) =
        localToRestricted F ζ hζ a (x a) v * (if v ∈ s then x v else 1)
      by_cases hva : v = a
      · subst v; simp [localToRestricted, ha]
      · simp [localToRestricted, hva]
    rw [hind, map_mul]
    apply Subgroup.mul_mem _ _ ih
    cases a with
    | inl w =>
      change f (localToRestricted F ζ hζ (Sum.inl w) (x (Sum.inl w))) ∈ _
      rw [hx w, map_one, map_one]
      exact Subgroup.one_mem _
    | inr q =>
      apply le_iSup (fun q : HeightOneSpectrum (𝓞 F) => (localInsertion F ζ hζ (Sum.inr q)).range) q
      rw [localInsertion_range]
      exact ⟨x (Sum.inr q), rfl⟩

theorem finiteSubgroup_eq_tupleFactor : finiteSubgroup F ζ hζ = tupleFactor F ζ hζ :=
  le_antisymm (finiteSubgroup_le_tupleFactor F ζ hζ) (tupleFactor_le_finiteSubgroup F ζ hζ)

theorem finiteSubgroup_eq_ker : finiteSubgroup F ζ hζ = (archProjection F ζ hζ).ker := by
  rw [finiteSubgroup_eq_tupleFactor]
  exact (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose_spec.2.2.2.1.symm

theorem archInsertion_commutes (a : ArchGroup F) (u : finiteSubgroup F ζ hζ) :
    Commute (archInsertion F ζ hζ a) (u : Cover F ζ hζ) := by
  apply RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a
    ⟨u.val, by
      change u.val ∈ tupleFactor F ζ hζ
      rw [← finiteSubgroup_eq_tupleFactor]; exact u.property⟩

end DedekindZetaZeroFree.ActualFiniteFactor

end
