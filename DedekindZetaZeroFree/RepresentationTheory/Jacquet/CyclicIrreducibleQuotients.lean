module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.SubmodulesAndQuotients
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.LocalCoinvariantExactness

@[expose] public section

namespace DedekindZetaZeroFree.KPCyclicQuotient

def cyclicSubmodule {G U : Type*} [Group G] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U) (u : U) : Submodule ℂ U :=
  Submodule.span ℂ (Set.range fun g : G => ρ g u)

theorem cyclicSubmodule_stable {G U : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U) (u : U) :
    ∀ g : G, cyclicSubmodule ρ u ≤ (cyclicSubmodule ρ u).comap (ρ g) := by
  intro g
  refine Submodule.span_le.mpr ?_
  rintro x ⟨h, rfl⟩
  change ρ g (ρ h u) ∈ cyclicSubmodule ρ u
  rw [← Module.End.mul_apply, ← map_mul]
  exact Submodule.subset_span ⟨g * h, rfl⟩

def cyclicRepresentation {G U : Type*} [Group G] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U) (u : U) :
    Representation ℂ G (cyclicSubmodule ρ u) :=
  ρ.subrepresentation (cyclicSubmodule ρ u) (cyclicSubmodule_stable ρ u)

def quotientMap {G U : Type*} [Group G] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U) (M : Submodule ℂ U)
    (hM : ∀ g : G, M ≤ M.comap (ρ g)) :
    Representation.IntertwiningMap ρ (ρ.quotient M hM) where
  toLinearMap := M.mkQ
  isIntertwining' _ := rfl

theorem exists_maximal_cyclic_quotient {G U : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (u : U) (hu : u ≠ 0) :
    ∃ M : Submodule ℂ (cyclicSubmodule ρ u),
      ∃ hM : ∀ g : G, M ≤ M.comap (cyclicRepresentation ρ u g),
        M ≠ ⊤ ∧
        (∀ (L : Submodule ℂ (cyclicSubmodule ρ u)),
          (∀ g : G, L ≤ L.comap (cyclicRepresentation ρ u g)) →
          M ≤ L → L ≠ ⊤ → L = M) ∧
        Nontrivial ((cyclicSubmodule ρ u) ⧸ M) ∧
        Representation.IsIrreducible ((cyclicRepresentation ρ u).quotient M hM) ∧
        Function.Surjective (quotientMap (cyclicRepresentation ρ u) M hM) := by
  classical
  let C := cyclicSubmodule ρ u
  let τ := cyclicRepresentation ρ u
  have huC : u ∈ C := by
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  let v : C := ⟨u, huC⟩
  have generates : ∀ L : Submodule ℂ C,
      (∀ g : G, L ≤ L.comap (τ g)) → v ∈ L → L = ⊤ := by
    intro L hL hv
    apply top_unique
    intro x _
    have hx : (x : U) ∈ L.map C.subtype := by
      have hspan : C ≤ L.map C.subtype := by
        apply Submodule.span_le.mpr
        rintro _ ⟨g, rfl⟩
        exact ⟨τ g v, hL g hv, rfl⟩
      exact hspan x.property
    obtain ⟨y, hy, he⟩ := hx
    have : y = x := Subtype.ext he
    simpa [this] using hy
  let P : Set (Submodule ℂ C) :=
    {L | (∀ g : G, L ≤ L.comap (τ g)) ∧ v ∉ L}
  obtain ⟨M, hMmax⟩ := zorn_le₀ P (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun L hL => le_sSup hL⟩
      · intro g x hx
        obtain ⟨L, hL, hxL⟩ := (Submodule.mem_sSup_of_directed hne hchain.directedOn).mp hx
        exact le_sSup hL ((hc hL).1 g hxL)
      · intro hv
        obtain ⟨L, hL, hvL⟩ := (Submodule.mem_sSup_of_directed hne hchain.directedOn).mp hv
        exact (hc hL).2 hvL
    · refine ⟨⊥, ⟨?_, ?_⟩, ?_⟩
      · intro g x hx
        change x = 0 at hx
        simpa [hx]
      · simpa [v, Submodule.mem_bot, Subtype.ext_iff] using hu
      · intro L hL
        exact False.elim (hne ⟨L, hL⟩))
  have hM : ∀ g : G, M ≤ M.comap (τ g) := hMmax.prop.1
  have hproper : M ≠ ⊤ := by
    intro he
    exact hMmax.prop.2 (he ▸ Submodule.mem_top)
  have hmax : ∀ L : Submodule ℂ C, (∀ g : G, L ≤ L.comap (τ g)) →
      M ≤ L → L ≠ ⊤ → L = M := by
    intro L hL hML hp
    exact le_antisymm (hMmax.2 ⟨hL, fun hv => hp (generates L hL hv)⟩ hML) hML
  have hn : Nontrivial (C ⧸ M) := Submodule.Quotient.nontrivial_iff.mpr hproper
  have hirr : Representation.IsIrreducible (τ.quotient M hM) := by
    letI := hn
    have hnt : Nontrivial (Subrepresentation (τ.quotient M hM)) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro he
      obtain ⟨x, hx⟩ := exists_ne (0 : C ⧸ M)
      have : x ∈ (⊥ : Subrepresentation (τ.quotient M hM)) := he ▸ Submodule.mem_top
      exact hx this
    letI := hnt
    refine ⟨fun L => ?_⟩
    let D := L.toSubmodule.comap M.mkQ
    have hD : ∀ g : G, D ≤ D.comap (τ g) := by
      intro g x hx
      exact L.apply_mem_toSubmodule g hx
    have hMD : M ≤ D := by
      intro x hx
      change M.mkQ x ∈ L.toSubmodule
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero M).mpr hx]
      exact L.toSubmodule.zero_mem
    by_cases hp : D = ⊤
    · right
      apply Subrepresentation.toSubmodule_injective
      apply (Submodule.comap_injective_of_surjective M.mkQ_surjective)
      change D = Submodule.comap M.mkQ ⊤
      simpa using hp
    · left
      have he : D = M := hmax D hD hMD hp
      apply Subrepresentation.toSubmodule_injective
      apply (Submodule.comap_injective_of_surjective M.mkQ_surjective)
      change D = Submodule.comap M.mkQ ⊥
      simpa using he
  exact ⟨M, hM, hproper, hmax, hn, hirr, M.mkQ_surjective⟩

theorem nonzero_representation_has_cyclic_quotient {G U : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] [Nontrivial U] (ρ : Representation ℂ G U) :
    ∃ u : U, u ≠ 0 ∧
      ∃ M : Submodule ℂ (cyclicSubmodule ρ u),
        ∃ hM : ∀ g : G, M ≤ M.comap (cyclicRepresentation ρ u g),
          M ≠ ⊤ ∧ Nontrivial ((cyclicSubmodule ρ u) ⧸ M) ∧
          Representation.IsIrreducible ((cyclicRepresentation ρ u).quotient M hM) ∧
          Function.Surjective (quotientMap (cyclicRepresentation ρ u) M hM) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  obtain ⟨M, hM, hproper, _, hnonzero, hirr, hsurj⟩ :=
    exists_maximal_cyclic_quotient ρ u hu
  exact ⟨u, hu, M, hM, hproper, hnonzero, hirr, hsurj⟩

def inside {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : Submodule ℂ V) : Submodule ℂ A := B.comap A.subtype

theorem inside_stable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A B : Submodule ℂ V)
    (hA : ∀ g : G, A ≤ A.comap (ρ g))
    (hB : ∀ g : G, B ≤ B.comap (ρ g)) :
    ∀ g : G, inside A B ≤ (inside A B).comap (ρ.subrepresentation A hA g) := by
  intro g x hx
  exact hB g hx

def subquotientRepresentation {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (A B : Submodule ℂ V) (hA : ∀ g : G, A ≤ A.comap (ρ g))
    (hB : ∀ g : G, B ≤ B.comap (ρ g)) : Representation ℂ G (A ⧸ inside A B) :=
  (ρ.subrepresentation A hA).quotient (inside A B) (inside_stable ρ A B hA hB)

def preimage {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : Submodule ℂ V) (C : Submodule ℂ (A ⧸ inside A B)) : Submodule ℂ A :=
  C.comap (inside A B).mkQ

theorem preimage_stable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A B : Submodule ℂ V)
    (hA : ∀ g : G, A ≤ A.comap (ρ g)) (hB : ∀ g : G, B ≤ B.comap (ρ g))
    (C : Submodule ℂ (A ⧸ inside A B))
    (hC : ∀ g : G, C ≤ C.comap (subquotientRepresentation ρ A B hA hB g)) :
    ∀ g : G, preimage A B C ≤ (preimage A B C).comap (ρ.subrepresentation A hA g) := by
  intro g x hx
  exact hC g hx

def preimageRepresentation {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (A B : Submodule ℂ V) (hA : ∀ g : G, A ≤ A.comap (ρ g))
    (hB : ∀ g : G, B ≤ B.comap (ρ g))
    (C : Submodule ℂ (A ⧸ inside A B))
    (hC : ∀ g : G, C ≤ C.comap (subquotientRepresentation ρ A B hA hB g)) :
    Representation ℂ G (preimage A B C) :=
  (ρ.subrepresentation A hA).subrepresentation (preimage A B C)
    (preimage_stable ρ A B hA hB C hC)

def preimageMap {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (A B : Submodule ℂ V) (hA : ∀ g : G, A ≤ A.comap (ρ g))
    (hB : ∀ g : G, B ≤ B.comap (ρ g))
    (C : Submodule ℂ (A ⧸ inside A B))
    (hC : ∀ g : G, C ≤ C.comap (subquotientRepresentation ρ A B hA hB g)) :
    Representation.IntertwiningMap (preimageRepresentation ρ A B hA hB C hC)
      ((subquotientRepresentation ρ A B hA hB).subrepresentation C hC) where
  toLinearMap :=
    { toFun := fun d => ⟨(inside A B).mkQ d.val, d.property⟩
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  isIntertwining' _ := rfl

abbrev ordinaryJacquet {K G U : Type*} [Field K] [Group G]
    [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (n : Multiplicative K →* G) := Representation.Coinvariants (ρ.comp n)

open scoped Topology
private theorem orbit_locallyConstant {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {v : V} (hv : SmoothVector ρ v) :
    IsLocallyConstant (fun g : G => ρ g v) := by
  obtain ⟨J, hJ⟩ := hv
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  refine ⟨{h : G | g⁻¹ * h ∈ J}, J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using J.one_mem
  · intro h hh
    have he := hJ (g⁻¹ * h) hh
    have := congrArg (ρ g) he
    simpa [← Module.End.mul_apply, ← map_mul] using this
private theorem fixed_surjective {G V W : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : SmoothRepresentation ρ) (q : Representation.IntertwiningMap ρ σ)
    (hq : Function.Surjective q) (J : CompactOpenLevel G)
    (w : fixedSubmodule σ J.toOpenSubgroup.toSubgroup) :
    ∃ v : fixedSubmodule ρ J.toOpenSubgroup.toSubgroup, q v = w := by
  classical
  obtain ⟨v, hv⟩ := hq w
  letI : CompactSpace J.toOpenSubgroup := isCompact_iff_compactSpace.mp J.isCompact
  have hfin : (Set.range fun g : J.toOpenSubgroup => ρ (g : G) v).Finite :=
    ((orbit_locallyConstant ρ (hρ v)).comp_continuous continuous_subtype_val).range_finite
  let S := hfin.toFinset
  have hS : ∀ x, x ∈ S ↔ ∃ g : J.toOpenSubgroup, ρ (g : G) v = x := by
    intro x
    exact hfin.mem_toFinset
  have ha : ∀ (g : J.toOpenSubgroup) x, x ∈ S → ρ (g : G) x ∈ S := by
    intro g x hx
    obtain ⟨h, rfl⟩ := (hS x).mp hx
    apply (hS _).mpr
    exact ⟨g * h, by simp [← Module.End.mul_apply, ← map_mul]⟩
  have hi : ∀ g : G, Function.Injective (ρ g) := by
    intro g x y he
    have := congrArg (ρ g⁻¹) he
    simpa [← Module.End.mul_apply, ← map_mul] using this
  have hs : ∀ g : J.toOpenSubgroup, ρ (g : G) (∑ x ∈ S, x) = ∑ x ∈ S, x := by
    intro g
    rw [map_sum]
    apply Finset.sum_bij (fun x _ => ρ (g : G) x)
    · exact ha g
    · intro x hx y hy he
      exact hi g he
    · intro y hy
      refine ⟨ρ ((g⁻¹ : J.toOpenSubgroup) : G) y, ha g⁻¹ y hy, ?_⟩
      simp [← Module.End.mul_apply, ← map_mul]
    · intros; rfl
  have hne : S.Nonempty := ⟨v, (hS v).mpr ⟨1, by simp⟩⟩
  have hc : (S.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_ne_zero
  refine ⟨⟨(S.card : ℂ)⁻¹ • ∑ x ∈ S, x, ?_⟩, ?_⟩
  · intro g
    simp [hs g]
  · change q ((S.card : ℂ)⁻¹ • ∑ x ∈ S, x) = w.val
    have hqx : ∀ x ∈ S, q x = w.val := by
      intro x hx
      obtain ⟨g, rfl⟩ := (hS x).mp hx
      rw [q.isIntertwining, hv]
      exact w.property g
    simp only [map_smul, map_sum, Finset.sum_congr rfl hqx, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
private theorem admissible_sub {G V : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (ha : Admissible ρ)
    (A : Submodule ℂ V) (hA : ∀ g, A ≤ A.comap (ρ g)) :
    Admissible (ρ.subrepresentation A hA) := by
  intro J
  let f : fixedSubmodule (ρ.subrepresentation A hA) J.toOpenSubgroup.toSubgroup →ₗ[ℂ]
      fixedSubmodule ρ J.toOpenSubgroup.toSubgroup :=
    (A.subtype.comp (fixedSubmodule (ρ.subrepresentation A hA) J.toOpenSubgroup.toSubgroup).subtype).codRestrict _
      (fun x => fun g => congrArg Subtype.val (x.property g))
  letI := ha J
  apply Module.Finite.of_injective f
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : fixedSubmodule ρ J.toOpenSubgroup.toSubgroup => z.val) he
private theorem admissible_quot {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hs : SmoothRepresentation ρ) (ha : Admissible ρ)
    (M : Submodule ℂ V) (hM : ∀ g, M ≤ M.comap (ρ g)) :
    Admissible (ρ.quotient M hM) := by
  intro J
  let q := quotientMap ρ M hM
  let f : fixedSubmodule ρ J.toOpenSubgroup.toSubgroup →ₗ[ℂ]
      fixedSubmodule (ρ.quotient M hM) J.toOpenSubgroup.toSubgroup :=
    (q.toLinearMap.comp (fixedSubmodule ρ J.toOpenSubgroup.toSubgroup).subtype).codRestrict _
      (fun x => fun g => by
        change (ρ.quotient M hM) g (q x.val) = q x.val
        rw [← q.isIntertwining]
        exact congrArg q (x.property g))
  letI := ha J
  apply Module.Finite.of_surjective f
  intro w
  obtain ⟨v, hv⟩ := fixed_surjective ρ _ hs q M.mkQ_surjective J w
  exact ⟨v, Subtype.ext hv⟩
private theorem root_smooth {K G V : Type*} [Field K] [TopologicalSpace K]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hs : SmoothRepresentation ρ)
    (n : Multiplicative K →* G) (hn : Continuous n) : KPCoinvariants.IsSmooth (ρ.comp n) := by
  intro v
  exact ((orbit_locallyConstant ρ (hs v)).isOpen_fiber v).preimage (hn.comp continuous_ofAdd)

private theorem twisted_one {K V : Type*} [Field K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative K) V) :
    KPCoinvariants.twistedRepresentation ρ 1 = ρ := by
  ext g v
  simp [KPCoinvariants.twistedRepresentation]
private theorem jacquet_sub_zero {K G V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (n : Multiplicative K →* G) (hn : Continuous n)
    (ρ : Representation ℂ G V) (hs : SmoothRepresentation ρ)
    (A : Submodule ℂ V) (hA : ∀ g, A ≤ A.comap (ρ g))
    (hz : Subsingleton (ordinaryJacquet ρ n)) :
    Subsingleton (ordinaryJacquet (ρ.subrepresentation A hA) n) := by
  let τ := ρ.subrepresentation A hA
  let σ := ρ.quotient A hA
  let i : Representation.IntertwiningMap (τ.comp n) (ρ.comp n) :=
    { toLinearMap := A.subtype, isIntertwining' _ := rfl }
  let p : Representation.IntertwiningMap (ρ.comp n) (σ.comp n) :=
    { toLinearMap := A.mkQ, isIntertwining' _ := rfl }
  have he : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap := by
    change A.subtype.range = A.mkQ.ker
    simp
  have hst := root_smooth τ (smoothRepresentation_subrepresentation ρ hs A hA) n hn
  have hsr := root_smooth ρ hs n hn
  have hss := root_smooth σ (smoothRepresentation_quotient ρ hs A hA) n hn
  have hi := (KPCoinvariants.exact (τ.comp n) (ρ.comp n) (σ.comp n)
    hst hsr hss 1 (by fun_prop) (IsLocallyConstant.of_constant _ (by intros; rfl))
    i p Subtype.val_injective A.mkQ_surjective he).1
  have hz' : Subsingleton (KPCoinvariants.Coinvariants (ρ.comp n) 1) := by
    simpa only [KPCoinvariants.Coinvariants, twisted_one] using hz
  have hz'' : Subsingleton (KPCoinvariants.Coinvariants (τ.comp n) 1) := by
    letI := hz'
    exact Function.Injective.subsingleton hi
  simpa only [KPCoinvariants.Coinvariants, twisted_one] using hz''
private theorem jacquet_quot_zero {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module ℂ V] (n : Multiplicative K →* G)
    (ρ : Representation ℂ G V) (A : Submodule ℂ V) (hA : ∀ g, A ≤ A.comap (ρ g))
    (hz : Subsingleton (ordinaryJacquet ρ n)) :
    Subsingleton (ordinaryJacquet (ρ.quotient A hA) n) := by
  let q : Representation.IntertwiningMap (ρ.comp n) ((ρ.quotient A hA).comp n) :=
    { toLinearMap := A.mkQ, isIntertwining' _ := rfl }
  let f := Representation.Coinvariants.map _ _ q
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective ((ρ.quotient A hA).comp n) x
    obtain ⟨z, rfl⟩ := A.mkQ_surjective y
    exact ⟨Representation.Coinvariants.mk (ρ.comp n) z, Representation.Coinvariants.map_mk q z⟩
  letI := hz
  exact hf.subsingleton

theorem jacquet_zero_subquotient_cyclic_quotient
    {K G V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (n : Multiplicative K →* G) (hn : Continuous n)
    (ρ : Representation ℂ G V) (hsmooth : SmoothRepresentation ρ)
    (hadmissible : Admissible ρ) (A B : Submodule ℂ V)
    (hA : ∀ g : G, A ≤ A.comap (ρ g)) (hB : ∀ g : G, B ≤ B.comap (ρ g))
    (hBA : B ≤ A) (hne : B ≠ A)
    (hJacquet : Subsingleton (ordinaryJacquet (subquotientRepresentation ρ A B hA hB) n)) :
    let Q := subquotientRepresentation ρ A B hA hB
    ∃ u : A ⧸ inside A B, u ≠ 0 ∧
      ∃ M : Submodule ℂ (cyclicSubmodule Q u),
        ∃ hM : ∀ g : G, M ≤ M.comap (cyclicRepresentation Q u g),
          let C := cyclicSubmodule Q u
          let σ := (cyclicRepresentation Q u).quotient M hM
          SmoothRepresentation Q ∧ Admissible Q ∧
          SmoothRepresentation (cyclicRepresentation Q u) ∧
          Admissible (cyclicRepresentation Q u) ∧
          Subsingleton (ordinaryJacquet (cyclicRepresentation Q u) n) ∧
          Nontrivial (C ⧸ M) ∧ Representation.IsIrreducible σ ∧
          SmoothRepresentation σ ∧ Admissible σ ∧
          Subsingleton (ordinaryJacquet σ n) ∧
          Function.Surjective (quotientMap (cyclicRepresentation Q u) M hM) ∧
          SmoothRepresentation (preimageRepresentation ρ A B hA hB C
            (cyclicSubmodule_stable Q u)) ∧
          Function.Surjective (preimageMap ρ A B hA hB C (cyclicSubmodule_stable Q u)) ∧
          Function.Surjective ((quotientMap (cyclicRepresentation Q u) M hM).comp
            (preimageMap ρ A B hA hB C (cyclicSubmodule_stable Q u))) := by
  classical
  dsimp only
  let Q := subquotientRepresentation ρ A B hA hB
  have hQA : SmoothRepresentation (ρ.subrepresentation A hA) :=
    smoothRepresentation_subrepresentation ρ hsmooth A hA
  have hQs : SmoothRepresentation Q :=
    smoothRepresentation_quotient _ hQA (inside A B) (inside_stable ρ A B hA hB)
  have hQa : Admissible Q :=
    admissible_quot _ hQA (admissible_sub ρ hadmissible A hA)
      (inside A B) (inside_stable ρ A B hA hB)
  have hproper : inside A B ≠ ⊤ := by
    intro he
    apply hne
    apply le_antisymm hBA
    intro x hx
    have hm : (⟨x, hx⟩ : A) ∈ inside A B := he ▸ Submodule.mem_top
    exact hm
  letI : Nontrivial (A ⧸ inside A B) := Submodule.Quotient.nontrivial_iff.mpr hproper
  obtain ⟨u, hu, M, hM, _, hnon, hirr, hsurj⟩ := nonzero_representation_has_cyclic_quotient Q
  let C := cyclicSubmodule Q u
  let τ := cyclicRepresentation Q u
  have hCs : SmoothRepresentation τ :=
    smoothRepresentation_subrepresentation Q hQs C (cyclicSubmodule_stable Q u)
  have hCa : Admissible τ := admissible_sub Q hQa C (cyclicSubmodule_stable Q u)
  have hCj : Subsingleton (ordinaryJacquet τ n) :=
    jacquet_sub_zero n hn Q hQs C (cyclicSubmodule_stable Q u) hJacquet
  have hSs : SmoothRepresentation (τ.quotient M hM) :=
    smoothRepresentation_quotient τ hCs M hM
  have hSa : Admissible (τ.quotient M hM) := admissible_quot τ hCs hCa M hM
  have hSj : Subsingleton (ordinaryJacquet (τ.quotient M hM) n) :=
    jacquet_quot_zero n τ M hM hCj
  have hDs : SmoothRepresentation (preimageRepresentation ρ A B hA hB C
      (cyclicSubmodule_stable Q u)) :=
    smoothRepresentation_subrepresentation _ hQA _
      (preimage_stable ρ A B hA hB C (cyclicSubmodule_stable Q u))
  have hps : Function.Surjective (preimageMap ρ A B hA hB C (cyclicSubmodule_stable Q u)) := by
    intro c
    obtain ⟨a, ha⟩ := (inside A B).mkQ_surjective c.val
    refine ⟨⟨a, ?_⟩, ?_⟩
    · change (inside A B).mkQ a ∈ C
      rw [ha]
      exact c.property
    · exact Subtype.ext ha
  exact ⟨u, hu, M, hM, hQs, hQa, hCs, hCa, hCj, hnon, hirr,
    hSs, hSa, hSj, hsurj, hDs, hps, hsurj.comp hps⟩

end DedekindZetaZeroFree.KPCyclicQuotient
